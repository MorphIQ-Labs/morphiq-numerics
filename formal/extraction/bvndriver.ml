(* Runs the extracted transcription of the bivariate normal's scalar kernel
   (BvnCrosscheck.v, formal/bivariate/BvnKernel.v) on the bvn lines of the
   internal cross-check corpus and compares each result with the Rust
   library's. Other lines are the internal driver's.

   Each line is "op args calls : result". The calls are the library calls the
   Rust made, "f/argument/result" with f one of e (exp), s (sin), a (asin),
   n (norm_cdf) and two binary64 encodings of 16 hex digits. The extracted
   kernel's library functions look their arguments up in them. A call the
   kernel makes with an argument the Rust never passed, and a call the Rust made
   that the kernel did not, are mismatches; so is a call recorded twice with
   different results. The sign of a zero argument is not distinguished: Rust
   does not fix the sign of max(-0.0, 0.0), and the library's results at -0 and
   +0 are required to be equal, which a recorded pair that is not fails.

     bvn_table rho calls : regime asr (kw p q)*    (or "none")
     bvn_cdf x y rho calls : result

   Exits 1 on a mismatch or a malformed line, or if no line was run. *)

open Bvncrosscheck

let rec pos_of_u64 n =
  if n = 1L then XH
  else
    let rest = pos_of_u64 (Int64.shift_right_logical n 1) in
    if Int64.logand n 1L = 1L then XI rest else XO rest

let z_of_u64 n = if n = 0L then Z0 else Zpos (pos_of_u64 n)

let rec u64_of_pos = function
  | XH -> 1L
  | XO p -> Int64.shift_left (u64_of_pos p) 1
  | XI p -> Int64.logor (Int64.shift_left (u64_of_pos p) 1) 1L

let u64_of_z = function Z0 -> 0L | Zpos p -> u64_of_pos p | Zneg _ -> failwith "negative encoding"

let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1

let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let hex s = Int64.of_string ("0x" ^ s)

let show_bits z = Printf.sprintf "%016Lx" (u64_of_z z)

(* The recorded calls of one function: argument (with -0 as +0) to result. *)
type calls = { table : (int64, int64) Hashtbl.t; used : (int64, unit) Hashtbl.t }

let key a = if a = Int64.min_int then 0L else a

let problems = ref []

let problem line msg = problems := (line, msg) :: !problems

let build line tokens =
  let mk () = { table = Hashtbl.create 64; used = Hashtbl.create 64 } in
  let e = mk () and s = mk () and a = mk () and n = mk () in
  List.iter (fun tok ->
      match String.split_on_char '/' tok with
      | [f; arg; res] ->
          let c = match f with
            | "e" -> e | "s" -> s | "a" -> a | "n" -> n
            | _ -> failwith ("unknown library function " ^ f) in
          let k = key (hex arg) and r = hex res in
          (match Hashtbl.find_opt c.table k with
           | Some r' when r' <> r -> problem line ("call " ^ tok ^ " recorded with two results")
           | _ -> Hashtbl.replace c.table k r)
      | _ -> failwith ("malformed call " ^ tok)) tokens;
  (e, s, a, n)

(* The library function of a recorded table, as a function on encodings. *)
let lookup line name c z =
  let k = key (u64_of_z z) in
  match Hashtbl.find_opt c.table k with
  | Some r -> Hashtbl.replace c.used k (); z_of_u64 r
  | None ->
      problem line (Printf.sprintf "the kernel called %s(%016Lx), which the Rust never did" name (u64_of_z z));
      z

let unused line name c =
  Hashtbl.iter (fun k _ ->
      if not (Hashtbl.mem c.used k) then
        problem line (Printf.sprintf "the Rust called %s(%016Lx), which the kernel never did" name k)) c.table

let regimes = Array.make 5 0
let none_tables = ref 0

let run line op args tokens expected =
  let (e, s, a, n) = build line tokens in
  let fe = lookup line "exp" e and fs = lookup line "sin" s
  and fa = lookup line "asin" a and fn = lookup line "norm_cdf" n in
  let got =
    match op, args with
    | "bvn_table", [rho] ->
        (match x_bvn_table fe fs fa fn (z_of_u64 (hex rho)) with
         | None -> incr none_tables; "none"
         | Some ((regime, range), nodes) ->
             let r = int_of_z regime in
             regimes.(r) <- regimes.(r) + 1;
             String.concat " " (string_of_int r :: show_bits range
               :: List.concat_map (fun ((kw, p), q) -> [show_bits kw; show_bits p; show_bits q]) nodes))
    | "bvn_cdf", [x; y; rho] ->
        show_bits (x_bvn_cdf fe fs fa fn (z_of_u64 (hex x)) (z_of_u64 (hex y)) (z_of_u64 (hex rho)))
    | _ -> failwith ("malformed bvn line " ^ line) in
  unused line "exp" e; unused line "sin" s; unused line "asin" a; unused line "norm_cdf" n;
  got = expected, got

let () =
  let file = open_in Sys.argv.(1) in
  let lines = ref 0 and failures = ref 0 and tables = ref 0 and values = ref 0 in
  let words s = List.filter (( <> ) "") (String.split_on_char ' ' s) in
  (try
     while true do
       let line = input_line file in
       if String.length line >= 4 && String.sub line 0 4 = "bvn_" then begin
         incr lines;
         match String.split_on_char ':' line with
         | [lhs; rhs] ->
             (match words lhs with
              | op :: args ->
                  let is_call w = String.contains w '/' in
                  let args' = List.filter (fun w -> not (is_call w)) args in
                  let tokens = List.filter is_call args in
                  let expected = String.concat " " (words rhs) in
                  problems := [];
                  let (ok, got) = run line op args' tokens expected in
                  if op = "bvn_table" then incr tables else incr values;
                  if (not ok) || !problems <> [] then begin
                    incr failures;
                    if !failures <= 20 then begin
                      let head = if String.length lhs > 120 then String.sub lhs 0 120 ^ "..." else lhs in
                      Printf.eprintf "mismatch: %s: Rust %s, extracted %s\n" head
                        (let r = String.concat " " (words rhs) in if String.length r > 120 then String.sub r 0 120 ^ "..." else r)
                        (if String.length got > 120 then String.sub got 0 120 ^ "..." else got);
                      List.iter (fun (_, m) -> Printf.eprintf "  %s\n" m) (List.rev !problems)
                    end
                  end
              | [] -> failwith ("malformed line " ^ string_of_int !lines))
         | _ -> failwith ("malformed line " ^ string_of_int !lines)
       end
     done
   with End_of_file -> ());
  Printf.printf "bvn crosscheck: %d tables (independent %d, comonotone %d, countermonotone %d, low %d, high %d, invalid %d), %d values, %d mismatches\n"
    !tables regimes.(0) regimes.(1) regimes.(2) regimes.(3) regimes.(4) !none_tables !values !failures;
  if !failures > 0 || !lines = 0 then exit 1
