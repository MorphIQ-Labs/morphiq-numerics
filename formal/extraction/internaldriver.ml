(* Runs the extracted Q128 and Q256 transcriptions, rounding tests and exp's
   reduction (InternalCrosscheck.v) on the internal cross-check corpus and
   compares each result with the Rust library's.

   Each line is "op args : result". A value is "n e k l1 .. lk": its sign
   (0 or 1), its exponent in decimal, its limb count and its 64-bit limbs in
   hex, least significant first; a binary64 is 16 hex digits; a rounding
   test's result is a binary64 or "none"; a reduction's is its six words.
   Exits 1 on a mismatch or a malformed line. *)

open Internalcrosscheck

let rec pos_of_u64 n =
  if n = 1L then XH
  else
    let rest = pos_of_u64 (Int64.shift_right_logical n 1) in
    if Int64.logand n 1L = 1L then XI rest else XO rest

let z_of_u64 n = if n = 0L then Z0 else Zpos (pos_of_u64 n)

let rec pos_of_int n =
  if n = 1 then XH else
  let rest = pos_of_int (n lsr 1) in
  if n land 1 = 1 then XI rest else XO rest

let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))

let rec u64_of_pos = function
  | XH -> 1L
  | XO p -> Int64.shift_left (u64_of_pos p) 1
  | XI p -> Int64.logor (Int64.shift_left (u64_of_pos p) 1) 1L

let u64_of_z = function Z0 -> 0L | Zpos p -> u64_of_pos p | Zneg _ -> failwith "negative limb"

let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1

let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)

let hex s = Int64.of_string ("0x" ^ s)

(* A value from the tokens, and the tokens after it. *)
let value = function
  | n :: e :: k :: rest ->
      let k = int_of_string k in
      let rec take i acc rest =
        if i = 0 then (List.rev acc, rest)
        else match rest with x :: r -> take (i - 1) (z_of_u64 (hex x) :: acc) r | [] -> failwith "short value" in
      let (l, rest) = take k [] rest in
      ((n = "1", z_of_int (int_of_string e), l), rest)
  | _ -> failwith "malformed value"

let show (n, e, l) =
  String.concat " " ((if n then "1" else "0") :: string_of_int (int_of_z e) :: string_of_int (List.length l)
    :: List.map (fun z -> Printf.sprintf "%016Lx" (u64_of_z z)) l)

let show_bits z = Printf.sprintf "%016Lx" (u64_of_z z)

let show_opt = function None -> "none" | Some z -> show_bits z

let compute op args =
  match op with
  | "q128_mul" | "q128_add" | "q256_mul" | "q256_add" ->
      let ((n1, e1, l1), rest) = value args in
      let ((n2, e2, l2), _) = value rest in
      let f = match op with
        | "q128_mul" -> x_q128_mul | "q128_add" -> x_q128_add
        | "q256_mul" -> x_q256_mul | _ -> x_q256_add in
      let ((n, e), l) = f n1 e1 l1 n2 e2 l2 in show (n, e, l)
  | "q128_to_f64" | "q256_to_f64" ->
      let ((n, e, l), _) = value args in
      show_bits ((if op = "q128_to_f64" then x_q128_to_f64 else x_q256_to_f64) n e l)
  | "q128_from_f64" | "q256_from_f64" ->
      let bits = z_of_u64 (hex (List.hd args)) in
      let ((n, e), l) = (if op = "q128_from_f64" then x_q128_from_f64 else x_q256_from_f64) bits in show (n, e, l)
  | "decide_with" ->
      (match args with
       | [hi; lo; eps] -> show_opt (x_decide_with (z_of_u64 (hex hi)) (z_of_u64 (hex lo)) (z_of_u64 (hex eps)))
       | _ -> failwith "decide_with takes three words")
  | "decide_scaled" ->
      (match args with
       | [hi; lo; eps; k] ->
           show_opt (x_decide_scaled (z_of_u64 (hex hi)) (z_of_u64 (hex lo)) (z_of_u64 (hex eps)) (z_of_int (int_of_string k)))
       | _ -> failwith "decide_scaled takes three words and an exponent")
  | "reduce" ->
      (match args with
       | [x] -> String.concat " " (List.map show_bits (x_reduce (z_of_u64 (hex x))))
       | _ -> failwith "reduce takes one word")
  | "q256_from_limbs" ->
      let ((n, e, l), _) = value args in
      let ((n, e), l) = x_q256_from_limbs n e l in show (n, e, l)
  | _ -> failwith ("unknown operation " ^ op)

let () =
  let file = open_in Sys.argv.(1) in
  let lines = ref 0 and failures = ref 0 in
  (try
     while true do
       let line = input_line file in
       incr lines;
       match String.split_on_char ':' line with
       | [lhs; rhs] ->
           let words s = List.filter (( <> ) "") (String.split_on_char ' ' s) in
           (match words lhs with
            | op :: args ->
                let expected = String.concat " " (words rhs) in
                let got = compute op args in
                if got <> expected then begin
                  incr failures;
                  if !failures <= 20 then
                    Printf.eprintf "mismatch: %s: Rust %s, extracted %s\n" (String.trim lhs) expected got
                end
            | [] -> failwith ("malformed line " ^ string_of_int !lines))
       | _ -> failwith ("malformed line " ^ string_of_int !lines)
     done
   with End_of_file -> ());
  Printf.printf "internal crosscheck: %d cases, %d mismatches\n" !lines !failures;
  if !failures > 0 || !lines = 0 then exit 1
