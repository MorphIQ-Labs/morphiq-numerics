(* Runs the extracted IEEE 754 definitions (Crosscheck.v) on the cross-check
   corpus and compares each result with the Rust library's, bit for bit.

   Each corpus line is "op in... : out...", every value a binary64 as 16 hex
   digits: two outputs for the double-word operations and transforms, one for
   sqrt, four for exp_split (a presence flag, the value's words and the exponent
   offset by 4096), and one for each slice reduction, whose inputs are the slice
   (for dot and dot2, x followed by y). Results must match exactly, except that
   outside the reductions any NaN matches any NaN: IEEE 754 leaves a NaN's
   payload to the implementation. The reductions define their NaN bits, so
   theirs must match too. Exits 1 on a
   mismatch or a malformed line. *)

open Crosscheck

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

let u64_of_z = function
  | Z0 -> 0L
  | Zpos p -> u64_of_pos p
  | Zneg _ -> failwith "negative bits"

let is_nan b =
  Int64.logand b 0x7ff0_0000_0000_0000L = 0x7ff0_0000_0000_0000L
  && Int64.logand b 0x000f_ffff_ffff_ffffL <> 0L

let same a b = a = b || (is_nan a && is_nan b)

(* The first and second halves of a dot product's inputs. *)
let halves l =
  let n = List.length l in
  if n mod 2 <> 0 then failwith "a dot product takes two slices of one length";
  (List.filteri (fun i _ -> i < n / 2) l, List.filteri (fun i _ -> i >= n / 2) l)

let reductions = ["sum"; "sum2"; "dot"; "dot2"; "sum_squares"; "sum_squares2"; "max_abs"]

let reduce op z =
  match op with
  | "sum" -> x_sum z
  | "sum2" -> x_sum2 z
  | "dot" -> let (x, y) = halves z in x_dot x y
  | "dot2" -> let (x, y) = halves z in x_dot2 x y
  | "sum_squares" -> x_sum_squares z
  | "sum_squares2" -> x_sum_squares2 z
  | _ -> x_max_abs z

let compute op ins =
  let z = List.map z_of_u64 ins in
  let pair (h, l) = [u64_of_z h; u64_of_z l] in
  match op, z with
  | _ when List.mem op reductions -> [u64_of_z (reduce op z)]
  | "two_sum", [a; b] -> pair (x_two_sum a b)
  | "fast_two_sum", [a; b] -> pair (x_fast_two_sum a b)
  | "two_prod", [a; b] -> pair (x_two_prod a b)
  | "add_f64", [a; b; c] -> pair (x_add_f64 a b c)
  | "add", [a; b; c; d] -> pair (x_add a b c d)
  | "sub", [a; b; c; d] -> pair (x_sub a b c d)
  | "mul_f64", [a; b; c] -> pair (x_mul_f64 a b c)
  | "mul", [a; b; c; d] -> pair (x_mul a b c d)
  | "div_f64", [a; b; c] -> pair (x_div_f64 a b c)
  | "div", [a; b; c; d] -> pair (x_div a b c d)
  | "sqrt", [a] -> [u64_of_z (x_sqrt a)]
  | "exp_split", [a; b] ->
      let (((f, h), l), k) = x_exp_split a b in
      List.map u64_of_z [f; h; l; k]
  | _ -> failwith ("unknown operation " ^ op)

let hex s = Int64.of_string ("0x" ^ s)

let () =
  let file = open_in Sys.argv.(1) in
  let lines = ref 0 and failures = ref 0 in
  (try
     while true do
       let line = input_line file in
       incr lines;
       match String.split_on_char ':' line with
       | [lhs; rhs] -> (
           let words s = List.filter (( <> ) "") (String.split_on_char ' ' s) in
           match words lhs, List.map hex (words rhs) with
           | op :: ins, (_ :: _ as rust) ->
               let extracted = compute op (List.map hex ins) in
               let show vs = String.concat " " (List.map (Printf.sprintf "%016Lx") vs) in
               if List.length extracted <> List.length rust
                  || not (List.for_all2 (if List.mem op reductions then Int64.equal else same)
                            extracted rust) then begin
                 incr failures;
                 if !failures <= 20 then
                   Printf.eprintf "mismatch: %s: Rust %s, extracted %s\n"
                     (String.trim lhs) (show rust) (show extracted)
               end
           | _ -> failwith ("malformed line " ^ string_of_int !lines))
       | _ -> failwith ("malformed line " ^ string_of_int !lines)
     done
   with End_of_file -> ());
  Printf.printf "crosscheck: %d cases, %d mismatches\n" !lines !failures;
  if !failures > 0 || !lines = 0 then exit 1
