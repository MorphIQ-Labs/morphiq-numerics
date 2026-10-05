(* Runs the extracted IEEE 754 definitions (Crosscheck.v) on the cross-check
   corpus and compares each result with the Rust library's, bit for bit.

   Each corpus line is "op in... : out out", every value a binary64 as 16 hex
   digits. Results must match exactly, except that any NaN matches any NaN:
   IEEE 754 leaves a NaN's payload to the implementation. Exits 1 on a
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

let compute op ins =
  let z = List.map z_of_u64 ins in
  let (h, l) =
    match op, z with
    | "two_sum", [a; b] -> x_two_sum a b
    | "fast_two_sum", [a; b] -> x_fast_two_sum a b
    | "two_prod", [a; b] -> x_two_prod a b
    | "add_f64", [a; b; c] -> x_add_f64 a b c
    | "add", [a; b; c; d] -> x_add a b c d
    | "sub", [a; b; c; d] -> x_sub a b c d
    | "mul_f64", [a; b; c] -> x_mul_f64 a b c
    | "mul", [a; b; c; d] -> x_mul a b c d
    | "div_f64", [a; b; c] -> x_div_f64 a b c
    | "div", [a; b; c; d] -> x_div a b c d
    | _ -> failwith ("unknown operation " ^ op)
  in
  (u64_of_z h, u64_of_z l)

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
           | op :: ins, [rh; rl] ->
               let (ch, cl) = compute op (List.map hex ins) in
               if not (same ch rh && same cl rl) then begin
                 incr failures;
                 if !failures <= 20 then
                   Printf.eprintf "mismatch: %s: Rust %016Lx %016Lx, extracted %016Lx %016Lx\n"
                     (String.trim lhs) rh rl ch cl
               end
           | _ -> failwith ("malformed line " ^ string_of_int !lines))
       | _ -> failwith ("malformed line " ^ string_of_int !lines)
     done
   with End_of_file -> ());
  Printf.printf "crosscheck: %d cases, %d mismatches\n" !lines !failures;
  if !failures > 0 || !lines = 0 then exit 1
