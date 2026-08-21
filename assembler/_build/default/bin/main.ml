open! Base
open! Stdio

type reg = Register of int | Io of string
let labels = ref []
let constants = ref []

(* Returns either Some with the value of the corresponding constant or None if there is no constant to be replaced*)
let constant_match str = 
  let rec const_enum lst = 
    match lst with
    | [] -> None
    | (const, value) :: rest -> 
      if String.is_substring str ~substring:const then
        Some (const, value)
      else const_enum rest in
  const_enum !constants

let label_match str = 
  let rec label_enum lst = 
    match lst with 
    | [] -> None
    | (label, address) :: rest -> 
      if String.is_substring str ~substring:label then 
        Some (label, address)
      else label_enum rest in
  label_enum !labels

(* goes through the list of instructions, adds all constants and labels to global list*)
let rec constant_label_add lst pc =
  match lst with
  | [] -> []
  | first :: rest ->
    let const_dec = Str.regexp {|const[ ]+\([A-Za-z0-9_]+\)[ ]*=[ ]*\([0-9]+\)|} in
    let label_dec = Str.regexp {|\([A-Za-z0-9_]+\):|} in
    if Str.string_match const_dec first 0 then
      let name = Str.matched_group 1 first in
      let value = Str.matched_group 2 first in
      begin constants := (name, value) :: !constants; constant_label_add rest pc end
    else if Str.string_match label_dec first 0 then
      let label = Str.matched_group 1 first in
      begin labels := (label, pc) :: !labels; constant_label_add rest pc end
    else first :: constant_label_add rest (pc + 1)

let rec constant_label_replace = function
  | [] -> []
  | first :: rest -> 
    (match (constant_match first, label_match first) with
      | (Some (const, value), Some (label, address)) ->
        let replaced_const = Str.global_replace (Str.regexp_string const) value first in
        let replaced_label = Str.global_replace (Str.regexp_string label) (Int.to_string address) replaced_const in
        replaced_label :: constant_label_replace rest
      | (Some (const, value), None) -> (Str.global_replace (Str.regexp_string const) value first) :: constant_label_replace rest
      | (None, Some (label, address)) -> (Str.global_replace (Str.regexp_string label) (Int.to_string address) first) :: constant_label_replace rest
      | (None, None) -> first :: constant_label_replace rest)

let assemble_alu x =
  match x with
  | "nand" -> "01000000"
  | "or" -> "01000001"
  | "and" -> "01000010"
  | "nor" -> "01000011"
  | "add" -> "01000100"
  | "sub" -> "01000101"
  | s -> s

let assemble_jump x = 
  match x with
  | "nop" -> "11000000"
  | "jmp" -> "11000001"
  | "jz" -> "11000010"
  | "jnz" -> "11000011"
  | "jl" -> "11000100"
  | "jge" -> "11000101"
  | "jle" -> "11000110"
  | "jg" -> "11000111"
  | s -> s

(* Converts to binary, pads with 5 zeroes, take String.suffix as needed *)
let rec convert_bin n = 
  let rec convert_helper m acc =
    match m with
    | 0 -> "0"
    | 1 -> "1" ^ acc
    | x -> convert_helper (x / 2) ((Int.to_string (x % 2)) ^ acc) in
  "00000" ^ convert_helper n ""

let assemble_move x y = 
  (match x with
  | Io out -> 
    (match y with
    | Io inreg -> "10110110"
    | Register r2 -> "10" ^ "110" ^ String.suffix (convert_bin r2) 3)
  | Register r1 -> 
    let r1_bin = String.suffix (convert_bin r1) 3 in
    (match y with
    | Io inreg -> "10" ^ r1_bin ^ "110"
    | Register r2 -> "10" ^ r1_bin ^ String.suffix (convert_bin r2) 3))

let assemble_imm x = 
  "00" ^ String.suffix (convert_bin x) 6

let rec assemble_h = function
  | [] -> Ok []
  | first :: rest ->
    (match first with
    | s when String.is_prefix s ~prefix:"or"
      || String.is_prefix s ~prefix:"and" 
      || String.is_prefix s ~prefix:"nor"
      || String.is_prefix s ~prefix:"nand" 
      || String.is_prefix s ~prefix:"add" 
      || String.is_prefix s ~prefix:"sub" -> 
        (match assemble_h rest with
        | Ok tail -> Ok (assemble_alu s :: tail)
        | Error e -> Error e)
    | s when String.is_prefix first ~prefix:"mov" ->
      let regex = Str.regexp {|mov[ ]*r\([0-9]\),[ ]*r\([0-9]\)|} in
      let regex2 = Str.regexp {|mov[ ]*out,[ ]*r\([0-9]\)|} in
      let regex3 = Str.regexp {|mov[ ]*r\([0-9]\),[ ]*in|} in
      if Str.string_match regex s 0 then
        let reg1 = Int.of_string (Str.matched_group 1 s) in
        let reg2 = Int.of_string (Str.matched_group 2 s) in
        (match assemble_h rest with
        | Ok tail -> Ok (assemble_move (Register reg1) (Register reg2) :: tail)
        | Error e -> Error e)
      else if Str.string_match regex2 s 0 then
        let sourcereg = Int.of_string (Str.matched_group 1 s) in
        (match assemble_h rest with
          | Ok tail -> Ok (assemble_move (Io "out") (Register sourcereg) :: tail)
          | Error e -> Error e)
      else if Str.string_match regex3 s 0 then
        let destreg = Int.of_string (Str.matched_group 1 s) in
        (match assemble_h rest with
          | Ok tail -> Ok (assemble_move (Register destreg) (Io "in") :: tail)
          | Error e -> Error e)
      else Error "invalid syntax" 
    | s when String.is_prefix first ~prefix:"imm" -> 
      let value = Str.regexp {|imm[ ]+\([0-9]+\)|} in
      if Str.string_match value s 0 then
        let imm_str = Int.of_string (Str.matched_group 1 s) in
        (match assemble_h rest with 
        | Ok tail -> Ok (assemble_imm imm_str :: tail)
        | Error e -> Error e)
      else Error "invalid immediate"
    | s when String.is_prefix first ~prefix:"nop" 
      || String.is_prefix first ~prefix:"jmp"
      || String.is_prefix first ~prefix:"jz"
      || String.is_prefix first ~prefix:"jnz"
      || String.is_prefix first ~prefix:"jl"
      || String.is_prefix first ~prefix:"jge"
      || String.is_prefix first ~prefix:"jle"
      || String.is_prefix first ~prefix:"jg" -> 
      (match assemble_h rest with
        | Ok tail -> Ok (assemble_jump s :: tail)
        | Error e -> Error e)
      | _ -> Error "invalid syntax")

let assemble lst = 
  match assemble_h (constant_label_replace (constant_label_add lst 0)) with
  | Ok assembled -> begin List.iter assembled ~f:Stdio.print_endline; labels := []; constants := [] end
  | Error e -> Stdio.prerr_endline e

(* Tests: *)
let () = print_endline "Test 1:"
let t1 = assemble ["nop"; "jg"; "imm 12"; "add";"mov r1,r1"]
let () = print_endline "Test 2:"
let t2 = assemble ["label1:"; "const c1 = 6"; "imm label1"; "imm c1"; "mov r1, r2"; "imm label1"; "jmp"]

let () = print_endline "Test 3 (assembly programming level)"
let t3 = assemble ["mov r2, in";
"imm 5" ; 
"mov r1, r0";
"add";
"mov out, r3";]
let () = print_endline "Test 4: (conditional jumps level)"
let t4 = assemble ["count:";
"imm 1";
"mov r1, r4";
"mov r2, r0";
"add";
"mov r4, r3";
"imm 37";
"mov r1, in";
"mov r2, r0";
"sub"; 
"imm count";
"jnz";
"mov out, r4";]
let () = print_endline "Test 5: (the maze level)"
let t5 = assemble ["const left_turn = 0";
"const forward = 1";
"const right_turn = 2";
"loop:";
"turn_right:";
"imm right_turn";
"mov out, r0";
"mov r3, in";
"imm move";
"jz";
"turn_back:";
"imm left_turn";
"mov out, r0";
"mov r3, in";
"imm turn_back";
"jnz";
"move:";
"imm forward";
"mov out, r0";
"imm loop";
"jmp";]