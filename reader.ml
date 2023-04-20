(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
(*module Reader = struct*) (*Comment the line above and uncomment this line in order to run seperate nt_parsers *)
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let get_Some s val_if_none = 
    match s with
    | Some(s) -> s
    | None -> val_if_none
;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;


let int_of_hex_char hchar = if (int_of_char hchar > 64)  && (int_of_char hchar < 71) then (int_of_char hchar - 55) (* Big letter *)
  else if (int_of_char hchar > 96) && (int_of_char hchar < 103) then (int_of_char hchar - 87) (* Small letter *)
  else (int_of_char hchar - 48) ;;



let char_list_to_string list = List.fold_right (fun x y -> (String.make 1 x) ^ y) list "" ;;

let append_strings list = List.fold_right (fun x y -> x ^ y) list "" ;;
  
let nt_hexString_to_ascii list_char =
  List.fold_left (fun x y -> x*16 + (int_of_hex_char y)) 0 list_char;;


let rec int_to_frac num = 
  if num < Float.one then num else int_to_frac (num /. 10.0)
;;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_line_comment str =
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str


and nt_paired_comment str = 

  let nt1 = word "{" in
  let nts = disj_list[ unitify nt_char; unitify nt_string; nt_comment; ] in
  let nts' = disj nts (unitify (one_of "{}")) in
  let nt3 = unitify (diff nt_any nts') in
  let nt3 = disj nt3 nts in
  let nt3 = star nt3 in
  let nt4 = word "}" in
  let nt5 = caten nt1 (caten nt3 nt4) in
  let nt5 = unitify nt5 in
  nt5 str

and nt_sexpr_comment str =
  let nt1 = word "#;" in
  let nt2 = nt_sexpr in
  let nt2 = caten nt1 nt2 in
  let nt2 = unitify nt2 in
  nt2 str

and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str

and nt_skip_star str =
  
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str

and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
  
and nt_int str = 
  let nt1 = char '+' in
  let nt2 = char '-' in
  let nt1 = caten (maybe nt1) (plus (range '0' '9')) in
  let nt2 = caten nt2 (plus (range '0' '9')) in
  let nt1 = pack nt1 (fun (_, e) -> List.fold_left (fun x y -> x*10 + (int_of_char y - 48)) 0 e)  in
  let nt2 = pack nt2 (fun (_, e) -> List.fold_left (fun x y -> x*10 - (int_of_char y - 48)) 0 e)  in
  let nt1 = disj_list[nt1; nt2] in
  nt1 str

and nt_frac str = 
  let nt1 = char '/' in
  let int_no_zero = diff nt_integer_part (word "0") in
  let nt1 = caten nt_int (caten nt1 int_no_zero) in
  let nt1 = pack nt1 (fun (e, (_, t)) -> ScmRational((e/(gcd t e)), (t/(gcd t e)))) in
  nt1 str

and nt_integer_part str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun (e) -> List.fold_left (fun x y -> x*10 + (int_of_char y - 48)) 0 e)  in
  nt1 str

and nt_mantissa str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun (e) -> "." ^ (String.of_seq (List.to_seq e))) in
  let nt1 = pack nt1 (fun (e) -> (Float.of_string e)) in
  nt1 str

and nt_exponent str =
  let nt1 = word "e" in
  let nt2 = word "E" in
  let nt3 = word "*10^" in
  let nt4 = word "*10**" in
  let nt1 = disj_list[nt1; nt2; nt3; nt4] in
  let nt1 = caten nt1 nt_int in
  let nt1 = pack nt1 (fun (_,e) -> e) in
  nt1 str

and nt_float str = 
  let nt_plus = char '+' in
  let nt_minus = char '-' in
  let dot = char '.' in 
  let nt1_plus = caten (maybe nt_plus) (caten nt_integer_part (caten dot (caten (maybe nt_mantissa) (maybe nt_exponent)))) in
  let nt1_minus = caten nt_minus (caten nt_integer_part (caten dot (caten (maybe nt_mantissa) (maybe nt_exponent)))) in
  let nt2_plus = caten (maybe nt_plus) (caten dot (caten nt_mantissa (maybe nt_exponent))) in
  let nt2_minus = caten nt_minus (caten dot (caten nt_mantissa (maybe nt_exponent))) in
  let nt3_plus = caten (maybe nt_plus) (caten nt_integer_part nt_exponent) in
  let nt3_minus = caten nt_minus (caten nt_integer_part nt_exponent) in
  let nt1_plus = pack nt1_plus (fun (_, (i, (_, (m, e)))) -> ScmReal(((float_of_int i) +. (get_Some m 0.0)) *. (10.0 ** (float_of_int (get_Some e 0))))) in
  let nt1_minus = pack nt1_minus (fun (_, (i, (_, (m, e)))) -> ScmReal(((float_of_int i) +. (get_Some m 0.0)) *. (10.0 ** (float_of_int (get_Some e 0))) *. -1.0)) in
  let nt2_plus = pack nt2_plus (fun (_,(_, (m,e))) -> ScmReal(m *. (10.0 ** (float_of_int (get_Some e 0))))) in
  let nt2_minus = pack nt2_minus (fun (_,(_, (m,e))) -> ScmReal(m *. (10.0 ** (float_of_int (get_Some e 0))) *. -1.0)) in
  let nt3_plus = pack nt3_plus (fun (_,(i,e)) -> ScmReal(float_of_int i *. (10.0 ** (float_of_int e)))) in
  let nt3_minus = pack nt3_minus (fun (_,(i,e)) -> ScmReal(float_of_int i *. (10.0 ** (float_of_int e)) *. -1.0)) in
  let nt1 = disj_list[nt1_plus; nt1_minus; nt2_plus; nt2_minus; nt3_plus; nt3_minus] in
  nt1 str

and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> ScmBoolean(false)) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> ScmBoolean(true)) in
  let nt1 = disj nt1 nt2 in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_char_simple str =   
  let nt_VisableSimple = range '!' '~' in
  let nt_VisableSimple = pack (caten (word "#\\") nt_VisableSimple) (fun (_,e) -> ScmChar(e)) in
  let nt_VisableSimple = not_followed_by nt_VisableSimple nt_symbol_char in
  nt_VisableSimple str

and make_named_char char_name ch =  pack (caten (word "#\\") (word_ci char_name)) (fun _ -> ScmChar(ch))

and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t');
               (make_named_char "~~" '~');
               make_named_char "nul" (char_of_int 0)] in
  nt1 str

and nt_char_hex str = 
  let nt1 = range '0' '9' in
  let nt2 = range 'a' 'f' in
  let nt3 = range 'A' 'F' in
  let nt1 = disj_list [nt1; nt2; nt3] in
  nt1 str

and nt_char str = 
  let nt1 = pack (caten (word "#\\") (caten (word_ci "x") (plus nt_char_hex))) (fun (_,(_,e)) -> nt_hexString_to_ascii e) in (** #\\x0*)
  let nt1 = only_if nt1 (fun e -> e < 128) in
  let nt1 = pack nt1 (fun e -> ScmChar(char_of_int e)) in
  let nt1 = disj_list [nt1; nt_char_named; nt_char_simple] in
  nt1 str

and nt_symbol_char str = 
  let numbers = range '0' '9' in
  let alphabet = range 'a' 'z' in
  let caps = range 'A' 'Z' in
  let sign = "!$^*-_=+<>?/:" in
  let sign = one_of sign in
  let nt1 = disj_list [numbers; alphabet; caps; sign] in
  nt1 str

and nt_symbol str =
(*Turns Symbol into lowercase if any letters are uppercase *)
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol (String.lowercase_ascii name)) in 
  let nt1 = diff nt1 nt_number in
  nt1 str

and nt_string_interpolated str = (* Check if ~{} is legal *)
  let nt1 = char '~' in 
  let nt2 = char '{' in
  let nt_skip_1 = nt_skip_star in
  let nts = nt_sexpr in
  let nt_skip_2 = nt_skip_star in
  let nt4 = char '}' in
  let nt5 = caten nt1 (caten nt2 (caten nt_skip_1 (caten nts (caten nt_skip_2 nt4 )))) in     (* ~{     sexpr    } *)
  let nt6 = pack nt5 (fun (_, (_, (_, (e, (_, _))))) -> 
                      ScmPair( ScmSymbol("format"),  
                        ScmPair( ScmString("~a"), 
                          ScmPair(e, ScmNil)))) in

  
  nt6 str
and nt_string_meta str = 
  let nt1 = 
    disj_list [pack (word "\\\\") (fun _ -> String.make 1 '\\');
               pack (word "\\n") (fun _ -> String.make 1 '\n');
               pack (word "\\r") (fun _ -> String.make 1 '\r');
               pack (word "\\f") (fun _ -> String.make 1 '\012');
               pack (word "\\t") (fun _ -> String.make 1 '\t');
               pack (word "~~") (fun _ -> String.make 1 '~')] in
  nt1 str

and nt_string_hex str =
(* all comments here are examples 126, 127, 139*)
  let nt1 = word_ci "\\x" in
  let nt2 = plus nt_char_hex in
  let nt3 = caten nt1 nt2 in
  let nt_semi = char ';' in
  let nt3 = caten nt3 nt_semi in
  let nt3 = pack nt3 (fun (e, _) -> e) in
  let nt3 = pack nt3 (fun (_, e) -> nt_hexString_to_ascii e) in
  let nt3 = only_if nt3 (fun e -> e < 128) in
  let nt3 = pack nt3 (fun e -> String.make 1 (char_of_int e)) in
  nt3 str

and nt_string_literal str = 
  let nt1 = range ' ' '~' in
  let nt2 = word "\\" in 
  let nt3 = word "\"" in
  let nt4 = word "~" in
  let nt1 = diff nt1 nt2 in
  let nt1 = diff nt1 nt3 in
  let nt1 = diff nt1 nt4 in 
  let nt1 = pack nt1 (fun (e) -> String.make 1 e) in
  nt1 str

and nt_string_char str =
  let nt1 = disj_list[nt_string_meta; nt_string_literal; nt_string_hex] in
  nt1 str 

and nt_string_regular str = 
  let nt1 = not_followed_by nt_string_regular_cont (diff nt_any (word "\"")) in
  let nt1 = pack nt1 (fun e -> [e]) in
  nt1 str


and nt_string_regular_cont str = 
  let nt1 = word "\"" in
  let nt2 = diff nt_string_char nt1 in
  let nt2 = plus nt2 in
  let nt2 = pack nt2 (fun (e) -> ScmString(append_strings e)) in
  nt2 str


and nt_with_inter str =
let start = word "\"" in
let nt1 = disj nt_string_interpolated nt_string_regular_cont in
let nt1 = star nt1 in
let ntdiff = diff nt_any start in
let nt1 = not_followed_by nt1 ntdiff in
nt1 str

and nt_string str = 
  let start = word "\"" in
  let nt1 = disj nt_string_regular nt_with_inter in
  let nt1 = caten start (caten nt1 start) in
  (*let nt1 = not_followed_by nt1 nt_any in*)
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  let nt1 = pack nt1 (fun str_elements -> 
                      match str_elements with
                      | [] -> ScmString ""
                      | hd::[] -> hd
                      | hd::tl -> list_to_proper_list ([ScmSymbol "string-append"]@str_elements)) in
  
  nt1 str
  
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and nt_list str =
  let nt1 = char '(' in
  let nt2 = char ')' in
  let dot = char '.' in
  let proper_list = caten nt1 (caten (star nt_sexpr) nt2) in
  let proper_list = pack proper_list (fun (_, (s,_)) -> List.fold_right (fun x y -> ScmPair(x, y))  s ScmNil) in
  let im_proper_list = caten nt1 (caten (plus nt_sexpr) (caten (caten dot nt_sexpr) nt2)) in
  let im_proper_list = pack im_proper_list (fun (_,(ps, ((_, s),_))) -> List.fold_right (fun x y -> ScmPair(x, y))  ps s) in
  let nt1 = disj proper_list im_proper_list in

  (* In order to let (    ) work as ScmNil, we implement below *)
  let nt_nil_1 = char '(' in
  let nt_nil_2 = char ')' in
  let nt3 = nt_skip_star in
  let nt3 = caten nt_nil_1 (caten nt3 nt_nil_2) in
  let nt3 = pack nt3 (fun (_, (_, _)) -> ScmNil) in
  let nt1 = disj nt1 nt3 in
  nt1 str

and nt_quote str = (*Must change nt2 in ScmPair to something else*)
  let nt1 = word "'" in
  let nt2 = nt_sexpr in
  let nt3 = caten nt1 nt2 in
  let nt3 = pack nt3 (fun (_, e) -> ScmPair(ScmSymbol("quote"),
                                 ScmPair(e, ScmNil))) in
  nt3 str

and nt_quasiquote str =
  let nt1 = word "`" in
  let nt2 = nt_sexpr in
  let nt3 = caten nt1 nt2 in
  let nt3 = pack nt3 (fun (_, e) -> ScmPair(ScmSymbol("quasiquote"),
                                 ScmPair(e, ScmNil))) in
  nt3 str

and nt_unquote str =
  let nt1 = word "," in
  let nt2 = nt_sexpr in
  let nt3 = caten nt1 nt2 in
  let nt3 = pack nt3 (fun (_, e) -> ScmPair(ScmSymbol("unquote"),
                                 ScmPair(e, ScmNil))) in
  nt3 str

and nt_unquote_splicing str = 
  let nt1 = word ",@" in
  let nt2 = nt_sexpr in
  let nt3 = caten nt1 nt2 in
  let nt3 = pack nt3 (fun (_, e) -> ScmPair(ScmSymbol("unquote-splicing"),
                                 ScmPair(e, ScmNil))) in
  nt3 str

and nt_quoted_forms str =
  let nt1 = disj_list [nt_quote; nt_quasiquote; nt_unquote; nt_unquote_splicing;] in
  nt1 str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_vector; nt_list; nt_quoted_forms; nt_string] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;