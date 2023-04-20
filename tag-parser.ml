#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;





let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

(* takes a scheme improper list (nested pairs) and convert it to ocaml list with the last element as the non nil end*)
let rec scm_improp_list_to_list_no_end  = function
| ScmPair (exp, rest) -> [exp] @ (scm_improp_list_to_list_no_end rest)
| last -> []

let rec scm_improp_list_end  = function
| ScmPair (_, rest) -> (scm_improp_list_end rest)
| last -> last


let scm_improp_list_to_list_and_end scm_list = 
  (scm_improp_list_to_list_no_end scm_list), (scm_improp_list_end scm_list) ;;

let rec scm_is_improper_list = function
| ScmPair (hd, tl) -> scm_is_improper_list tl
| ScmNil -> false
| _ -> true

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;



module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct


let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let is_reserved var =
    (List.exists (fun (e) -> var = e) reserved_word_list);;



let rec sexpr_to_list_rec sexpr list =
  match sexpr with
  | ScmNil -> list
  | ScmPair(car, cdr) -> (sexpr_to_list_rec cdr (list @ [car]))
  | _ -> raise (X_syntax_error (sexpr,  "not a valid list"))
  

let sexpr_to_list sexpr =
  sexpr_to_list_rec sexpr [];;


let rec list_to_sexpr_rec sexpr list =
  match list with
  | [] -> sexpr
  | _ -> (list_to_sexpr_rec (ScmPair((List.hd list), sexpr)) (List.tl list))

let list_to_sexpr list =
  list_to_sexpr_rec ScmNil (List.rev list);;

let take_out_of_pair sexpr = 
 match sexpr with
  | ScmPair(ret, ScmNil) -> ret 
  | last -> last;;

let rec l_star_to_l vars_apply body = 
  (if (List.length vars_apply > 1) then 
    ScmPair(ScmPair(ScmSymbol "let", ScmPair(ScmPair((List.hd vars_apply), ScmNil), (l_star_to_l (List.tl vars_apply) body))), ScmNil)
   else
    ScmPair(ScmPair(ScmSymbol "let", ScmPair(ScmPair((List.hd vars_apply), ScmNil), ScmPair((List.hd body), ScmNil))), ScmNil))

let make_set var_apply =
    ScmPair(ScmSymbol "set!", var_apply);;

let remove_outer_pair sexpr = 
  match sexpr with
  | ScmPair(ScmPair(a, b), ScmNil) -> ScmPair(a,b)
  | _ -> ScmNil;;


let create_arrow_let left right cont =
ScmPair
   (ScmSymbol "let",
    ScmPair
     (ScmPair
       (ScmPair (ScmSymbol "value", ScmPair (left, ScmNil)),
        ScmPair
         (ScmPair
           (ScmSymbol "f",
            ScmPair
             (ScmPair
               (ScmSymbol "lambda",
                ScmPair (ScmNil, ScmPair (right, ScmNil))),
              ScmNil)),
          ScmPair
           (ScmPair
             (ScmSymbol "rest",
              ScmPair
               (ScmPair
                 (ScmSymbol "lambda",
                  ScmPair (ScmNil, cont)),
                ScmNil)),
            ScmNil))),
      ScmPair
       (ScmPair
         (ScmSymbol "if",
          ScmPair
           (ScmSymbol "value",
            ScmPair
             (ScmPair
               (ScmPair (ScmSymbol "f", ScmNil),
                ScmPair (ScmSymbol "value", ScmNil)),
              ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
        ScmNil)))
  

let rec qq_list_expand sexpr =
  (* Printf.printf "\nSexpr right now is: %s\n" (string_of_sexpr sexpr); *)
  match sexpr with
  (* Regular symbol *)
  | ScmPair(ScmSymbol(a), rest) -> ScmPair(ScmSymbol "cons", ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol(a), ScmNil)) , ScmPair((qq_list_expand rest), ScmNil)))
  (* Regular char *)
  | ScmPair(ScmChar(a), rest) -> ScmPair(ScmSymbol "cons", (ScmPair(ScmChar(a), ScmPair((qq_list_expand rest), ScmNil))))
  (* Regular string *)
  | ScmPair(ScmString(d), rest) -> ScmPair(ScmSymbol "cons", ScmPair(ScmString(d), ScmPair((qq_list_expand rest), ScmNil)))
  (* Quote before something *)
  (* unquote symbol *)
  | ScmPair(ScmPair(ScmSymbol "unquote", ScmPair(inside, ScmNil)), rest) -> (ScmPair(ScmSymbol "cons", ScmPair(inside, ScmPair((qq_list_expand rest) , ScmNil))))
  (* unquote-splicing symbol *)
  (* | ScmPair(ScmSymbol "unquote-splicing", ScmPair(rest, ScmNil)) -> (ScmPair(ScmSymbol "append", ScmPair((qq_list_expand rest), ScmNil))) *)
  | ScmPair(ScmPair(ScmSymbol "unquote-splicing", ScmPair(inside, ScmNil)), rest) -> (ScmPair(ScmSymbol "append", ScmPair(inside, ScmPair((qq_list_expand rest), ScmNil))))
  (* Put something in a list of itself *)
  | ScmPair(rest1, rest2) -> ScmPair(ScmSymbol "cons", ScmPair((qq_list_expand rest1), ScmPair((qq_list_expand rest2), ScmNil)))
  (* End *)
  | ScmNil -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil, ScmNil))
  | _ -> sexpr
    
let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with

(* Implement tag parsing here *)
(* Const base cases *)
| ScmNil -> ScmConst (ScmNil)
| ScmBoolean (b) -> ScmConst(ScmBoolean (b))
| ScmChar (c) -> ScmConst (ScmChar (c))
| ScmNumber(x) -> ScmConst (ScmNumber (x))
| ScmString (s) -> ScmConst (ScmString (s))
| ScmPair (ScmSymbol ("quote"), ScmPair (cdr, ScmNil)) -> ScmConst (cdr)
(* Vector *)
| ScmVector(s) -> ScmConst(ScmVector(s))
(* Variables *)
| ScmSymbol (s) -> if (List.exists (fun (e) -> s = e) reserved_word_list) then raise (X_reserved_word s) else ScmVar (s) 

(* Conditionals *)
| ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair(dif, ScmNil)))) -> ScmIf ((tag_parse_expression test), (tag_parse_expression dit), (tag_parse_expression dif))
| ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil))) -> ScmIf ((tag_parse_expression test), (tag_parse_expression dit), (ScmConst (ScmVoid)))

(* Disjunctions - or  *)
| ScmPair (ScmSymbol "or", ScmNil) -> ScmConst (ScmBoolean false)
| ScmPair (ScmSymbol "or", ScmPair(exp, ScmNil)) -> (tag_parse_expression exp)
| ScmPair (ScmSymbol "or", rest) -> ScmOr (List.map tag_parse_expression (scm_list_to_list rest))

(* Lambda *)
| ScmPair (ScmSymbol "lambda", ScmPair (ScmSymbol (s), body)) -> let body_list = (List.map tag_parse_expression (scm_list_to_list body)) in
                                                        ScmLambdaOpt([], s, (if List.length body_list = 1 then (List.hd body_list) else (ScmSeq body_list)))

| ScmPair (ScmSymbol "lambda", ScmPair (args, body)) -> (let body_list = (List.map tag_parse_expression (scm_list_to_list body)) in
                                                         let body_list = (if List.length body_list = 1 then (List.hd body_list) else (ScmSeq body_list)) in
                                                         let unbox_args args = match args with
                                                                                | (ScmSymbol e ) -> e
                                                                                | _ -> "Erorr, arg not a string" in
                                                         if (scm_is_list args) then 
                                                                      (ScmLambdaSimple(List.map unbox_args (scm_list_to_list args), body_list))
                                                                      else (
                                                                        let (opt_args, arg) = scm_improp_list_to_list_and_end args in
                                                                        ScmLambdaOpt (List.map unbox_args opt_args, (string_of_sexpr arg), body_list)))

| ScmPair (ScmSymbol "define", ScmPair (ScmSymbol var, ScmPair (val_, ScmNil))) -> (let val_expr = tag_parse_expression val_ in
                                                                                    ScmDef((ScmVar var), val_expr))

(* Assignments *)
| ScmPair (ScmSymbol "set!", ScmPair(ScmSymbol var, ScmPair(val_, ScmNil))) -> (let val_expr = tag_parse_expression val_ in 
                                                                                if (List.exists (fun (e) -> var = e) reserved_word_list) then
                                                                                  raise (X_syntax_error (sexpr, "Reserved word in LHS of set!"))
                                                                                else
                                                                                  ScmSet((ScmVar var), val_expr))

| ScmPair (ScmSymbol "set!", ScmPair(not_good, rest)) -> raise (X_syntax_error (not_good, "Let structure not recognized"))

(* Sequences *)
| ScmPair(ScmSymbol "begin", rest) -> (let rest_list = (sexpr_to_list rest) in
                                       let rest_parsed = (List.map tag_parse_expression (scm_list_to_list rest)) in
                                       (if ((List.length rest_list) == 1) then
                                          (List.hd rest_parsed)
                                        else
                                          ScmSeq(rest_parsed)))

 (* Applications *)
 (* Regular application *)  
| ScmPair(ScmSymbol var, cont) -> let all = (List.map tag_parse_expression (scm_list_to_list cont)) in
                                  if (List.exists (fun (e) -> var = e) reserved_word_list) then
                                    raise (X_syntax_error(sexpr, "Application can't use reserved word on LHS"))
                                  else 
                                    ScmApplic(ScmVar(var), all)

| ScmPair(ScmChar(ch), cont) ->  let all = (List.map tag_parse_expression (scm_list_to_list cont)) in
                                 let ch = ScmChar(ch) in
                                 let cha = (tag_parse_expression ch) in
                                 ScmApplic(cha, all)

| ScmPair(ScmPair(ScmSymbol "lambda", lambda_cont ), insert) -> (let lambda_temp = ScmPair(ScmSymbol "lambda", lambda_cont) in
                                                                let lambda_parsed = tag_parse_expression lambda_temp in
                                                                let insert_parsed = (List.map tag_parse_expression (scm_list_to_list insert)) in
                                                                match lambda_parsed with
                                                                | ScmLambdaSimple(_) | ScmLambdaOpt(_) ->  ScmApplic(lambda_parsed, insert_parsed)
                                                                | _ -> raise (X_syntax_error (sexpr, "not a valid lambda struct")))

| ScmPair(apply, cont) -> let all = (List.map tag_parse_expression (scm_list_to_list cont)) in
                                    ScmApplic((tag_parse_expression apply), all)           

| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))



and macro_expand sexpr =
match sexpr with

(* Handle macro expansion patterns here *)

(* Let Expression *)
| ScmPair(ScmSymbol "let", rest) -> (expand_let rest)                       

(* Let Star Expressions *)
| ScmPair(ScmSymbol "let*", rest) -> (expand_let_star rest)


| ScmPair(ScmSymbol "letrec", rest) -> (expand_let_rec rest)

                                                             
| ScmPair(ScmSymbol "cond", cont) ->  (take_out_of_pair (expand_cond cont))
                                       
                                      
(* MIT Define *)
| ScmPair(ScmSymbol "define", ScmPair(ScmPair(ScmSymbol (def_name), vars), body)) -> 
  ScmPair(ScmSymbol "define", ScmPair(ScmSymbol(def_name), ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(vars , body)), ScmNil)))

| ScmPair(ScmSymbol "and", rest) -> (expand_and (sexpr_to_list rest))

| ScmPair(ScmSymbol "quasiquote", rest) -> (expand_qq rest)
                                            
| _ -> sexpr

and expand_let rest = 
match rest with
| ScmPair(vars_apply, body)  ->
                  (let vars_apply_list = sexpr_to_list vars_apply in
                   let get_var vars_apply = match vars_apply with
                                   | (ScmPair(ScmSymbol(e), ScmPair(value, ScmNil))) -> ScmSymbol(e)
                                   | _ -> raise (X_syntax_error (vars_apply, "boken var")) in
                   let get_apply vars_apply = match vars_apply with
                                   | (ScmPair(ScmSymbol(e), ScmPair(value, ScmNil))) -> value
                                   | _ -> raise (X_syntax_error (vars_apply, "boken apply")) in
                    let all_vars = (List.map get_var vars_apply_list) in                                                                                                      
                    let all_apply = (List.map get_apply vars_apply_list) in 
                    let vars_sexpr = (list_to_sexpr all_vars) in                        
                    let apply_sexpr = (list_to_sexpr all_apply) in
                    ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(vars_sexpr, body)), apply_sexpr))
| _ -> raise (X_syntax_error (rest, "Let structure not recognized"))

and expand_let_star rest =
match rest with
| ScmPair(ScmNil, body) -> ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, body)), ScmNil)

(* Let Star Regular *)
| ScmPair(vars_apply, body) -> (let vars_apply_list = sexpr_to_list vars_apply in
                                                           let body_list = sexpr_to_list body in
                                                           let stage1 = (l_star_to_l vars_apply_list body_list) in
                                                           (macro_expand (take_out_of_pair stage1)))
                                                          
| _ -> raise (X_syntax_error (rest, "Let star structure not recognized"))

and expand_let_rec rest =
match rest with
| ScmPair(vars_apply, body) -> (let get_vars_and_whatervr vars_apply = match vars_apply with
                          | ScmPair(ScmSymbol(e), ScmPair(value, ScmNil)) -> 
                              ScmPair(ScmSymbol(e), ScmPair(ScmPair (ScmSymbol ("quote"), ScmPair (ScmSymbol "whatever", ScmNil)), ScmNil))
                          |_ -> raise (X_syntax_error (rest, "not a vaild let rec exp")) in
                          
                                let vars_and_whatever = scm_map get_vars_and_whatervr vars_apply in
                                let vars_apply_list = (sexpr_to_list vars_apply) in
                                let vars_apply_wrapped = ScmPair(vars_and_whatever, ScmNil) in
                                let vars_apply_wrapped_list = (sexpr_to_list vars_apply_wrapped) in
                                let set_list = (List.map make_set vars_apply_list) in

                                let vars_apply_set_list = vars_apply_wrapped_list @ set_list in

                                let body_sexpr = body in
                                let body_list = (sexpr_to_list body_sexpr) in
                                let full_list = vars_apply_set_list   @ body_list in
                                let full = (list_to_sexpr full_list) in
                                
                                
                                (macro_expand (ScmPair(ScmSymbol "let", full))))
| _ -> raise (X_syntax_error (rest, "Let rec structure not recognized"))

and expand_cond sexpr = 
  match sexpr with
  | ScmPair(ScmSymbol "cond", rest) -> expand_cond rest

  | ScmPair(ScmPair(ScmSymbol "else", ScmPair(a, ScmPair(b, rest1))), rest2) -> let send = ScmPair(a, ScmPair(b, rest1)) in
                                                                                ScmPair(ScmPair(ScmSymbol "begin", (macro_expand send)), ScmNil)
  | ScmPair(ScmPair(ScmSymbol "else", a), rest2) -> (macro_expand a)
  | ScmPair(ScmPair(a, ScmPair(ScmSymbol "=>", ScmPair(b, ScmNil))), rest) -> ScmPair(macro_expand (create_arrow_let a b (expand_cond rest)), ScmNil)
                                                                              
  | ScmPair(ScmPair(a, ScmPair(b, ScmPair(c, rest1))), rest2) -> let send = ScmPair(b, ScmPair(c, rest1)) in
                                                                 ScmPair(ScmPair(ScmSymbol "if", ScmPair(a, ScmPair(ScmPair(ScmSymbol "begin", macro_expand send), expand_cond rest2))), ScmNil)
  | ScmPair(ScmPair(a, ScmPair(b, ScmNil)), rest) -> ScmPair(ScmPair(ScmSymbol "if", ScmPair(a, ScmPair(b, expand_cond rest))), ScmNil)
  | ScmNil -> ScmNil
  | _ -> raise (X_syntax_error (sexpr, "Cond structure not recognized"))
  

 and expand_and list =
  ((if ((List.length list == 1)) then
    (List.hd list)
  else if ((List.length list == 2)) then
    ScmPair(ScmSymbol "if", ScmPair((List.hd list), ScmPair((List.hd (List.tl list)), ScmPair(ScmBoolean false, ScmNil))))
  else if ((List.length list > 2)) then
    ScmPair(ScmSymbol "if", ScmPair((List.hd list), ScmPair((expand_and (List.tl list)) , ScmPair(ScmBoolean false, ScmNil))))
  else
    ScmBoolean(true)))

  and expand_qq sexpr =
  match sexpr with
  | ScmPair(ScmPair(ScmPair(ScmSymbol "unquote", rest), ScmNil), ScmNil) -> let send = ScmPair(ScmPair(ScmSymbol "unquote", rest), ScmNil) in
                                                                            (qq_list_expand send)
  | ScmPair(ScmPair(ScmPair(ScmSymbol "unquote-splicing", rest), ScmNil), ScmNil) -> let send = ScmPair(ScmPair(ScmSymbol "unquote-splicing", rest), ScmNil) in
                                                                            (qq_list_expand send)
  | ScmPair(ScmVector(rest), ScmNil) ->  ScmPair(ScmSymbol "list->vector", ScmPair((qq_list_expand (list_to_sexpr rest)), ScmNil))
  | ScmPair(ScmPair(ScmSymbol "unquote", ScmPair(ScmSymbol(a), ScmNil)), ScmNil) -> ScmSymbol(a) (*qq regular expand *)
  | ScmPair(ScmPair(ScmSymbol "unquote-splicing", rest), ScmNil) -> ScmPair(ScmSymbol "quote", ScmPair(ScmPair(ScmSymbol "unquote-splicing", rest), ScmNil))(*qq regular expand *)
  | ScmPair(ScmPair(a, rest), ScmNil) -> let send = ScmPair(a, rest) in (*Is list*)
                                                    (qq_list_expand send)
  
  | ScmPair(ScmSymbol(a), ScmNil) -> ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol(a), ScmNil))
  | ScmNil -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil, ScmNil))
  | _ -> ScmPair(ScmSymbol "quote", ScmPair(ScmNil, ScmNil))


end;; 


                       

