(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec index_of x list = 
  match list with
  | [] -> raise X_this_should_not_happen
  | h :: t -> if x = h then 0 else 1 + index_of x t

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;


  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
        | ScmConst(e) -> ScmConst' e
        | ScmVar(s)   -> ScmVar'(tag_lexical_address_for_var s params env)
        | ScmIf(test, dit, dif) -> ScmIf'(run test params env, 
                                          run dit params env,
                                          run dif params env)

        | ScmSeq(list)-> ScmSeq' (List.map (fun e -> run e params env) list) 
        | ScmSet(ScmVar(var_to), from) -> ScmSet'(tag_lexical_address_for_var var_to params env,
                                              run from params env)
        | ScmDef(ScmVar(name), value)-> ScmDef'(tag_lexical_address_for_var name params env,
                                  run value params env)

        | ScmOr(list) -> ScmOr' (List.map (fun e -> run e params env) list) 
        | ScmLambdaSimple(param_list, body) -> ScmLambdaSimple'(param_list,
                                          (run body param_list (params::env)))

        | ScmLambdaOpt(param_list, option, body) ->  ScmLambdaOpt'(param_list,
                                                                    option,
                                    (run body (param_list @ [option]) (params::env))) 
        | ScmApplic(f, args) ->     ScmApplic' (run f params env, 
                          (List.map (fun e -> run e params env) args))
        | _ -> raise X_this_should_not_happen

        in 
   run pe [] [];;
    
 
  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
    
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
      match pe with
        | ScmConst' _ -> pe
        | ScmVar' _ -> pe
        | ScmIf' (test, dit, dif) -> ScmIf' (run test false, run dit in_tail, run dif in_tail)
        | ScmOr' list ->  
                         let first, last = (rdc_rac list) in 
                         let send_first = List.map (fun (exp) -> run exp false) first in
                         ScmOr' (send_first@[run last true])
        | ScmSet'(var, expr) -> ScmSet' (var, run expr false)
        | ScmDef'(var, expr) -> ScmDef' (var, run expr false)
        | ScmSeq' list -> let first, last = (rdc_rac list) in
                          let send_first = List.map (fun (exp) -> run exp false) first in
                          ScmSeq' (send_first@[run last true])
        | ScmLambdaSimple' (params, body) -> ScmLambdaSimple' (params, run body true)
        | ScmLambdaOpt' (params, option, body) -> ScmLambdaOpt' (params, option, run body true)
        | ScmApplic'(expr, exprs) ->
          if in_tail
            then  ScmApplicTP' (run expr false, all_false exprs)
            else  ScmApplic' (run expr false, all_false exprs)
        | _ -> raise X_this_should_not_happen
      and all_false list = List.map (fun exp -> run exp false) list
   in 
   run pe false;;

  (* boxing *)  

  let var_type name enclosing_lambda var =
    match var with
      | VarFree _ -> []
      | VarParam (var, minor) -> if var = name then [enclosing_lambda] else []
      | VarBound (var, _ , minor) -> if var = name then [enclosing_lambda] else []

  let map_and_concat f list =
    let mapped = List.map f list in
    List.fold_right (fun x y -> x @ y) mapped [];;

  let rec find_reads name enclosing_lambda expr = 
    match expr with
      | ScmSeq' [ScmSet' (VarParam (_, _), ScmBox' (VarParam (_, _))); body ] -> find_reads name enclosing_lambda body
      | ScmConst' _ -> []
      | ScmBoxGet' (_) | ScmBoxSet' (_) -> []
      | ScmBox' (_) -> []
      | ScmVar'(var) -> var_type name enclosing_lambda var
      | ScmIf' (test, dit, dif) -> find_reads name enclosing_lambda test @ find_reads name enclosing_lambda dit @ find_reads name enclosing_lambda dif
      | ScmOr' list -> map_and_concat (fun (exp) -> (find_reads name enclosing_lambda exp)) list
      | ScmSet'(var, exp) -> find_reads name enclosing_lambda exp
      | ScmDef'(var, exp) -> find_reads name enclosing_lambda exp
      | ScmSeq' list -> map_and_concat (fun (exp) -> (find_reads name enclosing_lambda exp)) list
      | ScmApplic'(exp, exps) -> find_reads name enclosing_lambda exp @ map_and_concat (fun (exp) -> (find_reads name enclosing_lambda exp)) exps
      | ScmApplicTP'(exp, exps) -> find_reads name enclosing_lambda exp @ map_and_concat (fun (exp) -> (find_reads name enclosing_lambda exp)) exps
      | ScmLambdaSimple' (new_params, new_body) -> 
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params)
                then 
                  find_reads name expr new_body
                else
                  find_reads name enclosing_lambda new_body
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params) || old_option = name
                then 
                  find_reads name expr new_body
                else
                  find_reads name enclosing_lambda new_body
            | _ -> raise X_this_should_not_happen)
      | ScmLambdaOpt' (new_params, new_option, new_body) ->
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params)
                then 
                  find_reads name expr new_body
                else
                  find_reads name enclosing_lambda new_body
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params) || old_option = name
                then 
                  find_reads name expr new_body
                else
                  find_reads name enclosing_lambda new_body
            
            | _ -> raise X_this_should_not_happen)


 

  let rec find_writes name enclosing_lambda expr = 
    match expr with
      | ScmSeq' [ScmSet' (VarParam (_, _), ScmBox' (VarParam (_, _))); body ] ->  find_writes name enclosing_lambda body
      | ScmConst' _ -> []
      | ScmVar'(var) -> []
      | ScmBoxGet' (_) | ScmBoxSet' (_) -> []
      | ScmBox' (_) -> []
      | ScmIf' (test, dit, dif) -> find_writes name enclosing_lambda test @ find_writes name enclosing_lambda dit @ find_writes name enclosing_lambda dif
      | ScmOr' list -> map_and_concat (fun (exp) -> (find_writes name enclosing_lambda exp)) list
      | ScmSet'(var, exp) -> var_type name enclosing_lambda var
      | ScmDef'(var, exp) -> find_writes name enclosing_lambda exp
      | ScmSeq' list -> map_and_concat (fun (exp) -> (find_writes name enclosing_lambda exp)) list
      | ScmApplic'(exp, exps) -> find_writes name enclosing_lambda exp @ map_and_concat (fun (exp) -> (find_writes name enclosing_lambda exp)) exps
      | ScmApplicTP'(exp, exps) -> find_writes name enclosing_lambda exp @ map_and_concat (fun (exp) -> (find_writes name enclosing_lambda exp)) exps
      | ScmLambdaSimple' (new_params, new_body) -> 
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params)
                then 
                  find_writes name expr new_body
                else
                  find_writes name enclosing_lambda new_body
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params) || old_option = name
                then 
                  find_writes name expr new_body
                else
                  find_writes name enclosing_lambda new_body

            | _ -> raise X_this_should_not_happen)
      | ScmLambdaOpt' (new_params, new_option, new_body) ->
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params)
                then 
                  find_writes name expr new_body
                else
                  find_writes name enclosing_lambda new_body
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params)
              then []
              else
                if (List.exists (fun (p) -> name = p) old_params) || old_option = name
                then 
                  find_writes name expr new_body
                else
                  find_writes name enclosing_lambda new_body

            | _ -> raise X_this_should_not_happen)
  
  let create_return_for_check_box bool read =
    match read with
    | (lambda, p_or_b, index) -> (lambda, bool, p_or_b, index)

  let check_box name enclosing_lambda expr = 
    let reads = find_reads name enclosing_lambda expr in 
    let writes = find_writes name enclosing_lambda expr in
    try
      List.exists (fun r -> List.exists (fun (w) -> not (expr'_eq r w)) writes) reads
    with 
      Invalid_argument _ -> true
    

    let start_of_lambda name enclosing_lambda expr = 
    match enclosing_lambda with
    | ScmLambdaSimple'(params, body) -> if body = expr then
                                        (match body with
                                        | ScmSeq'(list) -> let add_set = ScmSet' (VarParam (name, index_of name params), ScmBox' (VarParam (name, index_of name params))) in
                                                           let new_list = add_set :: list in
                                                           ScmSeq'(new_list)
                                        | _ -> ScmSeq' [ScmSet' (VarParam (name, index_of name params), ScmBox' (VarParam (name, index_of name params))); body ])
                                        
                                        else enclosing_lambda 
    | ScmLambdaOpt'(params, option, body) -> if body = expr then 
                                              (match body with
                                             
                                              | ScmSeq'(list) -> let add_set = ScmSet' (VarParam (name, index_of name (params @ [option])), ScmBox' (VarParam (name, index_of name (params @ [option])))) in
                                                                 let new_list = add_set :: list in
                                                                 ScmSeq'(new_list)
                                              | _ -> ScmSeq' [ScmSet' (VarParam (name, index_of name (params @ [option])), ScmBox' (VarParam (name, index_of name (params @ [option])))); body ])
                                              
                                                 else enclosing_lambda
    | _ -> raise X_this_should_not_happen
                                          
  let rec boxing name enclosing_lambda expr =
    match expr with
      | ScmConst' c -> ScmConst' c

      | ScmBoxGet'(a) -> ScmBoxGet'(a)
      | ScmBox' _ -> expr
      | ScmBoxSet' (VarFree(var), from) -> ScmBoxSet'(VarFree(var), boxing name enclosing_lambda from)
      | ScmBoxSet' (VarParam(var, i1), from) -> ScmBoxSet'(VarParam(var, i1), boxing name enclosing_lambda from)
      | ScmBoxSet' (VarBound(var, i1, i2), from) -> ScmBoxSet'(VarBound(var, i1, i2), boxing name enclosing_lambda from)
      | ScmVar' (VarFree (var)) -> if var = name then ScmBoxGet'(VarFree(var)) else ScmVar' (VarFree (var))
      | ScmVar' (VarParam (var, i1)) -> if var = name then ScmBoxGet'(VarParam(var, i1)) else ScmVar' (VarParam (var, i1))
      | ScmVar' (VarBound (var, i1, i2)) -> if var = name then ScmBoxGet'(VarBound(var, i1, i2)) else ScmVar' (VarBound (var, i1, i2))

      | ScmSet' (VarParam (var1, i1), ScmBox' (VarParam (var2, i2))) -> expr

      | ScmSet' (VarFree(var), from) -> if var = name 
                                        then ScmBoxSet'(VarFree(var), boxing name enclosing_lambda from)
                                        else ScmSet' (VarFree(var), boxing name enclosing_lambda from)

      | ScmSet' (VarParam (var, i1), from) -> if var = name
                                              then ScmBoxSet'(VarParam (var, i1), boxing name enclosing_lambda from)
                                              else ScmSet' (VarParam (var, i1), boxing name enclosing_lambda from)
      | ScmSet' (VarBound (var, i1, i2), from) -> if var = name
                                                  then ScmBoxSet'(VarBound (var, i1, i2), boxing name enclosing_lambda from)
                                                  else ScmSet' (VarBound (var, i1, i2), boxing name enclosing_lambda from)
                                                  
      | ScmIf'(test, dit, dif) -> ScmIf'(boxing name enclosing_lambda test, 
                                        boxing name enclosing_lambda dit,
                                        boxing name enclosing_lambda dif)

      | ScmSeq' (list) ->  ScmSeq' (List.map (fun (exp) -> boxing name enclosing_lambda exp) list)
      
      | ScmDef'(VarFree(var), value)-> ScmDef'(VarFree(var), boxing name enclosing_lambda value)
      | ScmDef'(VarParam(var, i1), value)-> ScmDef'(VarParam(var, i1), boxing name enclosing_lambda value)
      | ScmDef'(VarBound(var, i1, i2), value)-> ScmDef'(VarBound(var, i1, i2), boxing name enclosing_lambda value)

      | ScmOr'(list) -> ScmOr' (List.map (fun (exp) -> boxing name enclosing_lambda exp) list) 
      | ScmApplic'(f, args) -> ScmApplic' (boxing name enclosing_lambda f, 
                        (List.map (fun (exp) -> boxing name enclosing_lambda exp) args))
      | ScmApplicTP' (f, args) -> ScmApplicTP' (boxing name enclosing_lambda f, 
                        (List.map (fun (exp) -> boxing name enclosing_lambda exp) args))

      | ScmLambdaSimple' (new_params, new_body) -> 
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params)
              then 
                ScmLambdaSimple' (new_params, new_body)
              else
                ScmLambdaSimple' (new_params ,(boxing name enclosing_lambda new_body))
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params) 
              then 
                ScmLambdaSimple' (new_params, new_body)
              else
                ScmLambdaSimple' (new_params ,(boxing name enclosing_lambda new_body))

            | _ -> raise X_this_should_not_happen)
      | ScmLambdaOpt' (new_params, new_option, new_body) ->
          (match enclosing_lambda with
            | ScmLambdaSimple' (old_params, old_body) -> 
              if (List.exists (fun (p) -> name = p) new_params) || new_option = name
              then 
                ScmLambdaOpt' (new_params, new_option, new_body)
              else
                ScmLambdaOpt' (new_params , new_option, (boxing name enclosing_lambda new_body))
            | ScmLambdaOpt' (old_params, old_option, old_body) ->
              if (List.exists (fun (p) -> name = p) new_params) || new_option = name
              then 
                ScmLambdaOpt' (new_params, new_option, new_body)
              else
                ScmLambdaOpt' (new_params , new_option, (boxing name enclosing_lambda new_body))
            | _ -> raise X_this_should_not_happen)

  let boxing_before name enclosing_lambda expr =
    if check_box name enclosing_lambda expr 
    then boxing name enclosing_lambda (start_of_lambda name enclosing_lambda expr)
    else expr

  let rec fold_body_simple_rec original_params params expr body = 
    match params with
    | hd :: tl -> let body_after_box = boxing_before hd expr body in
           let expr_after_box = ScmLambdaSimple' (original_params, body_after_box) in
           fold_body_simple_rec original_params tl expr_after_box body_after_box

    | [] -> body

  let fold_body_simple params expr body = 
    fold_body_simple_rec params (List.rev params) expr body

  let rec fold_body_opt_rec original_params params option expr body = 
    match params with
    | hd :: tl -> let body_after_box = boxing_before hd expr body in
           let expr_after_box = ScmLambdaOpt' (original_params, option, body_after_box) in
           fold_body_opt_rec original_params tl option expr_after_box body_after_box

    | [] -> let body_after_box = boxing_before option expr body in
            body_after_box

  let fold_body_opt params option expr body = 
    fold_body_opt_rec params (List.rev params) option expr body

  let rec box_set expr = 
    match expr with
      | ScmSet' (VarParam (_, _), ScmBox' (VarParam (_, _))) -> expr
      | ScmConst' _ -> expr
      | ScmVar' _ -> expr
      | ScmBoxGet'(_) | ScmBoxSet'(_) -> expr
      | ScmBox'(_) -> expr
      | ScmIf' (test, dit, dif) -> ScmIf' (box_set test, box_set dit, box_set dif)
      | ScmOr' list -> ScmOr' (List.map box_set list)
      | ScmSet'(var, expr) -> ScmSet' (var, box_set expr)
      | ScmDef'(var, expr) -> ScmDef' (var, box_set expr)
      | ScmSeq' list -> ScmSeq' (List.map box_set list)
      | ScmApplic'(expr, exprs) -> ScmApplic' (box_set expr, (List.map box_set exprs))
      | ScmApplicTP'(expr, exprs) -> ScmApplicTP' (box_set expr, (List.map box_set exprs))
      | ScmLambdaSimple' (params, body) -> let body_after_box = fold_body_simple params expr body in
                                           ScmLambdaSimple' (params, box_set body_after_box)

      | ScmLambdaOpt' (params, option, body) -> let body_after_box = fold_body_opt params option expr body in
                                                ScmLambdaOpt' (params, option, box_set body_after_box)
      
                                                

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

   (* let run_semantics expr =
    box_set
         (annotate_lexical_addresses expr) *)

end;; (* end of module Semantic_Analysis *)
