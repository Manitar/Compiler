#use "semantic-analyser.ml";;

type const_table_entry = Const_Table_Entry of sexpr * int * string
type const_table = Const_Table of const_table_entry list * int

exception Exception_code_gen_rdc_rac

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
   
     val make_consts_tbl : expr' list -> (*const_table*) const_table_entry list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
    val make_fvars_tbl : expr' list -> (string * int) list
  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : const_table_entry list -> (string * int) list -> expr' -> string

  val find_entry : sexpr -> const_table_entry list -> int 
end;;

module Code_Gen : CODE_GEN = struct

let rec rdc_rac s =
  match s with
  | [e] -> ([], e)
  | e :: s ->
      let (rdc, rac) = rdc_rac s
      in (e :: rdc, rac)
  | _ -> raise Exception_code_gen_rdc_rac;;

let take_out_of_const e =
  match e with
  | ScmConst'(a) -> a
  | _ -> raise X_this_should_not_happen

let put_in_const e =
  match e with
  | e -> ScmConst'(e)

let make_counter () =
  let x = ref 0 in
  let get () = !x in
  let inc () = x := !x + 1 in
  let inc_and_get() =
    inc();
    get() in
  inc_and_get;;

let inc_and_get = make_counter()

let map_and_concat f list =
  let mapped = List.map f list in
  List.fold_right (fun x y -> x @ y) mapped []

let find_index_in_free_table fvar_table name =
  let name, index = List.find (fun ((n, i)) -> name = n) fvar_table in
  index

let remove_duplicates list = (* Reverses list, removes duplicates from right, reverses list again *)
    let check_has cdr car = if List.mem car cdr then cdr else car :: cdr in
    let remove_from_left lst = List.rev (List.fold_left check_has [] lst) in
    remove_from_left list

let get_entries table =
    match table with
  | Const_Table(entries, _) -> entries

let rec find_entry sexpr table =
  match table with
    | [] -> -1
    | entry :: entries -> 
      match entry with
      | Const_Table_Entry(s, o, _) -> if (sexpr_eq s sexpr) then o else find_entry sexpr entries

let transform_char c =
  match c with
  | '\000' -> 0
  | _ -> (int_of_char c)


let sexpr_to_asm sexpr table =
  match sexpr with 
    | ScmVoid    -> "db T_VOID"
    | ScmNil     -> "db T_NIL"
    | ScmBoolean(v) -> if v then "db T_BOOL, 1" else "db T_BOOL, 0"
    | ScmChar(c) -> Printf.sprintf "MAKE_LITERAL_CHAR %d" (transform_char c)
    | ScmString(s) -> Printf.sprintf "MAKE_LITERAL_STRING %d, '%s'" (String.length s) s
    | ScmSymbol(s) -> Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (find_entry (ScmString(s)) table)
    | ScmNumber(ScmRational(u, d)) -> Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" u d
    | ScmNumber(ScmReal(n)) -> Printf.sprintf "MAKE_LITERAL_FLOAT %f" n
    | ScmVector (elements) -> Printf.sprintf "db T_VECTOR\n dq %d\n" (List.length elements) ^ (List.fold_left (fun code e -> code ^ Printf.sprintf "dq (const_tbl+%d)\n" (find_entry e table)) "" elements)
    | ScmPair (car, cdr) -> Printf.sprintf "MAKE_LITERAL_PAIR ((const_tbl+%d), (const_tbl+%d))" (find_entry car table) (find_entry cdr table)

  let sexpr_to_asm_size sexpr =
  match sexpr with 
    | ScmVoid | ScmNil  -> 1
    | ScmBoolean(_) | ScmChar (_) -> 1 + 1
    | ScmNumber(ScmRational(_)) -> 1 + 8 + 8
    | ScmNumber(_) | ScmSymbol(_) -> 1 + 8
    | ScmString(s) -> 1 + 8 + (String.length s)
    | ScmVector (elements) -> 1 + 8 + 8*(List.length elements)
    | ScmPair (car, cdr) -> 1 + 8 + 8

let add_entry table sexpr = 
  match table with
  | Const_Table(entries, offset) ->  Const_Table(entries @ [Const_Table_Entry(sexpr, offset ,(sexpr_to_asm sexpr (get_entries table)))],
                                                (sexpr_to_asm_size sexpr) + offset)

let expand_consts_table list = 
  List.fold_left (fun const_table const -> add_entry const_table const)
      (Const_Table([], 0))
      list
                

let make_consts_tbl asts = 
    
    let rec first_pass ast = 
      match ast with
      | ScmConst' e -> [e]
      | ScmVar' _ -> []
      | ScmBox' _ -> []
      | ScmBoxGet' _ -> []
      | ScmBoxSet' (var, exp) -> first_pass exp
      | ScmIf' (test, dit, dif) -> first_pass test @ first_pass dit @ first_pass dif
      | ScmSeq' (list) -> map_and_concat first_pass list
      | ScmSet' (var, exp) -> first_pass exp
      | ScmDef' (var, exp) -> first_pass exp
      | ScmOr' list -> map_and_concat first_pass list
      | ScmLambdaSimple' (params, expr) -> first_pass expr
      | ScmLambdaOpt' (params, option, expr) -> first_pass expr
      | ScmApplic' (exp, exprs) -> first_pass exp @ map_and_concat first_pass exprs
      | ScmApplicTP' (exp, exprs) -> first_pass exp @ map_and_concat first_pass exprs in

   

    let second_pass sexprs =
      let rec single_pass sexpr =
        match sexpr with
        | ScmVoid -> [sexpr]
        | ScmNil -> [sexpr]
        | ScmBoolean _ -> [sexpr]
        | ScmChar _ -> [sexpr]
        | ScmString _ -> [sexpr]
        | ScmSymbol (s) -> [ScmString(s); sexpr]
        | ScmNumber _ -> [sexpr]
        | ScmVector (list) -> map_and_concat single_pass list @ [sexpr]
        | ScmPair (car, cdr) -> single_pass car @ single_pass cdr @ [sexpr] in
    
      map_and_concat single_pass sexprs in

    get_entries(
      expand_consts_table(
        remove_duplicates(
          second_pass(
            remove_duplicates(
              ([ScmVoid ; ScmNil ; ScmBoolean (false) ; ScmBoolean (true)] @ map_and_concat first_pass asts))))))
    ;;

    

  let make_fvars_tbl asts =
    let rec find_free_vars ast =
      match ast with
      | ScmConst' _ -> []
      | ScmVar'(VarFree var) -> [var]
      | ScmVar' _ -> [] 
      | ScmBox' _ -> []
      | ScmBoxGet' e -> []
      | ScmBoxSet' (var, exp) -> find_free_vars exp
      | ScmIf' (test, dit, dif) -> find_free_vars test @ find_free_vars dit @ find_free_vars dif
      | ScmSeq' (list) -> map_and_concat find_free_vars list
      | ScmSet' (var, exp) -> find_free_vars exp
      | ScmDef' (var, exp) -> find_free_vars (ScmVar'(var)) @ find_free_vars exp
      | ScmOr' list -> map_and_concat find_free_vars list
      | ScmLambdaSimple' (params, expr) -> find_free_vars expr
      | ScmLambdaOpt' (params, option, expr) -> find_free_vars expr
      | ScmApplic' (exp, exprs) -> find_free_vars exp @ map_and_concat find_free_vars exprs
      | ScmApplicTP' (exp, exprs) -> find_free_vars exp @ map_and_concat find_free_vars exprs in

    let init_free_vars =
      [("boolean?", 0); ("flonum?", 1); ("rational?", 2); ("pair?", 3);
      ("null?", 4); ("char?", 5); ("string?", 6); ("procedure?", 7);
      ("symbol?", 8); ("string-length",9); ("string-ref", 10); ("string-set!", 11);
      ("make-string", 12); ("symbol->string", 13); ("char->integer", 14);
      ("integer->char", 15); ("exact->inexact", 16); ("eq?", 17); ("+", 18); ("*", 19);
      ("/", 20); ("=", 21); ("<", 22); ("numerator", 23); ("denominator", 24);
      ("gcd", 25); ("apply", 26); ("car", 27); ("cdr", 28); ("cons", 29);
      ("set-car!", 30); ("set-cdr!", 31)] in


    let rec index_free_vars list i =
      match list with
      | car :: cdr -> [(car, i)] @ index_free_vars cdr (i+1)
      | [] -> [] in


    

    let add_index list = 
      index_free_vars list 32 in

   
    init_free_vars @ (add_index (remove_duplicates (map_and_concat find_free_vars asts)))



  let generate consts fvars expr  = 
   let rec copyEnv toCopy offset =
      if toCopy <= 0 then "" 
                    else  let copy_var = Printf.sprintf ("mov rcx, [rbx + 8 * %d]       ; copy the var at Env[%d] to rcx\n" ^^
                                                        "mov [rax + 8 * (%d + 1)], rcx ; and from rcx to the ExtEnv[%d]\n") offset offset offset (offset + 1) in
                              copy_var ^ copyEnv (toCopy - 1) (offset + 1) in

        
    let opt_to_list num_of_args = Printf.sprintf ("mov rdx, num_of_params       ; number of params in stack \n" ^^
                                      "mov r8, rdx                  ; number of args before fix\n" ^^
                                      "mov rax, PVAR(rdx)           ; rax -> '()\n" ^^
                                      ".loopOpt:\n" ^^
                                      "cmp rdx, %d\n" ^^
                                      "je .endloopOpt\n" ^^
                                      "dec rdx\n" ^^
                                      "mov rcx, PVAR(rdx)\n" ^^
                                      "MAKE_PAIR(rbx, rcx, rax) ; caten the list\n" ^^
                                      "mov rax, rbx\n" ^^
                                      "jmp .loopOpt\n" ^^
                                      ".endloopOpt:\n" ^^
                                      "mov PVAR(%d), rax           ; copy the opt list to the last param location\n" ^^
                                      "cmp qword num_of_params, %d       ; if num_of_param < num_of_param after fix then no need to fix the param\n" ^^
                                      "mov qword num_of_params, %d  ; adjust number of param to the correct number\n" ^^
                                      "jl .no_fix\n" ^^
                                      "FIX_MORE_PARAMS r8, %d\n" ^^
                                      "inc qword num_of_params  ; adjust number of param after fix to include nil (so opt and TP works)\n" ^^
                                       ".no_fix:\n") num_of_args num_of_args (num_of_args + 1) (num_of_args + 1)  (num_of_args + 1)  in


    let copy_param label = Printf.sprintf ("mov r8, 0                   ; r8 = offset of param\n" ^^
                                      ".loop:\n" ^^ 
                                      "cmp r8, rdx\n" ^^
                                      "je .endloop\n" ^^
                                      "mov rcx, PVAR(r8)            ; copy the r8 param at the stack to rcx\n" ^^
                                      "mov [rax + 8 *r8], rcx       ; and from rcx to the ExtEnv[0][r8]\n" ^^
                                      "inc r8                       ; remove last push\n" ^^ 
                                      "jmp .loop\n"  ^^ 
                                      ".endloop:\n") in

    let extEnv envSize paramSize label =  Printf.sprintf (" mov rdi, (%d * 8)      ; array of 64 bit pointer lenght of 1 + |Env|\n" ^^
                                     "call malloc         ; rax -> ExtEnv \n" ^^    
                                     "mov rbx, env_ptr             ; rbx -> Env \n" ^^
                                     "; for var in Env: \n" ^^
                                      "%s\n" ^^
                                     "mov rbx, rax                 ; backup the pointer to ExtEnv \n" ^^
                                     "mov rdx, num_of_params       ; number of params in stack \n" ^^
                                    
                                     "lea rdi, [rdx * 8]           ; each place is stack is 8 byte long \n" ^^
                                     "BACKUP                       ; backup rbx, rcx, rdx and r8\n"  ^^
                                     "call malloc                  ; rax -> new param rib\n\n" ^^
                                     "RESTORE\n" ^^
                                     "mov [rbx], rax               ; ExtEnv[0] -> new param rib\n" ^^
                                     "mov rax, [rbx]                 ; rax -> ExtEnv[0]" ^^
                                     "\n; for param in stack:\n%s\n")
                                     (envSize + 1) (copyEnv envSize 0) (copy_param label) in

    let rec g e d ast_index = 
    match e with
    | ScmConst' (c) -> Printf.sprintf "mov rax, (const_tbl + %d)\n" (find_entry c consts)
    | ScmVar'(VarFree (v)) -> Printf.sprintf "mov rax, FVAR(%d)\n" (find_index_in_free_table fvars v)
    | ScmVar'(VarParam (_, minor)) -> Printf.sprintf "mov rax, PVAR(%d)\n" minor
    | ScmVar'(VarBound (_, major, minor)) -> Printf.sprintf ("mov rax, qword env_ptr\n" ^^
                                                            "mov rax, qword [rax + 8 * %d]\n" ^^
                                                            "mov rax, qword [rax + 8 * %d]\n") major minor
    | ScmBox'(VarParam(_, minor)) -> Printf.sprintf ("BACKUP\n" ^^
                                                              "mov rdi, 8     ; pointer to the box of the var\n" ^^
                                                              "call malloc\n" ^^
                                                              "mov rbx, PVAR(%d)\n" ^^
                                                              "mov [rax], rbx  ; rax -> box of param\n" ^^
                                                              "RESTORE\n") minor
    | ScmBoxGet'(v) -> Printf.sprintf "%s mov rax, qword[rax]\n" (g (ScmVar'(v)) d ast_index)
    | ScmBoxSet'(v, exp) -> Printf.sprintf ("%s\n" ^^
                                           "push rax\n" ^^
                                           "%s\n" ^^
                                           "pop qword [rax]\n" ^^
                                           "mov rax, (const_tbl)\n") (g exp d ast_index) (g (ScmVar'(v)) d ast_index)
    | ScmIf'(test, dit, dif) -> let label = Printf.sprintf "%d_%d" ast_index (inc_and_get()) in
                              Printf.sprintf (";start if\n%s\n" ^^
                                               "cmp rax, (const_tbl + 2)\n" ^^
                                               "je Lelse%s\n%s\n" ^^
                                               "jmp Lexit%s\n" ^^
                                               "Lelse%s:\n\t%s\n" ^^
                                               "Lexit%s:\n" )
                                               (g test d ast_index) label (g dit d ast_index) label label (g dif d ast_index) label
    | ScmSeq' list -> List.fold_left (fun code exp -> code ^ (g exp d ast_index) ^ "\n") "" list
    | ScmSet'(VarFree(v), exp) -> Printf.sprintf ("%s\n" ^^
                                                 "mov FVAR(%d), rax\n" ^^
                                                 "mov rax, (const_tbl)\n") (g exp d ast_index) (find_index_in_free_table fvars v)
    | ScmSet'(VarParam (_, minor), exp) -> Printf.sprintf ("%s\n" ^^
                                                          "mov qword PVAR(%d), rax\n" ^^
                                                          "mov rax, (const_tbl)\n") (g exp d ast_index) minor
    | ScmSet'(VarBound(v, major, minor), exp) -> Printf.sprintf ("%s\n" ^^
                                                                "mov rbx, qword env_ptr\n" ^^
                                                                "mov rbx, qword [rbx + 8 * %d]\n" ^^
                                                                "mov qword [rbx + 8 * %d], rax\n" ^^
                                                                "mov rax, (const_tbl)\n") (g exp d ast_index) major minor

    | ScmDef'(VarFree(v), exp) -> Printf.sprintf  ("%s\n" ^^
                                                 "mov FVAR(%d), rax\n" ^^
                                                 "mov rax, (const_tbl)\n") (g exp d ast_index) (find_index_in_free_table fvars v)

    | ScmOr' (list) -> let label = Printf.sprintf "%d_%d" ast_index (inc_and_get()) in
                       let first, last = rdc_rac list in
                       let first_code = List.fold_left (fun code exp -> code ^ (g exp d ast_index) ^ "cmp rax, (const_tbl + 2) \n jne Lexit" ^ label ^ "\n ") "" first in
                       let last_code = (g last d ast_index) ^ "Lexit" ^ label ^ ":\n" in
                       Printf.sprintf "%s" (first_code ^ last_code)
                     
    | ScmLambdaSimple'(args, body) -> let label = Printf.sprintf "%d_%d" ast_index  (inc_and_get()) in
                                    let closure = Printf.sprintf ("MAKE_CLOSURE(rax, rbx, Lcode%s) \n" ^^ 
                                                                   "jmp Lcont%s\n" ^^ 
                                                                   "Lcode%s: \n" ^^ 
                                                                   "\tpush rbp \n" ^^
                                                                   "\tmov rbp, rsp \n" ^^
                                                                   ";body start\n%s\n;body end\n" ^^
                                                                   "\tleave \n" ^^
                                                                   "\tret \n" ^^
                                                      "Lcont%s:") label label label (g body (d + 1) ast_index) label ^ "\n" in
                                      if d == -1 then ";New closure\n" ^ "mov rbx, SOB_NIL_ADDRESS\n" ^ closure
                                                 else ";New closure\n" ^ (extEnv d (List.length args) label) ^ closure
    | ScmLambdaOpt'(args, opt, body) -> let label = Printf.sprintf "%d_%d" ast_index  (inc_and_get()) in
                                    let fix_params = opt_to_list (List.length args) in
                                    let closure = Printf.sprintf ("MAKE_CLOSURE(rax, rbx, Lcode%s) \n" ^^ 
                                                                  "jmp Lcont%s\n" ^^ 
                                                                  "Lcode%s: \n" ^^ 
                                                                  "\tpush rbp \n" ^^
                                                                  "\tmov rbp, rsp \n" ^^
                                                                  "push qword num_of_params\n" ^^
                                                                   "%s\n" ^^
                                                                  ";body start\n%s\n;body end\n" ^^
                                                                  "pop rbx\n" ^^
                                                                  ";cmp rbx, num_of_params\n" ^^
                                                                  ";jge .args_fix             ; if there opt args then\n" ^^
                                                                  "dec qword num_of_params     ; add 1 to num_of_param so magic will be fixed\n" ^^
                                                                  ";.args_fix:\n" ^^
                                                                  "\tleave \n" ^^
                                                                  "\tret \n" ^^
                                                                  "Lcont%s:") label label label fix_params (g body (d + 1) ast_index) label ^ "\n" in
                                    if d == -1 then ";New closure\n" ^ "mov rbx, SOB_NIL_ADDRESS\n" ^ closure
                                    else ";New closure\n" ^ (extEnv d (List.length args) label) ^ closure

    

    | ScmApplic'(proc, args) -> let start = Printf.sprintf "\n;Start of applic\n" in
                                let magic = "push (const_tbl + 1)     ; placeholder for lambdaOpt nil\n" in
                                let length = (List.length args) in
                                let args_code = (List.fold_right (fun exp code -> code ^ (g exp d ast_index) ^ "push rax \n") args "") ^ (Printf.sprintf "push %d \n" length) in
                                let proc_code = (g proc d ast_index) in
                                let rest_code = Printf.sprintf ("inc rax\n" ^^
                                                               "push qword [rax] ;Push rax->env \n" ^^
                                                               "mov rax, qword [rax + 8]\n" ^^
                                                               "call rax ;Call rax->code \n" ^^
                                                               "add rsp , 8*1 \n" ^^
                                                               "pop rbx       ; number of args\n" ^^
                                                               "lea rsp , [rsp + 8*rbx] \n" ^^
                                                               "add rsp, 8 * 1\n" ^^
                                                               ";End of applic\n\n") in
                                start ^ magic ^ args_code ^ proc_code ^ rest_code     

    | ScmApplicTP'(proc, args) -> let start = Printf.sprintf "\n;Start of applic\n" in
                                let magic = "push (const_tbl + 1)     ; placeholder for lambdaOpt nil\n" in
                                let length = (List.length args) in
                                let args_code = (List.fold_right (fun exp code -> code ^ (g exp d ast_index) ^ "push rax \n") args "") ^ (Printf.sprintf "push %d \n" length) in
                                let proc_code = (g proc d ast_index) in
                                let rest_code = Printf.sprintf ("inc rax\n" ^^
                                                               "push qword [rax] ;Push rax->env \n" ^^
                                                               "mov rax, qword [rax + 8]\n" ^^
                                                               "call rax ;Call rax->code \n" ^^
                                                               "add rsp , 8*1 \n" ^^
                                                               "pop rbx       ; number of args\n" ^^
                                                               "lea rsp , [rsp + 8*rbx] \n" ^^
                                                               "add rsp, 8 * 1\n" ^^
                                                               ";End of applic\n\n") in
                                start ^ magic ^ args_code ^ proc_code ^ rest_code     
                                (* let start = Printf.sprintf "\n;Start of applic tail position\n" in
                                  let magic = "push (const_tbl + 1)     ; placeholder for lambdaOpt nil\n" in
                                  let length = (List.length args) in
                                  let args_code = (List.fold_right (fun exp code -> code ^ (g exp d ast_index) ^ "push rax \n") args "") ^ (Printf.sprintf "push %d \n" length) in
                                  let proc_code = (g proc d ast_index) in
                                  let rest_code = Printf.sprintf ("inc rax \n" ^^
                                                                 "mov rdx, num_of_params\n" ^^
                                                                 "add rdx, 5\n" ^^
                                                                 "shl rdx, 3\n" ^^
                                                                 "push qword [rax] ;Push rax->env \n" ^^
                                                                 "push qword [rbp + 8 * 1] ;old return address \n" ^^
                                                                 "SHIFT_FRAME %d ;Fixing the stack \n" ^^
                                                                 "add rsp, rdx\n" ^^
                                                                 "mov rax, qword [rax + 8] \n" ^^
                                                                 "jmp rax ;Jump to rax->code \n " ^^
                                                                 ";End of applic tail position\n\n") (5 + length)in
                                  start ^ magic ^ args_code ^ proc_code ^ rest_code *)
    
    | _ -> "; ** Unmatched expr **" in

    (g expr (-1) 0) (*depth for the size of the lexical env *)
        
end;;

