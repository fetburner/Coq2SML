(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s Production of Sml syntax. *)

open Pp
open Util
open Names
open Nameops
open Libnames
open Table
open Miniml
open Mlutil
open Modutil
open Common
open Declarations


(*s Some utility functions. *)

let pp_tvar id =
  let s = string_of_id id in
  if String.length s < 2 || s.[1]<>'\''
  then str ("'"^s)
  else str ("' "^s)

let pp_abst = function
  | [] -> mt ()
  | l  ->
      str "fn " ++ prlist_with_sep (fun () -> str " => fn ") pr_id l ++
      str " =>" ++ spc ()

let pp_parameters l =
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

let pp_string_parameters l =
  (pp_boxed_tuple str l ++ space_if (l<>[]))

let pp_letin pat def body =
  let fstline = str "let val " ++ pat ++ str " =" ++ spc () ++ def in
  hv 0 (hv 0 (hov 2 fstline ++ spc () ++ str "in") ++ spc () ++ hov 0 body ++ spc () ++ str "end")

(*s Sml renaming issues. *)

let keywords =
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "abstype"; "and"; "andalso"; "as"; "case"; "datatype"; "do";
    "else"; "end"; "exception"; "div"; "fn"; "fun"; "bandle"; "if";
    "in"; "infix"; "infixr"; "let"; "local"; "nonfix"; "of";
    "op"; "open"; "orelse"; "raise"; "rec"; "sig"; "then";
    "type"; "val"; "with"; "withtype"; "while"; "o"; "_"; "coq___" ]
  Idset.empty

let pp_open mp = str ("open "^ string_of_modfile mp ^"\n")

let preamble _ used_modules usf =
  prlist pp_open used_modules ++
  (if used_modules = [] then mt () else fnl ()) ++
  (if usf.tdummy || usf.tunknown then str "type coq___ = unit\n" else mt()) ++
  (if usf.mldummy then
    str "val coq___ = ()\n"
   else mt ()) ++
  (if usf.tdummy || usf.tunknown || usf.mldummy then fnl () else mt ())

let sig_preamble _ used_modules usf =
  str "_require \"basis.smi\"\n\n" ++
  prlist pp_open used_modules ++
  (if used_modules = [] then mt () else fnl ()) ++
  (if usf.tdummy || usf.tunknown then str "type coq___ = unit\n" else mt())

(*s The pretty-printer for Sml syntax*)

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

let str_global k r =
  if is_inline_custom r then find_custom r else Common.pp_global k r

let pp_global k r = str (str_global k r)

let pp_modname mp = str (Common.pp_module mp)

let is_infix r =
  is_inline_custom r &&
  (let s = find_custom r in
   let l = String.length s in
   l >= 2 && s.[0] = '(' && s.[l-1] = ')')

let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)

let get_ind = function
  | IndRef _ as r -> r
  | ConstructRef (ind,_) -> IndRef ind
  | _ -> assert false

let pp_one_field r i = function
  | Some r -> pp_global Term r
  | None -> pp_global Type (get_ind r) ++ str "coq___" ++ int i

let pp_field r fields i = pp_one_field r i (List.nth fields i)

let pp_fields r fields = list_map_i (pp_one_field r) 0 fields

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_tvar (List.nth vl (pred i))
                 with e when Errors.noncritical e ->
                   (str "'a" ++ int i))
    | Tglob (r,[a1;a2]) when is_infix r ->
        pp_par par (pp_rec true a1 ++ str (get_infix r) ++ pp_rec true a2)
    | Tglob (r,[]) -> pp_global Type r
    | Tglob (IndRef(kn,0),l)
        when not (keep_singleton ()) && kn = mk_ind "Coq.Init.Specif" "sig" ->
        pp_tuple_light pp_rec l
    | Tglob (r,l) ->
        pp_tuple_light pp_rec l ++ spc () ++ pp_global Type r
    | Tarr (t1,t2) ->
        pp_par par
          (pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ pp_rec false t2)
    | Tdummy _ -> str "coq___"
    | Tunknown -> str "coq___"
  in
  hov 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let is_bool_patt p s =
  try
    let r = match p with
      | Pusual r -> r
      | Pcons (r,[]) -> r
      | _ -> raise Not_found
    in
    find_custom r = s
  with Not_found -> false


let is_ifthenelse = function
  | [|([],p1,_);([],p2,_)|] -> is_bool_patt p1 "true" && is_bool_patt p2 "false"
  | _ -> false

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase (_,_,[|_|]) -> false
  | MLcase (_,_,pv) -> not (is_ifthenelse pv)
  | _        -> false

let rec pp_expr par env args =
  let apply st = pp_apply st par args
  and apply2 st = pp_apply2 st par args in
  function
    | MLrel n ->
        let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
        let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a ->
              let fl,a' = collect_lams a in
        let fl = List.map id_of_mlid fl in
        let fl,env' = push_vars fl env in
        let st = pp_abst (List.rev fl) ++ pp_expr false env' [] a' in
        apply2 st
    | MLletin (id,a1,a2) ->
        let i,env' = push_vars [id_of_mlid id] env in
        let pp_id = pr_id (List.hd i)
        and pp_a1 = pp_expr false env [] a1
        and pp_a2 = pp_expr (not par && expr_needs_par a2) env' [] a2 in
        hv 0 (apply2 (pp_letin pp_id pp_a1 pp_a2))
    | MLglob r ->
        (try
           let args = list_skipn (projection_arity r) args in
           let record = List.hd args in
     pp_apply (pp_apply (str "#" ++ pp_global Term r) par [record]) par (List.tl args)
         with e when Errors.noncritical e -> apply (pp_global Term r))
    | MLfix (i,ids,defs) ->
        let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
        pp_fix par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
        (* An [MLexn] may be applied, but I don't really care. *)
        pp_par par (str ("raise (Fail \""^s^"\")") ++ spc () ++ str ("(* "^s^" *)"))
    | MLdummy ->
        str "coq___" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
        pp_apply (str "Unsafe.cast") par (pp_expr true env [] a :: args)
    | MLaxiom ->
        pp_par par (str "failwith \"AXIOM TO BE REALIZED\"")
    | MLcons (_,r,a) as c ->
        assert (args=[]);
        begin match a with
          | _ when is_native_char c -> pp_native_char c
          | [a1;a2] when is_infix r ->
            let pp = pp_expr true env [] in
            pp_par par (pp a1 ++ str (get_infix r) ++ pp a2)
          | _ when is_coinductive r ->
            let ne = (a<>[]) in
            let tuple = space_if ne ++ pp_tuple (pp_expr true env []) a in
            pp_par par (str "lazy " ++ pp_par ne (pp_global Cons r ++ tuple))
          | [] -> pp_global Cons r
          | _ ->
            let fds = get_record_fields r in
            if fds <> [] then
              pp_record_pat (pp_fields r fds, List.map (pp_expr true env []) a)
            else
              let tuple = pp_tuple (pp_expr true env []) a in
              if str_global Cons r = "" (* hack Extract Inductive prod *)
              then tuple
              else pp_par par (pp_global Cons r ++ spc () ++ tuple)
        end
    | MLtuple l ->
        assert (args = []);
        pp_boxed_tuple (pp_expr true env []) l
    | MLcase (_, t, pv) when is_custom_match pv ->
        if not (is_regular_match pv) then
          error "Cannot mix yet user-given match and general patterns.";
        let mkfun (ids,_,e) =
          if ids <> [] then named_lams (List.rev ids) e
          else dummy_lams (ast_lift 1 e) 1
        in
        let pp_branch tr = pp_expr true env [] (mkfun tr) ++ fnl () in
        let inner =
          str (find_custom_match pv) ++ fnl () ++
          prvect pp_branch pv ++
          pp_expr true env [] t
        in
        apply2 (hov 2 inner)
    | MLcase (typ, t, pv) ->
        let head =
          if not (is_coinductive_type typ) then pp_expr false env [] t
          else (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
        in
        (* First, can this match be printed as a mere record projection ? *)
        (try pp_record_proj par env typ t pv args
         with Impossible ->
           (* Second, can this match be printed as a let-in ? *)
           if Array.length pv = 1 then
             let s1,s2 = pp_one_pat env pv.(0) in
             hv 0 (apply2 (pp_letin s1 head s2))
           else
             (* Third, can this match be printed as [if ... then ... else] ? *)
             (try apply2 (pp_ifthenelse env head pv)
              with Not_found ->
                (* Otherwise, standard match *)
                apply2
                  (v 0 (str "case " ++ head ++ str " of" ++ fnl () ++
                        pp_pat env pv))))

and pp_record_proj par env typ t pv args =
  (* Can a match be printed as a mere record projection ? *)
  let fields = record_fields_of_type typ in
  if fields = [] then raise Impossible;
  if Array.length pv <> 1 then raise Impossible;
  if has_deep_pattern pv then raise Impossible;
  let (ids,pat,body) = pv.(0) in
  let n = List.length ids in
  let no_patvar a = not (List.exists (ast_occurs_itvl 1 n) a) in
  let rel_i,a = match body with
    | MLrel i when i <= n -> i,[]
    | MLapp(MLrel i, a) when i<=n && no_patvar a -> i,a
    | _ -> raise Impossible
  in
  let rec lookup_rel i idx = function
    | Prel j :: l -> if i = j then idx else lookup_rel i (idx+1) l
    | Pwild :: l -> lookup_rel i (idx+1) l
    | _ -> raise Impossible
  in
  let r,idx = match pat with
    | Pusual r -> r, n-rel_i
    | Pcons (r,l) -> r, lookup_rel rel_i 0 l
    | _ -> raise Impossible
  in
  if is_infix r then raise Impossible;
  let env' = snd (push_vars (List.rev_map id_of_mlid ids) env) in
  let pp_args = (List.map (pp_expr true env' []) a) @ args in
  let pp_head = str "#" ++ pp_field r fields idx ++ str " " ++ pp_expr true env [] t
  in
  pp_apply pp_head par pp_args

and pp_record_pat (fields, args) =
   str "{ " ++
   prlist_with_sep (fun () -> str "," ++ spc ())
     (fun (f,a) -> f ++ str " =" ++ spc () ++ a)
     (List.combine fields args) ++
   str " }"

and pp_cons_pat r ppl =
  if is_infix r && List.length ppl = 2 then
    List.hd ppl ++ str (get_infix r) ++ List.hd (List.tl ppl)
  else
    let fields = get_record_fields r in
    if fields <> [] then pp_record_pat (pp_fields r fields, ppl)
    else if str_global Cons r = "" then
      pp_boxed_tuple identity ppl (* Hack Extract Inductive prod *)
    else
      pp_global Cons r ++ space_if (ppl<>[]) ++ pp_boxed_tuple identity ppl

and pp_gen_pat ids env = function
  | Pcons (r, l) -> pp_cons_pat r (List.map (pp_gen_pat ids env) l)
  | Pusual r -> pp_cons_pat r (List.map pr_id ids)
  | Ptuple l -> pp_boxed_tuple (pp_gen_pat ids env) l
  | Pwild -> str "_"
  | Prel n -> pr_id (get_db_name n env)

and pp_ifthenelse env expr pv = match pv with
  | [|([],tru,the);([],fal,els)|] when
      (is_bool_patt tru "true") && (is_bool_patt fal "false")
      ->
      hv 0 (hov 2 (str "if " ++ expr) ++ spc () ++
            hov 2 (str "then " ++
                   hov 2 (pp_expr (expr_needs_par the) env [] the)) ++ spc () ++
            hov 2 (str "else " ++
                   hov 2 (pp_expr (expr_needs_par els) env [] els)))
  | _ -> raise Not_found

and pp_one_pat env (ids,p,t) =
  let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
  pp_gen_pat (List.rev ids') env' p,
  pp_expr (expr_needs_par t) env' [] t

and pp_pat env pv =
  prvecti
    (fun i x ->
       let s1,s2 = pp_one_pat env x in
       hv 2 (hov 4 ((if i = 0 then str "  " else str "| ") ++ s1 ++ str " =>") ++ spc () ++ hov 2 s2) ++
       if i = Array.length pv - 1 then mt () else fnl ())
    pv

and pp_function env t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
          (List.length bl <> 0, pr_binding (List.rev bl) ++
          str " =" ++ fnl () ++ str "  " ++
          hov 2 (pp_expr false env' [] t'))

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env i (ids,bl) args =
  pp_par par
    (v 0 (str "let fun " ++
          prvect_with_sep
                  (fun () -> fnl () ++ str "and ")
            (fun (fi,ti) -> pr_id fi ++ snd (pp_function env ti))
            (array_map2 (fun id b -> (id,b)) ids bl) ++
          fnl () ++
    hov 2 (str "in " ++ pp_apply (pr_id ids.(i)) false args ++ str " end ")))

let pp_val e typ =
  hov 4 (str "(** val " ++ e ++ str " :" ++ spc () ++ pp_type false [] typ ++
  str " **)")  ++ fnl2 ()

(*s Pretty-printing of [Dfix] *)

let pp_Dfix (rv,c,t) =
  let names = Array.map
    (fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
  in
  let rec pp init i =
    if i >= Array.length rv then
      (if init then failwith "empty phrase" else mt ())
    else
      let void = is_inline_custom rv.(i) ||
        (not (is_custom rv.(i)) && c.(i) = MLexn "UNUSED")
      in
      if void then pp init (i+1)
      else
        let (isfun, def) =
          if is_custom rv.(i) then (false, str " = " ++ str (find_custom rv.(i)))
          else pp_function (empty_env ()) c.(i)
        in
        (if init then mt () else fnl2 ()) ++
        pp_val names.(i) t.(i) ++
        str
    (if init then
       if isfun then "fun "
       else "val "
     else "and ") ++ names.(i) ++ def ++
        pp false (i+1)
  in pp true 0

(*s Pretty-printing of inductive types declaration. *)

let pp_equiv param_list name = function
  | NoEquiv, _ -> mt (), false
  | Equiv kn, i ->
      str " = datatype " ++ pp_parameters param_list ++ pp_global Type (IndRef (mind_of_kn kn,i)), true
  | RenEquiv ren, _  ->
      str " = datatype " ++ pp_parameters param_list ++ str (ren^".") ++ name, true

let pp_comment s = str "(* " ++ s ++ str " *)"

let pp_one_ind prefix ip_equiv pl name cnames ctyps =
  let pl = rename_tvars keywords pl in
  let pp_constructor i typs =
    (if i=0 then mt () else fnl ()) ++
    hov 3 ((if i = 0 then str "  " else str "| ") ++ cnames.(i) ++
           (if typs = [] then mt () else str " of ") ++
           prlist_with_sep
            (fun () -> spc () ++ str "* ") (pp_type true pl) typs)
  in
  let pp_eq, is_rep = pp_equiv pl name ip_equiv in
  pp_parameters pl ++ str prefix ++ name ++
  pp_eq ++ if is_rep then mt () else str " =" ++
  if Array.length ctyps = 0 then str " unit (* empty inductive *)"
  else fnl () ++ v 0 (prvecti pp_constructor ctyps)

let pp_logical_ind packet =
  pp_comment (pr_id packet.ip_typename ++ str " : logical inductive") ++
  fnl () ++
  pp_comment (str "with constructors : " ++
              prvect_with_sep spc pr_id packet.ip_consnames) ++
  fnl ()

let pp_singleton kn packet =
  let name = pp_global Type (IndRef (kn,0)) in
  let l = rename_tvars keywords packet.ip_vars in
  hov 2 (str "type " ++ pp_parameters l ++ name ++ str " =" ++ spc () ++
         pp_type false l (List.hd packet.ip_types.(0)) ++ fnl () ++
         pp_comment (str "singleton inductive, whose constructor was " ++
                     pr_id packet.ip_consnames.(0)))

let pp_record kn fields ip_equiv packet =
  let ind = IndRef (kn,0) in
  let name = pp_global Type ind in
  let fieldnames = pp_fields ind fields in
  let l = List.combine fieldnames packet.ip_types.(0) in
  let pl = rename_tvars keywords packet.ip_vars in
  let pp_eq, is_rep = pp_equiv pl name ip_equiv in
  str "type " ++ pp_parameters pl ++ name ++
  pp_eq ++ if is_rep then mt () else str " = { "++
  hov 0 (prlist_with_sep (fun () -> str "," ++ spc ())
           (fun (p,t) -> p ++ str " : " ++ pp_type true pl t) l)
  ++ str " }"

let pp_coind pl name =
  let pl = rename_tvars keywords pl in
  pp_parameters pl ++ name ++ str " = " ++
  pp_parameters pl ++ str "coq___" ++ name ++ str " Lazy.t" ++
  fnl() ++ str "and "

let pp_ind co kn ind =
  let prefix = if co then "coq___" else "" in
  let some = ref false in
  let init= ref (str "datatype ") in
  let names =
    Array.mapi (fun i p -> if p.ip_logical then mt () else
                  pp_global Type (IndRef (kn,i)))
      ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p -> if p.ip_logical then [||] else
         Array.mapi (fun j _ -> pp_global Cons (ConstructRef ((kn,i),j+1)))
           p.ip_types)
      ind.ind_packets
  in
  let rec pp i =
    if i >= Array.length ind.ind_packets then mt ()
    else
      let ip = (kn,i) in
      let ip_equiv = ind.ind_equiv, i in
      let p = ind.ind_packets.(i) in
      if is_custom (IndRef ip) then pp (i+1)
      else begin
        some := true;
        if p.ip_logical then pp_logical_ind p ++ pp (i+1)
        else
          let s = !init in
          begin
            init := (fnl () ++ str "and ");
            s ++
            (if co then pp_coind p.ip_vars names.(i) else mt ()) ++
            pp_one_ind
              prefix ip_equiv p.ip_vars names.(i) cnames.(i) p.ip_types ++
            pp (i+1)
          end
      end
  in
  let st = pp 0 in if !some then st else failwith "empty phrase"


(*s Pretty-printing of a declaration. *)

let pp_mind kn i =
  match i.ind_kind with
    | Singleton -> pp_singleton kn i.ind_packets.(0)
    | Coinductive -> pp_ind true kn i
    | Record fields -> pp_record kn fields (i.ind_equiv,0) i.ind_packets.(0)
    | Standard -> pp_ind false kn i

let pp_decl = function
    | Dtype (r,_,_) when is_inline_custom r -> failwith "empty phrase"
    | Dterm (r,_,_) when is_inline_custom r -> failwith "empty phrase"
    | Dind (kn,i) -> pp_mind kn i
    | Dtype (r, l, t) ->
        let name = pp_global Type r in
        let l = rename_tvars keywords l in
        let ids, def =
          try
            let ids,s = find_type_custom r in
            pp_string_parameters ids, str "=" ++ spc () ++ str s
          with Not_found ->
            pp_parameters l,
            if t = Taxiom then str "(* AXIOM TO BE REALIZED *)"
            else str "=" ++ spc () ++ pp_type false l t
        in
        hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)
    | Dterm (r, a, t) ->
        let (isfun, def) =
          if is_custom r then (false, str (" = " ^ find_custom r))
          else if is_projection r then
            (false, (prvect str (Array.make (projection_arity r) " _")) ++
      str " : " ++ pp_type false [] t ++ str " = fn x => #")
          else pp_function (empty_env ()) a
        in
        let name = pp_global Term r in
        let postdef = if is_projection r then name ++ str " x" else mt () in
        pp_val name t ++ hov 0 (str (if isfun then "fun " else "val ") ++ name ++ def ++ postdef)
    | Dfix (rv,defs,typs) ->
        pp_Dfix (rv,defs,typs)

let pp_alias_decl ren = function
  | Dind (kn,i) -> pp_mind kn { i with ind_equiv = RenEquiv ren }
  | Dtype (r, l, _) ->
      let name = pp_global Type r in
      let l = rename_tvars keywords l in
      let ids = pp_parameters l in
      hov 2 (str "type " ++ ids ++ name ++ str " =" ++ spc () ++ ids ++
             str (ren^".") ++ name)
  | Dterm (r, a, t) ->
      let name = pp_global Term r in
      hov 2 (str "val " ++ name ++ str (" = "^ren^".") ++ name)
  | Dfix (rv, _, _) ->
      prvecti (fun i r -> if is_inline_custom r then mt () else
                 let name = pp_global Term r in
                 hov 2 (str "val " ++ name ++ str (" = "^ren^".") ++ name) ++
                 fnl ())
        rv

let pp_spec = function
  | Sval (r,_) when is_inline_custom r -> failwith "empty phrase"
  | Stype (r,_,_) when is_inline_custom r -> failwith "empty phrase"
  | Sind (kn,i) -> pp_mind kn i
  | Sval (r,t) ->
      let def = pp_type false [] t in
      let name = pp_global Term r in
      hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) ->
      let name = pp_global Type r in
      let l = rename_tvars keywords vl in
      let ids, def =
        try
          let ids, s = find_type_custom r in
          pp_string_parameters ids,  str "= " ++ str s
        with Not_found ->
          let ids = pp_parameters l in
          match ot with
            | None -> ids, mt ()
            | Some Taxiom -> ids, str "(* AXIOM TO BE REALIZED *)"
            | Some t -> ids, str "=" ++ spc () ++ pp_type false l t
      in
      hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)

let pp_alias_spec ren = function
  | Sind (kn,i) -> pp_mind kn { i with ind_equiv = RenEquiv ren }
  | Stype (r,l,_) ->
      let name = pp_global Type r in
      let l = rename_tvars keywords l in
      let ids = pp_parameters l in
      hov 2 (str "datatype " ++ ids ++ name ++ str " =" ++ spc () ++ ids ++
             str (ren^".") ++ name)
  | Sval _ -> assert false

let rec pp_specif = function
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) ->
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         hov 1 (str ("structure "^ren^" = struct ") ++ fnl () ++ pp_spec s) ++
         fnl () ++ str "end" ++ fnl () ++
         pp_alias_spec ren s
       with Not_found -> pp_spec s)
  | (l,Smodule mt) ->
      let def = pp_module_type [] mt in
      let def' = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "signature " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ hov 1 (str ("sig "^ren^" = ") ++ fnl () ++ def')
       with Not_found -> Pp.mt ())
  | (l,Smodtype mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "signature " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ str ("signature "^ren^" = ") ++ name
       with Not_found -> Pp.mt ())

and pp_module_type params = function
  | MTident kn ->
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      let typ = pp_module_type [] mt in
      let name = pp_modname (MPbound mbid) in
      let def = pp_module_type (MPbound mbid :: params) mt' in
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MTsig (mp, sign) ->
      push_visible mp params;
      let l = map_succeed pp_specif sign in
      pop_visible ();
      str "sig " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
        fnl () ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let ids = pp_parameters (rename_tvars keywords vl) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = list_sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot(mp,label_of_id l)) mp_mt idl'
      in
      let r = ConstRef (make_con mp_w empty_dirpath (label_of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_type false vl typ
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
        List.fold_left (fun mp id -> MPdot(mp,label_of_id id)) mp_mt idl
      in
      push_visible mp_mt [];
      let pp_w = str " and " ++ pp_modname mp_w in
      pop_visible ();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_modname mp

let is_short = function MEident _ | MEapply _ -> true | _ -> false

let rec collect_functors = function
  | MEfunctor (mbid, mt, me) ->
      let args, me' = collect_functors me in
      ((mbid, mt) :: args, me')
  | me -> [], me

let rec pp_structure_elem = function
  | (l,SEdecl d) ->
       (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         hov 1 (str ("structure "^ren^" = struct ") ++ fnl () ++ pp_decl d) ++
         fnl () ++ str "end" ++ fnl () ++
         pp_alias_decl ren d
        with Not_found -> pp_decl d)
  | (l,SEmodule m) ->
      let typ =
        (* virtual printing of the type, in order to have a correct mli later*)
        if Common.get_phase () = Pre then
          str ": " ++ pp_module_type [] m.ml_mod_type
        else mt ()
      in
      let args, me = collect_functors m.ml_mod_expr in
      let def = pp_module_expr [] me in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      let prefix = if args = [] then "structure " else "functor " in
      hov 1
      (str prefix ++ name ++ fnl () ++ pp_meargs args ++ typ ++ str " = " ++
       (if is_short me then mt () else fnl ()) ++ def) ++
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ str ("structure "^ren^" = ") ++ name
       with Not_found -> mt ())
  | (l,SEmodtype m) ->
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "signature " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ str ("signature "^ren^" = ") ++ name
       with Not_found -> mt ())

and pp_meargs args =
  let pp_functor (mbid, mt) =
    let name = pp_modname (MPbound mbid) in
    let typ = pp_module_type [] mt in
    str "(" ++ name ++ str ":" ++ typ ++ str ")" ++ fnl () in
  List.fold_left ( ++ ) (mt ())
    (List.map pp_functor args)

and pp_module_expr params = function
  | MEident mp -> pp_modname mp
  | MEapply (me, me') ->
      pp_module_expr [] me ++ str "(" ++ pp_module_expr [] me' ++ str ")"
  | MEfunctor (mbid, mt, me) -> failwith "pp_module_expr"
  | MEstruct (mp, sel) ->
      push_visible mp params;
      let l = map_succeed pp_structure_elem sel in
      pop_visible ();
      str "struct " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
      fnl () ++ str "end"

let do_struct f s =
  let pp s = try f s ++ fnl2 () with Failure "empty phrase" -> mt ()
  in
  let ppl (mp,sel) =
    push_visible mp [];
    let p = prlist_strict pp sel in
    (* for monolithic extraction, we try to simulate the unavailability
       of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_strict ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  p

let pp_struct s = do_struct pp_structure_elem s

let push_module_type, get_module_type =
  let env = ref [] in
  ((fun l mt -> env := (MPdot (top_visible_mp (), l), mt) :: !env),
   (fun kn -> List.assoc kn !env))

let rec collect_funsigs = function
  | MTfunsig (mbid, mt, mt') ->
      let (args, modtype) = collect_funsigs mt' in
      ((mbid, mt) :: args, modtype)
  | mt -> ([], mt)

let rec pp_specif' = function
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) ->
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         hov 1 (str ("structure "^ren^" = struct ") ++ fnl () ++ pp_spec s) ++
         fnl () ++ str "end" ++ fnl () ++
         pp_alias_spec ren s
       with Not_found -> pp_spec s)
  | (l,Smodule mt) ->
      let args, mt' = collect_funsigs mt in
      let def = pp_module_type' [] mt' in
      let def' = pp_module_type' [] mt' in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      let prefix = if args = [] then "structure " else "functor " in
      hov 1 (str prefix ++ name ++ fnl () ++ pp_mtargs args ++ str " = " ++ def) ++
      (try
         let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ hov 1 (str (prefix ^ ren) ++ pp_mtargs args ++ str " = " ++ def')
       with Not_found -> Pp.mt ())
  | (l,Smodtype mt) -> push_module_type l mt; Pp.mt ()

and pp_mtargs args =
  let pp_funsig (mbid, mt) =
    let typ = pp_module_type'' [] mt in
    let name = pp_modname (MPbound mbid) in
    str "(" ++ name ++ str ":" ++ typ ++ str ")" ++ fnl () in
  List.fold_left ( ++ ) (mt ()) (List.map pp_funsig args)

and pp_module_type' params = function
  | MTident kn ->
      pp_module_type' [] (get_module_type kn)
  | MTfunsig (mbid, mt, mt') -> failwith "pp_module_type'"
  | MTsig (mp, sign) ->
      push_visible mp params;
      let l = map_succeed pp_specif' sign in
      pop_visible ();
      str "struct " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
        fnl () ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let ids = pp_parameters (rename_tvars keywords vl) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = list_sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot(mp,label_of_id l)) mp_mt idl'
      in
      let r = ConstRef (make_con mp_w empty_dirpath (label_of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type' [] mt ++ pp_w ++ str " = " ++ pp_type false vl typ
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
        List.fold_left (fun mp id -> MPdot(mp,label_of_id id)) mp_mt idl
      in
      push_visible mp_mt [];
      let pp_w = str " and " ++ pp_modname mp_w in
      pop_visible ();
      pp_module_type' [] mt ++ pp_w ++ str " = " ++ pp_modname mp

and pp_module_type'' params = function
  | MTident kn ->
      pp_module_type'' [] (get_module_type kn)
  | MTfunsig (mbid, mt, mt') -> failwith "pp_module_type''"
  | MTsig (mp, sign) ->
      push_visible mp params;
      let l = map_succeed pp_specif sign in
      pop_visible ();
      str "sig " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
        fnl () ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let ids = pp_parameters (rename_tvars keywords vl) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = list_sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot(mp,label_of_id l)) mp_mt idl'
      in
      let r = ConstRef (make_con mp_w empty_dirpath (label_of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type'' [] mt ++ pp_w ++ str " = " ++ pp_type false vl typ
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
        List.fold_left (fun mp id -> MPdot(mp,label_of_id id)) mp_mt idl
      in
      push_visible mp_mt [];
      let pp_w = str " and " ++ pp_modname mp_w in
      pop_visible ();
      pp_module_type'' [] mt ++ pp_w ++ str " = " ++ pp_modname mp

let pp_signature s = do_struct pp_specif' s

let pp_decl d = try pp_decl d with Failure "empty phrase" -> mt ()

let sml_descr = {
  keywords = keywords;
  file_suffix = ".sml";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = Some ".smi";
  sig_preamble = sig_preamble;
  pp_sig = pp_signature;
  pp_decl = pp_decl;
}


