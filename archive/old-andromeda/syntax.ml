(** Annotated abstract syntax for Andromedan type theory. *)

type name = string

type label = string (* field label *)

let anonymous = Input.anonymous

(** We use de Bruijn indices *)
type variable = Common.debruijn

type ty = ty' * Position.t
and ty' =
  | Type
  | El of term
  | RecordTy of (label * (name * ty)) list
  | Prod of name * ty * ty

and term = term' * Position.t
and term' =
  | Var of variable
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Spine of variable * ty * term list
  | Record of (label * (name * ty * term)) list
  | Project of term * (label * (name * ty)) list * label

(* Helper functions for construction *)

let mkType ?(loc=Position.nowhere) u = Type u, loc
let mkEl ?(loc=Position.nowhere) u e = El (u,e), loc
let mkRecordTy ?(loc=Position.nowhere) lst = RecordTy lst, loc
let mkProd ?(loc=Position.nowhere) x t1 t2 = Prod (x,t1,t2), loc
let mkId  ?(loc=Position.nowhere) t e1 e2 = Id (t,e1,e2), loc

let mkVar ?(loc=Position.nowhere) v = Var v, loc
let mkEquation ?(loc=Position.nowhere) e1 t e2 = Equation(e1,t,e2), loc
let mkRewrite ?(loc=Position.nowhere) e1 t e2 = Rewrite(e1,t,e2), loc
let mkAscribe ?(loc=Position.nowhere) e t = Ascribe(e,t), loc
let mkLambda ?(loc=Position.nowhere) x t1 t2 e = Lambda(x,t1,t2,e), loc
let mkSpine ?(loc=Position.nowhere) f fty es = Spine (f, fty, es), loc
let mkRecord ?(loc=Position.nowhere) lst = Record lst, loc
let mkProject ?(loc=Position.nowhere) e t lbl = Project (e, t, lbl), loc
let mkRefl ?(loc=Position.nowhere) t e = Refl(t,e), loc
let mkNameType ?(loc=Position.nowhere) () = NameType, loc
let mkNameRecordTy ?(loc=Position.nowhere) lst = NameRecordTy lst, loc
let mkNameProd ?(loc=Position.nowhere) u1 u2 x e1 e2 = NameProd(u1, u2, x, e1, e2), loc
let mkNameType ?(loc=Position.nowhere) u = NameType u, loc
let mkNameId ?(loc=Position.nowhere) u e1 e2 e3 = NameId(u,e1,e2,e3), loc


(* XXX. Technically, we ought to check that the application isn't at a "weird" type
 * before we assume it can be a spine.
 *)
let mkApp ?(loc=Position.nowhere) x t1 t2 e1 e2 =
  match fst e1 with
  | Var v              -> Spine (v, mkProd ~loc x t1 t2, [e2]), loc
  | Spine (f, fty, es) -> Spine (f, fty, es @ [e2]), loc
  | _                  -> App((x,t1,t2),e1,e2), loc


(*********************)
(* Alpha equality    *)
(*********************)

(** If [equal term1 term2] returns true, then the terms are identical modulo
    names of bound variables (and the presence/absence of hints). Moreover,
    if one is well-typed, then so is the other and they are equivalent.

    We don't use ML's built-in [=] operator for alpha equality,
    because we maintain variable names and source locations (for debugging and
    error-reporting) in terms, and want to ignore names of bound variables,
    and we ignore the hints.

    We do ignore equation and rewrite hints, because they should be thought
    of as (theoretically optional) guidance for the algorithm, rather than
    being officially part of the language.

    We do not ignore all magenta annotations, because two terms can be
    equal in all their non-magenta parts yet not be interchangeable because they
    have different types.

    E.g., if  T -> U == T -> V  (without U == V)
              f : T -> U
              t : T
          then
              f @[T->U] t : U
          but
              f @[T->V] t : V

    Further, we want this equality to respect equality, and if
              (x:nat) -> U(x)  ==  nat -> U(0)
              f : (x:nat) -> U(x)
    then
              f @[x:nat.U(x)] 0 : U(0)
              f @[s:nat.U(0)] 0 : U(0)
    have the same non-magenta terms and even the same type, but
    but we cannot prove in general that these terms are equal because
    the congruence-of-application rule doesn't apply (because the
    two Pi types involved are not *componentwise* equal).
*)

let rec equal ((left',_) as left) ((right',_) as right) =
  match left', right' with

  | Var index1, Var index2 -> index1 = index2

  | Equation(_, _, term1), _ -> equal term1 right
  | _, Equation(_, _, term1) -> equal left  term1

  | Rewrite(_, _, term1), _ -> equal term1 right
  | _, Rewrite(_, _, term1) -> equal left  term1

  | NameProd(universe1, universe2, _, term3, term4),
    NameProd(universe5, universe6, _, term7, term8) ->
         Universe.eq universe1 universe5
      && Universe.eq universe2 universe6
      && equal term3 term7
      && equal term4 term8

  | Ascribe(term1, ty2), Ascribe(term3, ty4) ->
         equal_ty ty2 ty4
      && equal term1 term3

  | Lambda(_, ty1, ty2, term3), Lambda(_, ty4, ty5, term6) ->
         equal_ty ty1 ty4
      && equal_ty ty2 ty5
      && equal term3 term6

  | App((_,ty1,ty2),term3,term4), App((_,ty5,ty6),term7,term8) ->
         equal_ty ty1 ty5
      && equal_ty ty2 ty6
      && equal term3 term7
      && equal term4 term8

  | Spine (f1, fty1, es1), Spine (f2, fty2, es2) ->
         f1 = f2
      && equal_ty fty1 fty2
      && List.for_all2 equal es1 es2

  | Record lst1, Record lst2 ->
    List.length lst1 = List.length lst2 &&
    List.for_all2
     (fun (lbl1,(_,t1,e1)) (lbl2,(_,t2,e2)) ->
       lbl1 = lbl2 && equal_ty t1 t2 && equal e1 e2)
     lst1 lst2

  | Project (e1, lst1, lbl1), Project (e2, lst2, lbl2) ->
    lbl1 = lbl2 &&
    List.length lst1 = List.length lst2 &&
    List.for_all2 (fun (lbl1,(_,t1)) (lbl2,(_,t2)) -> lbl1 = lbl2 && equal_ty t1 t2) lst1 lst2 &&
    equal e1 e2

  | UnitTerm, UnitTerm
  | NameUnit, NameUnit -> true

  | Idpath(ty2, term3), Idpath(ty5, term6)
  | Refl  (ty2, term3), Refl  (ty5, term6) ->
      equal_ty ty2 ty5
      && equal term3 term6

  | J(ty1, (_, _, _, ty2), (_, term3), term4, term5, term6),
    J(ty7, (_, _, _, ty8), (_, term9), term10, term11, term12) ->
         equal_ty ty1 ty7
      && equal_ty ty2 ty8
      && equal term3 term9
      && equal term4 term10
      && equal term5 term11
      && equal term6 term12

  | Coerce(universe1, universe2, term3), Coerce(universe4, universe5, term6) ->
         Universe.eq universe1 universe4
      && Universe.eq universe2 universe5
      && equal term3 term6

  | NameUniverse universe1, NameUniverse universe2 ->
      Universe.eq universe1 universe2

  | NameRecordTy lst1, NameRecordTy lst2 ->
    List.length lst1 = List.length lst2 &&
    List.for_all2
     (fun (lbl1,(_,u1,e1)) (lbl2,(_,u2,e2)) ->
       lbl1 = lbl2 && Universe.eq u1 u2 && equal e1 e2)
     lst1 lst2

  | NamePaths(universe1, term2, term3, term4), NamePaths(universe5, term6, term7, term8)
  | NameId   (universe1, term2, term3, term4), NameId   (universe5, term6, term7, term8) ->
         Universe.eq universe1 universe5
      && equal term2 term6
      && equal term3 term7
      && equal term4 term8

  | (Var _ | Ascribe _ | Lambda _
     | App _ | Spine _
     | Record _ | Project _
     | UnitTerm | Idpath _ | J _ | Refl _ | Coerce _ | NameRecordTy _
     | NameUnit | NameProd _ | NameUniverse _ | NamePaths _| NameId _), _ ->
         false


and equal_ty (left_ty,_) (right_ty,_) =
  match left_ty, right_ty with

  | Universe universe1, Universe universe2 ->
      Universe.eq universe1 universe2

  | El(universe1, term2), El(universe3, term4) ->
      Universe.eq universe1 universe3 && equal term2 term4

  | RecordTy lst1, RecordTy lst2 ->
    List.length lst1 = List.length lst2 &&
    List.for_all2
     (fun (lbl1,(_,t1)) (lbl2,(_,t2)) -> lbl1 = lbl2 && equal_ty t1 t2)
     lst1 lst2

  | Unit, Unit -> true

  | Prod(_, ty1, ty2), Prod(_, ty3, ty4) ->
      equal_ty ty1 ty3 && equal_ty ty2 ty4

  | Paths(ty1, term2, term3), Paths(ty4, term5, term6)
  | Id   (ty1, term2, term3), Id   (ty4, term5, term6) ->
      equal_ty ty1 ty4 && equal term2 term5 && equal term3 term6

  | (Universe _ | El _ | RecordTy _ | Unit | Prod _ | Paths _ | Id _), _ ->
      false

(*******************)
(* Transformations *)
(*******************)

(** Shifting and substitution are almost exactly the same code. We
   factor out this common pattern into [transform], which rewrites an
   expression by recursively traversing the term and then applying
   a generic transformation function [ftrans].

   [transform] recursively maintains a count [bvs], the number of bound variables whose
   scope we are in, and provides that count to [ftrans] along with the
   recursively transformed term.
*)
let rec transform ftrans bvs ((term', loc) as term) =
  (* Shorthand for recursive calls *)
  let recurse    = transform ftrans bvs in
  let recurse_ty = transform_ty ftrans bvs in
  (* Shorthand for recursive calls on terms/types that are
     inside n new binders *)
  let recurse_in_binders    n = transform    ftrans (bvs+n) in
  let recurse_ty_in_binders n = transform_ty ftrans (bvs+n) in

  ftrans bvs
    (match term' with

      | Var _index -> term

      | Equation(term1, ty2, term3) ->
          mkEquation ~loc (recurse term1) (recurse_ty ty2) (recurse term3)

      | Rewrite(term1, ty2, term3) ->
          mkRewrite ~loc (recurse term1) (recurse_ty ty2) (recurse term3)

      | Ascribe(term1, ty2)    ->
          mkAscribe ~loc (recurse term1) (recurse_ty ty2)

      | Lambda(name, ty1, ty2, term1) ->
          mkLambda ~loc name (recurse_ty ty1)
                   (recurse_ty_in_binders 1 ty2) (recurse_in_binders 1 term1)

      | App((name, ty1, ty2), term1, term2) ->
          mkApp ~loc name (recurse_ty ty1) (recurse_ty_in_binders 1 ty2)
                (recurse term1) (recurse term2)

      | Spine (f, fty, es) ->
          begin
            match recurse (mkVar f) with
            | Var f, _ -> mkSpine ~loc f (recurse_ty fty) (List.map recurse es)
            | _ -> recurse (from_spine f fty es)
          end

      | Record lst ->
        let rec fold k = function
          | [] -> []
          | (lbl,(x,t,e)) :: lst ->
            let t = recurse_ty_in_binders k t
            and e = recurse_in_binders k e
            in
              (lbl, (x, t, e)) :: fold (k+1) lst
        in
          mkRecord ~loc (fold 0 lst)

      | Project (e, lst, lbl) ->
        let rec fold k = function
          | [] -> []
          | (lbl,(x,t)) :: lst ->
            let t = recurse_ty_in_binders k t in
              (lbl, (x, t)) :: fold (k+1) lst
        in
        let lst = fold 0 lst
        and e = recurse e
        in
          mkProject ~loc e lst lbl

      | UnitTerm -> mkUnitTerm ~loc ()

      | Idpath(ty1, term2) ->
          mkIdpath ~loc (recurse_ty ty1) (recurse term2)

      | J(ty1, (name1, name2, name3, ty2), (name4, term2), term3, term4, term5) ->
          mkJ ~loc (recurse_ty ty1)
              (name1, name2, name3, recurse_ty_in_binders 3 ty2)
              (name4, recurse_in_binders 1 term2)
              (recurse term3) (recurse term4) (recurse term5)

      | Refl(ty1, term2)  ->
          mkRefl ~loc (recurse_ty ty1) (recurse term2)

      | Coerce(universe1, universe2, term1) ->
          mkCoerce ~loc universe1 universe2 (recurse term1)

      | NameRecordTy lst ->
        let rec fold k = function
          | [] -> []
          | (lbl,(x,u,e)) :: lst ->
            let e = recurse_in_binders k e
            in
              (lbl, (x, u, e)) :: fold (k+1) lst
        in
          mkNameRecordTy ~loc (fold 0 lst)

      | NameUnit ->
          mkNameUnit ~loc ()

      | NameProd(universe1, universe2, name, term1, term2) ->
          mkNameProd ~loc universe1 universe2 name
                     (recurse term1) (recurse_in_binders 1 term2)

      | NameUniverse universe1 ->
          mkNameUniverse ~loc universe1

      | NamePaths(universe1, term1, term2, term3) ->
          mkNamePaths ~loc universe1 (recurse term1) (recurse term2) (recurse term3)

      | NameId(universe1, term1, term2, term3) ->
          mkNameId ~loc universe1 (recurse term1) (recurse term2) (recurse term3)
    )

and transform_ty ftrans bvs (ty', loc) =
  let recurse    = transform    ftrans bvs in
  let recurse_ty = transform_ty ftrans bvs in

  let recurse_ty_in_binders n = transform_ty ftrans (bvs+n)  in
  match ty' with

  | Universe universe1 ->
      mkUniverse ~loc universe1

  | El(universe1, term1) ->
      mkEl ~loc universe1 (recurse term1)

  | RecordTy lst ->
    let rec fold k = function
      | [] -> []
      | (lbl,(x,t)) :: lst ->
        let t = recurse_ty_in_binders k t
        in
          (lbl, (x, t)) :: fold (k+1) lst
    in
      mkRecordTy ~loc (fold 0 lst)

  | Unit ->
      mkUnit ~loc ()

  | Prod(name, ty1, ty2) ->
      mkProd ~loc name (recurse_ty ty1) (recurse_ty_in_binders 1 ty2)

  | Paths(ty1, term1, term2) ->
      mkPaths ~loc (recurse_ty ty1) (recurse term1) (recurse term2)

  | Id(ty1, term1, term2) ->
      mkId ~loc (recurse_ty ty1) (recurse term1) (recurse term2)

(*****************)
(* spine removal *)
(*****************)

and fold_left_spine : 'b . Position.t ->
                            (name -> ty -> ty -> 'b -> term -> 'b) ->
                            'b -> ty -> term list -> 'b

  = fun loc funct base fty es ->
  let rec loop accum ty = function
    | []    -> accum
    | e::es ->
        match fst (whnf_ty ty) with
        | Prod(n, t1, t2) ->
            let accum' = funct n t1 t2 accum e  in
            let ty' =  beta_ty t2 e  in
            loop accum' ty' es
        | _ -> Error.runtime ~loc "fold_left_spine: Spine without a Pi type"
  in
        loop base fty es

and from_spine ?(loc=Position.nowhere) f fty es =
  from_spine' ~loc (mkVar ~loc f) fty es

and from_spine' ?(loc=Position.nowhere) fn fty es =
  fold_left_spine loc (fun n t1 t2 e1 e2 -> App((n,t1,t2),e1,e2),loc) fn fty es

and fold_left2_spine : 'p 'a .
                            Position.t ->
                            (name -> ty -> ty -> 'a -> 'p -> term -> 'a) ->
                            'a -> ty -> 'p list -> term list -> 'a
  = fun loc funct base fty ps es  ->
  let rec loop accum ty = function
    | [], []    -> accum
    | (p::ps, e::es) ->
        begin
          match fst (whnf_ty ty) with
            | Prod(n, t1, t2) ->
                let accum' = funct n t1 t2 accum p e  in
                let ty' =  beta_ty t2 e  in
                loop accum' ty' (ps, es)
            | _ -> Error.runtime ~loc "fold_left2_spine: Spine without a Pi type"
        end
    | _, _ -> Error.runtime ~loc "Length mismatch in fold_left2_spine"
  in
        loop base fty (ps,es)


and whnf_ty ((t',loc) as t) =
  begin match t' with

    (* tynorm-el *)
    | El (alpha, e) ->
      begin match fst (whnf (mkUniverse ~loc alpha) e) with

        (* tynorm-pi *)
        | NameProd (beta, gamma, x, e1, e2)
            when Universe.eq alpha (Universe.max beta gamma) ->
          let t1 = mkEl ~loc:(snd e1) beta e1 in
          let t2 = mkEl ~loc:(snd e2) gamma e2 in
          mkProd ~loc x t1 t2

        (* tynorm-unit *)
        | NameUnit ->
          mkUnit ~loc ()

        | NameRecordTy lst
            when Universe.eq alpha (Universe.maxs (List.map (fun (_,(_,u,_)) -> u) lst)) ->
          mkRecordTy ~loc
            (List.map
               (fun (lbl, (x, beta, e)) -> (lbl, (x, mkEl ~loc:(snd e) beta e)))
               lst)

        (* tynorm-universe *)
        | NameUniverse beta
            when Universe.eq alpha (Universe.succ beta) ->
          mkUniverse ~loc beta

        (* tynorm-coerce *)
        | Coerce (beta, gamma, e)
            when Universe.eq alpha gamma ->
          whnf_ty (mkEl ~loc:(snd e) beta e)

        (* tynorm-paths *)
        | NamePaths (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = mkEl ~loc:(snd e1) alpha e1  in
            mkPaths ~loc t1 e2 e3

        (* tynorm-id *)
        | NameId (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = mkEl ~loc:(snd e1) alpha e1  in
            mkId ~loc t1 e2 e3

        (* tynorm-other *)
        | (Var _ | Equation _ | Rewrite _ | Ascribe _
              | Lambda _ | App _ | Spine _
              | Record _ | Project _
              | UnitTerm | Idpath _ | NameRecordTy _
              | J _ | Refl _ | Coerce _ | NameProd _
              | NameUniverse _ | NamePaths _ | NameId _) as e' ->
          mkEl ~loc alpha (e', loc)
      end

    | (Universe _ | RecordTy _ | Unit |
       Prod _ | Paths _ | Id _) ->
      t
  end

and whnf t ((e',loc) as e0) =
  let e =
    begin match e' with

      (* norm-var-def *)
      | Var _ -> e0

      (* norm-equation *)
      | Equation (_, _, e2) ->
          whnf t e2

      (* norm-rewrite *)
      | Rewrite (_, _, e2)  ->
          whnf t e2

      (* norm-ascribe *)
      | Ascribe(e, _) ->
        whnf t e

      | App ((x, u1, u2), e1, e2) ->
        begin
          let e1 = whnf (mkProd ~loc x u1 u2) e1 in
            match fst e1 with
              (* norm-app-beta *)
              | Lambda (y, t1, t2, e1')
                  when equal_ty u1 t1 && equal_ty u2 t2 ->
                whnf (beta_ty u2 e2) (beta e1' e2)

              (* norm-app-other *)
              | _ ->
                mkApp ~loc x u1 u2 e1 e2
        end

      | Spine _ -> e0    (* Spines are always in whnf *)

      | Project (e, lst, lbl) ->
        begin
          let e' = whnf (mkRecordTy lst) e in
            match fst e' with
              | Record lst' ->
                  (* XXX: Was this check necessary? *)
                (* when (equal_ty (type_of ctx e') (mkRecordTy lst)) -> * *)
                let rec fold es = function
                  | [] -> Error.impossible "whnf: invalid projection during whnf"
                  | (lbl',(_,_,e)) :: lst ->
                    if lbl = lbl'
                    then
                      List.fold_left beta e es
                    else
                      fold (e::es) lst
                in
                  fold [] lst'
              | _ ->
                mkProject e' lst lbl
        end

      | J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
        begin
          let e2 = whnf (mkPaths ~loc t e3 e4) e2 in
            match fst e2 with
              (* norm-J-idpath *)
              | Idpath (t', e2') when equal_ty t t' ->
                whnf (betas_ty u [e2; e2'; e2]) (beta e1 e2')

              (* norm-J-other *)
              | _ ->
                mkJ ~loc t (x,y,p,u) (z,e1) e2 e3 e4
        end

      (* norm-coerce-trivial *)
      | Coerce (alpha, beta, e)
          when Universe.eq alpha beta ->
        whnf (mkUniverse ~loc alpha) e

      | Coerce (alpha, beta, e) ->
        begin match whnf (mkUniverse ~loc alpha) e with
          (* norm-coerce-trans *)
          | (Coerce (gamma, delta, e), _) when Universe.eq delta alpha ->
            if Universe.eq gamma beta
            then
              (* norm-coerce-trivial *)
              e
            else
              mkCoerce ~loc gamma beta e

          (* norm-coerce-other *)
          | e ->
            mkCoerce ~loc alpha beta e
        end

      | (Lambda _ | Record _ | UnitTerm | Idpath _ |
         Refl _ | NameRecordTy _ | NameUnit | NameProd _ |
         NameUniverse _ | NamePaths _ | NameId _) ->
        e0
    end
  in
    e

(******************************)
(* Shifting de Bruijn indices *)
(******************************)


(** [shift delta e] is a transformation that adds [delta] to all
    free variable indices in [e].
*)

and ftrans_shift ?exn delta bvs = function
  | (Var index, loc) as var ->
      if (index < bvs) then
        (* This is a reference to a bound variable; don't transform *)
        var
      else
        begin
          (* Add delta to the index of this free variable *)
          if index + delta < 0 then begin
            match exn with
            | None -> Error.impossible ~loc "shifting produced a negative index"
            | Some e -> raise e
          end ;
          mkVar ~loc (index + delta)
        end

  | nonvar -> nonvar


(* Adding the short-circut when shifting by zero sped up
 * one (native-code) benchmark by 10%.
 *)

and shift ?exn ?(bound=0) delta term =
  if delta = 0 then
    term
  else
    transform (ftrans_shift ?exn delta) bound term

and shift_ty ?exn ?(bound=0) delta ty =
  if delta = 0 then
    ty
  else
    transform_ty (ftrans_shift ?exn delta) bound ty


and ftrans_subst free_index replacement_term bvs = function
  | (Var index, loc) as var ->
      if index - bvs = free_index then
        (* It's the variable we're looking for.
           Shift it to match the local context *)
        shift bvs replacement_term
      else
        var
  | nonvar -> nonvar

(** [subst j e' e] is a transformation that replaces free occurrences
    of variable [j] in [e] (relative to the "outside" of the term) by [e'].
*)
and subst    free_index replacement_term = transform    (ftrans_subst free_index replacement_term) 0
and subst_ty free_index replacement_term = transform_ty (ftrans_subst free_index replacement_term) 0


(**************************)

 (** [beta body arg] substitutes [arg] in for variable [0] in [body].

  So, if [G, x:t |- body : ...] and [G |- arg : t] then
  [beta body arg] is the term [body[x->arg]].

  This is exactly the substitution required, for example, to
  beta-reduce a function application ([body] is the body of the lambda),
  or to substitute away the parameter in a [Pi] or [Sigma] type ([body] is
  the type of the codomain or second component, respectively).
*)
and beta eBody eArg =
  shift (-1) (subst 0 (shift 1 eArg) eBody)

and beta_ty tBody eArg =
  shift_ty (-1) (subst_ty 0 (shift 1 eArg) tBody)

and betas_ty tBody eArgs =
  let rec betas k t = function
    | [] -> t
    | e :: es ->
      let t = betas (k+1) t es in
        shift_ty (-1) (subst_ty 0 (shift k e) t)
  in
    betas 1 tBody eArgs

let make_arrow ?(loc=Position.nowhere) dom cod =
   mkProd ~loc "_" dom (shift_ty 1 cod)

(**
  Suppose we have [G, x_1:t_1, ..., x_n:t_n |- exp : ...] and the inhabitants
  [e_1; ...; e_n] all well-formed in [G] (!) with types [t_1] through [t_n]
  respectively. Then [strengthen exp [e_1,...,e_n]] is the result of
  substituting away the x_i's, resulting in a term well-formed in [G].

  In particular, [strengthen env eBody [eArg]] is just [beta eBody
 *)
let strengthen exp inhabitants =
  let rec loop n accum = function
    | [] -> accum
    | inhabitant :: inhabitants ->
        begin
          let accum' = beta accum (shift (n-1) inhabitant)  in
          loop (n-1) accum' inhabitants
        end  in
  loop (List.length inhabitants) exp (List.rev inhabitants)

let strengthen_ty ty inhabitants =
  let rec loop n accum = function
    | [] -> accum
    | inhabitant :: inhabitants ->
        begin
          let accum' = beta_ty accum (shift (n-1) inhabitant)  in
          loop (n-1) accum' inhabitants
        end  in
  loop (List.length inhabitants) ty (List.rev inhabitants)

(** If [G |- exp] then [G' |- weaken i exp] where [G'] has an extra (unused)
     variable inserted at position [i]. This is just a simple renumbering, with
     all free variables [< i] unchanged, and all [>= i] incremented (because
     there's a new variable in front of them). *)
let weaken new_var_pos exp =
  shift ~bound:new_var_pos 1 exp

let weaken_ty new_var_pos ty =
  shift_ty ~bound:new_var_pos 1 ty

(***************)
(* Occurrences *)
(***************)

(** Does DeBruijn index occur in a term? *)
let rec occurs k (e, _) =
  match e with

    | Var m -> k = m

    | Equation (e1, t, e2) -> occurs k e1 || occurs_ty k t || occurs k e2

    | Rewrite (e1, t, e2) -> occurs k e1 || occurs_ty k t || occurs k e2

    | Ascribe (e, t) -> occurs k e || occurs_ty k t

    | Lambda (_, t, u, e) -> occurs_ty k t || occurs_ty (k+1) u || occurs (k+1) e

    | App ((_, t, u), e1, e2) -> occurs_ty k t || occurs_ty (k+1) u || occurs k e1 || occurs k e2

    | Spine (f, fty, es) ->
        k = f || occurs_ty k fty || List.exists (occurs k) es

    | Record lst ->
      let rec fold k = function
        | [] -> false
        | (_, (_,t,e)) :: lst ->
          occurs_ty k t || occurs k e || fold (k+1) lst
      in
        fold k lst

    | Project (e, lst, lbl) ->
      let rec fold k = function
        | [] -> false
        | (_, (_, t)) :: lst ->
          occurs_ty k t || fold (k+1) lst
      in
        occurs k e || fold k lst

    | UnitTerm -> false

    | Idpath (t, e) -> occurs_ty k t || occurs k e

    | J (t, (_, _, _, u), (_, e1), e2, e3, e4) ->
      occurs_ty k t || occurs_ty (k+3) u || occurs (k+1) e1 ||
        occurs k e2 || occurs k e3 || occurs k e4

    | Refl (t, e) -> occurs_ty k t || occurs k e

    | Coerce (_, _, e) -> occurs k e

    | NameRecordTy lst ->
      let rec fold k = function
        | [] -> false
        | (_, (_,_,e)) :: lst ->
          occurs k e || fold (k+1) lst
      in
        fold k lst

    | NameUnit -> false

    | NameProd (_, _, _, e1, e2) -> occurs k e1 || occurs (k+1) e2

    | NameUniverse _ -> false

    | NamePaths (_, e1, e2, e3) -> occurs k e1 || occurs k e2 || occurs k e3

    | NameId (_, e1, e2, e3) -> occurs k e1 || occurs k e2 || occurs k e3


(** Does DeBruijn index occur in a type? *)
and occurs_ty k (t, _) =
  match t with

    | Universe _ -> false

    | El (_, e) -> occurs k e

    | RecordTy lst ->
      let rec fold k = function
        | [] -> false
        | (_, (_,t)) :: lst -> occurs_ty k t || fold (k+1) lst
      in
        fold k lst

    | Unit -> false

    | Prod (_, t1, t2) -> occurs_ty k t1 || occurs_ty (k+1) t2

    | Paths (t, e1, e2) -> occurs_ty k t || occurs k e1 || occurs k e2

    | Id (t, e1, e2) -> occurs_ty k t || occurs k e1 || occurs k e2

(* Counting Occurrences *)

(** Count occurrences of DeBruijn index in a term? *)
let rec occurrences k (e, _) =
  match e with

    | Var m -> if k = m then 1 else 0

    | Equation (e1, t, e2) ->
      occurrences k e1 + occurrences_ty k t + occurrences k e2

    | Rewrite (e1, t, e2) ->
      occurrences k e1 + occurrences_ty k t + occurrences k e2

    | Ascribe (e, t) ->
      occurrences k e + occurrences_ty k t

    | Lambda (_, t, u, e) ->
      occurrences_ty k t + occurrences_ty (k+1) u + occurrences (k+1) e

    | App ((_, t, u), e1, e2) ->
      occurrences_ty k t + occurrences_ty (k+1) u + occurrences k e1 + occurrences k e2

    | Spine (f, fty, es) ->
        List.fold_left (+) 0
          ( (if k = f then 1 else 0) ::
            occurrences_ty k fty ::
            List.map (occurrences k) es )

    | Record lst ->
      let rec fold k = function
        | [] -> 0
        | (_, (_,t,e)) :: lst ->
          occurrences_ty k t + occurrences k e + fold (k+1) lst
      in
        fold k lst

    | Project (e, lst, lbl) ->
      let rec fold k = function
        | [] -> 0
        | (_, (_, t)) :: lst ->
          occurrences_ty k t + fold (k+1) lst
      in
        occurrences k e + fold k lst

    | UnitTerm -> 0

    | Idpath (t, e) ->
      occurrences_ty k t + occurrences k e

    | J (t, (_, _, _, u), (_, e1), e2, e3, e4) ->
      occurrences_ty k t + occurrences_ty (k+3) u + occurrences (k+1) e1 +
        occurrences k e2 + occurrences k e3 + occurrences k e4

    | Refl (t, e) -> occurrences_ty k t + occurrences k e

    | Coerce (_, _, e) -> occurrences k e

    | NameRecordTy lst ->
      let rec fold k = function
        | [] -> 0
        | (_, (_,_,e)) :: lst ->
          occurrences k e + fold (k+1) lst
      in
        fold k lst

    | NameUnit -> 0

    | NameProd (_, _, _, e1, e2) ->
      occurrences k e1 + occurrences (k+1) e2

    | NameUniverse _ -> 0

    | NamePaths (_, e1, e2, e3) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3

    | NameId (_, e1, e2, e3) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3

(** Count occurrences of DeBruijn index in a type? *)
and occurrences_ty k (t, _) =
  match t with
    | Universe _ -> 0
    | El (_, e) -> occurrences k e
    | RecordTy lst ->
      let rec fold k = function
        | [] -> 0
        | (_,(_,t)) :: lst ->
          occurrences_ty k t + fold (k+1) lst
      in
        fold k lst
    | Unit -> 0
    | Prod (_, t1, t2) -> occurrences_ty k t1 + occurrences_ty (k+1) t2
    | Paths (t, e1, e2) -> occurrences_ty k t + occurrences k e1 + occurrences k e2
    | Id (t, e1, e2) -> occurrences_ty k t + occurrences k e1 + occurrences k e2

(******************)
(* Simplification *)
(******************)

(* Reduce very simple (almost administrative) lambdas *)

(** Is this argument simple enought to be worth plugging into an
   arbitrary lambda?
*)
let rec simple_term term =
  match fst term with
  | UnitTerm       -> true
  | Var _          -> true
  | App(_, e1, e2) -> simple_term e1 && simple_term e2
  | NameUnit       -> true
  | NameUniverse _ -> true
  | Refl (t,e)     -> simple_term e
  | Idpath (t,e)   -> simple_term e
  | _              -> false

let ftrans_simplify bvs term =
  match fst term with
  | App((x1,ty2,ty3), (Lambda(x4,ty5,ty6,e7),_), e8) when equal_ty ty2 ty5
                                                       && equal_ty ty3 ty6 ->
      (* Reduce if the type annotations match literally,
       * and either the argument is very simple or the
       * lambda ignores its term or is linear.
       *)
      if simple_term e8 || (occurrences 0 e7 <= 1) then
        beta e7 e8
      else
        term

  | _ -> term

let simplify = transform ftrans_simplify 0
let simplify_ty = transform_ty ftrans_simplify 0
