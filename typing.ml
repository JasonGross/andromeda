(** Type inference. *)

module Ctx = Context
module D = Desugar
module P = Print
module S = Syntax



type env = {
  ctx : Ctx.context;
  handlers : (int * S.term * S.term) list;  (* int is the install-level *)
}

let empty_env = { ctx = Ctx.empty_context;
                  handlers = [];
                 }

let currentLevel env = List.length env.ctx.Ctx.names

let add_parameter x t env =
  {env with ctx = Ctx.add_parameter x t env.ctx}
let add_definition x t e env =
  {env with ctx = Ctx.add_definition x t e env.ctx}

let lookup v env = Ctx.lookup v env.ctx
let lookup_classifier v env = Ctx.lookup_classifier v env.ctx
let whnf env e = Norm.whnf env.ctx e
let print_term env e = Print.term env.ctx.Ctx.names e



let rec equal env t1 t2 k =
  t1 = t2 ||                    (* Short-circuit in the common case *)
  handled env t1 t2 ||
  match (whnf env k) with
      | S.Pi (x, t3, k3) ->
          let env' = add_parameter x t3 env  in
          let t1' = S.App (S.shift 1 t1, S.Var 0) in
          let t2' = S.App (S.shift 1 t2, S.Var 0) in
          equal env' t1' t2'  k3
      | S.Sigma (x, c, d) ->
          let t1' i = S.Proj (i, t1) in
          let t2' i = S.Proj (i, t2) in
          equal env (t1' 1) (t2' 1) c &&
          equal env (t1' 2) (t2' 2) (S.beta d (t1' 1))
      | S.Eq(S.Ju, _, _, _) ->
          (* K rule for Judgmental equality! *)
          true
      | S.Base S.TUnit ->
          (* Everything is equal at type unit *)
          true
      | _ -> equal_structural env t1 t2

and equal_structural env t1 t2 =
  let t1' = whnf env t1 in
  let t2' = whnf env t2 in
  t1' = t2' ||       (* Catches U/Var/Const/Base; also, might short-circuit *)
  handled env t1' t2' ||
  match t1', t2' with
  | S.Pi    (x, t11, t12), S.Pi    (_, t21, t22)
  | S.Sigma (x, t11, t12), S.Sigma (_, t21, t22) ->
      equal_structural env                       t11 t21 &&
      equal_structural (add_parameter x t11 env) t12 t22

  | S.Refl(o1, t1, k1), S.Refl(o2, t2, k2) ->
      o1 = o2 &&
      equal_structural env k1 k2 &&
      equal env t1 t2 k1

  | S.Eq(o1, e11, e12, t1), S.Eq(o2, e21, e22, t2) ->
      o1 = o2 &&
      equal_structural env t1 t2 &&
      equal env e11 e21 t1 &&
      equal env e21 e22 t1

  | S.Lambda(x, t1, e1), S.Lambda(_, t2, e2) ->
      equal_structural env t1 t2 &&
      equal_structural (add_parameter x t1 env) e1 e2

  | S.Pair(e11, e12), S.Pair(e21, e22) ->
      equal_structural env e11 e21 &&
      equal_structural env e12 e22

  | S.J(o1, c1, w1, a1, b1, t1, p1),
    S.J(o2, c2, w2, a2, b2, t2, p2) ->
      let pathtype = S.Eq(o1, a1, b1, t1) in
      o1 == o2 &&
      equal_structural env t1 t2 &&
      equal env a1 a2 t1 &&
      equal env b1 b2 t1 &&
      (* OK, at this point we are confident that both paths
       * have the same type *)
      equal env p1 p2 pathtype &&
      equal_structural
           (add_parameter "_p" pathtype
              (add_parameter "_y" t1
                (add_parameter "_x" t1 env))) c1 c2   &&
      equal (add_parameter "_z" t1 env) w1 w2
               (S.beta (S.beta (S.beta w1 (S.Var 0)) (S.Var 0))
                       (S.Refl(o1, S.Var 0, t1)))

  | S.App _, S.App _
  | S.Proj _ , S.Proj _ ->
      begin
        match equal_path env t1' t2' with
        | Some _ -> true
        | None   -> false
      end

  | (S.Var _ | S.Lambda _ | S.Pi _ | S.App _ | S.Sigma _ |
     S.Pair _ | S.Proj _ | S.Refl _ | S.Eq _ | S.J _ |
     S.U _ | S.Base _ | S.Const _), _ -> false


and equal_path env e1 e2 =
  match e1, e2 with
  | S.Var v1, S.Var v2 ->
      if v1 = v2 then Some (lookup_classifier v1 env) else None


  | S.Proj (i1, e3), S.Proj (i2, e4) when i1 = i2 ->
      begin
        match i1, equal_path env e3 e4 with
          | 1, Some (S.Sigma(_, t1, _)) -> Some t1
          | 2, Some (S.Sigma(_, _, t2)) -> Some (S.beta t2 e1)
          | _                           -> None
      end

  | S.App (e3, e5), S.App(e4, e6) ->
      begin
        match equal_path env e3 e4 with
          | Some (S.Pi(_, t1, t2)) ->
              if equal env e5 e6 t1 then
                Some (S.beta t2 e5)
              else
                None
          | _ -> None
      end

  | _, _ -> None


(* We check handlers in both directions, so that the user is not required
 * to worry about symmetry, i.e., which direction to specify the equivalence *)
and handled env e1 e2 =
  let level = currentLevel env  in
  let rec loop = function
    | [] -> false
    | (installLevel, h1', h2')::rest ->
        let d = level - installLevel  in
        let h1 = S.shift d h1'  in
        let h2 = S.shift d h2'  in
        (e1 = h1) && (e2 = h2)  ||  (e1 = h2) && (e2 = h1) || loop rest
  in
    loop (env.handlers)




let rec infer env (term, loc) =
  match term with

    | D.Var v ->
        (S.Var v, lookup_classifier v env)

    | D.Pi (x, term1, term2) ->
      begin
        let t1, u1 = infer_ty env term1 in
        let env' = add_parameter x t1 env in
        let t2, u2 = infer_ty env' term2  in
        (*
        let _ =
                (print_endline ("Original Pi : " ^ Desugar.string_of_term
        (term,loc));
                 print_endline ("Translated domain: " ^ S.string_of_term t1);
                 print_endline ("Translated codomain: " ^ S.string_of_term t2);
                 print_endline ("Output Pi : " ^ S.string_of_term (S.Pi(x, t1,
                 t2)))
                )  in
        *)
        S.Pi(x, t1, t2), S.U (S.universe_join u1 u2)
      end

    | D.Sigma (x, term1, term2) ->
      begin
        let t1, u1 = infer_ty env term1 in
        let env' = add_parameter x t1 env in
        let t2, u2 = infer_ty env' term2  in
        S.Sigma(x, t1, t2), S.U (S.universe_join u1 u2)
      end

    | D.Universe u ->
        S.U u, S.U (S.universe_classifier u)

    | D.App (term1, term2) ->
        begin
          let e1, t1 = infer env term1  in
          match whnf env t1 with
          | S.Pi(_, t11, t12) ->
            let e2 = check env term2 t11  in
            let appTy = S.beta t12 e2  in
            S.App(e1, e2), appTy
          | _ ->
            Error.typing ~loc "Applying a term of type %t"
              (print_term env t1)
        end

    | D.Pair (term1, term2) ->
        begin
          let e1, t1 = infer env term1  in
          let e2, t2 = infer env term2  in
          let ty = S.Sigma("_", t1, S.shift 1 t2)  in
          S.Pair(e1,e2), ty
        end

    | D.Proj (("1"|"fst"), term2) ->
        begin
          let e2, t2 = infer env term2  in
          match whnf env t2 with
          | S.Sigma(_, t21, _) ->  S.Proj(1, e2), t21
          | _ -> Error.typing ~loc "Projecting from %t with type %t"
                    (print_term env e2) (print_term env t2)
        end

    | D.Proj (("2"|"snd"), term2) ->
        begin
          let e2, t2 = infer env term2  in
          match whnf env t2 with
          | S.Sigma(_, _, t22) -> S.Proj(2, e2), S.beta t22 (S.Proj(1, e2))
          | _ -> Error.typing ~loc "Projecting from %t with type %t"
                    (print_term env e2) (print_term env t2)
        end

    | D.Proj (s1, _) -> Error.typing ~loc "Unrecognized projection %s" s1

    | D.Ascribe (term1, term2) ->
        begin
          let t2, _ = infer_ty env term2  in
          let e1 = check env term1 t2  in
          e1, t2
        end

    | D.Lambda (x, None, _) -> Error.typing ~loc "cannot infer the domain type"

    | D.Lambda (x, Some term1, term2) ->
        begin
          let t1, k1 = infer_ty env term1 in
          let e2, t2 = infer (add_parameter x t1 env) term2 in
          S.Lambda (x, t1, e2), S.Pi(x, t1, t2)
        end

    | D.Handle (term, handlers) ->
        let env'= addHandlers env handlers in
        infer env' term

    | D.Equiv(o, term1, term2, term3) ->
        begin
          let ty3, u3 = infer_ty env term3 in
          let e1 = check env term1 ty3  in
          let e2 = check env term2 ty3  in
          S.Eq (o, e1, e2, ty3), S.U u3
        end

    | D.Refl(o, term) ->
        let e, t = infer env term in
        S.Refl(o, e, t), S.Eq(o, e, e, t)


(*
    | D.J(o, term1, term2, term3) ->
        let exp, e1, e2, t = infer_eq env term3 o  in
        let e1 = check env term1 ty3  in
          let e2 = check env term2 ty3  in
          S.Eq (o, e1, e2, ty3), S.U u3
        end
        *)


and addHandlers env handlers =
  let installLevel = currentLevel env  in
  let rec loop = function
    | [] -> env
    | term :: rest ->
        let _, e1, e2, _ = infer_eq env term S.Ju in
        let env' = { env with handlers = (installLevel,e1,e2) :: env.handlers } in
        addHandlers env' rest  in
  loop handlers

and infer_ty env term =
  let t, k = infer env term in
  match whnf env k with
  | S.U u -> t, u
  | _ -> Error.typing "Not a type: %t" (print_term env t)

and infer_eq env term o =
  let exp, ty = infer env term in
  match whnf env ty with
  | S.Eq(o', e1, e2, t) ->
      if (o = o') then
        exp, e1, e2, t
      else
        Error.typing "Wrong sort of equivalence: %t" (print_term env ty)
  | _ -> Error.typing "Not an equivalence: %t" (print_term env exp)


and check env ((term1, loc) as term) t =
  match term1, whnf env t with
    | D.Lambda (x, None, term2), S.Pi (_, t1, t2) ->
        begin
          let e2 = check (add_parameter x t1 env) term2 t2 in
          S.Lambda(x, t1, e2)
        end
    | D.Pair (term1, term2), S.Sigma(x, t1, t2) ->
        let e1 = check env term1 t1  in
        let t2' = S.beta t2 e1  in
        let e2 = check env term2 t2'  in
        S.Pair(e1, e2)
    | _, _ ->
      let e, t' = infer env term in
        (* NB: Using equal_structural lets us avoid the question of
         * which universe to compare t' and t in. Of course, it presumes
         * they belong to a common universe, so a non-subsumptive
         * hierarchy would cause problems here. *)
        if not (equal_structural env t' t ) then
          Error.typing ~loc "expression %t has type %t\nbut it should have type %t"
            (print_term env e) (print_term env t') (print_term env t)
        else
          e



let inferParam ?(verbose=false) env names ((_,loc) as term) =
  let ty,_ = infer_ty env term in
  let env, _ = List.fold_left
      (fun (env, t) name ->
         (*if List.mem x ctx.names then Error.typing ~loc "%s already exists" x ;*)
         if verbose then Format.printf "Term %s is assumed.@." name ;
         (add_parameter name t env, Syntax.shift 1 t))
        (env, ty) names  in
  env

let inferDefinition ?(verbose=false) env name ((_,loc) as termDef) =
  let expr, ty = infer env termDef in
  if verbose then Format.printf "%s is defined.@." name;
  add_definition name ty expr env

let inferAnnotatedDefinition ?(verbose=false) env name ((_,loc) as term) termDef =
  let ty, _ = infer_ty env term  in
  let expr = check env termDef ty in
  add_definition name ty expr env



