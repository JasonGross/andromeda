(** Typing context and runtime environment *)

(** A context holds free variables with their types and an
    environment of runtime bindings. *)
type t = {
  free : (Name.t * Tt.ty) list;
  primitive : (Name.t * Tt.primsig) list;
  bound : (Name.t * Value.value) list;
  beta : Pattern.beta_hint list ;
  eta : Pattern.eta_hint list;
  hint : Pattern.general_hint list;
  inhabit : Pattern.inhabit_hint list;
  files : string list;
}

(** The empty context *)
let empty = {
  free = [];
  primitive = [];
  bound = [] ;
  beta = [] ;
  eta = [] ;
  hint = [] ;
  inhabit = [] ;
  files = [] ;
}

let eta_hints {eta=lst} = lst

let beta_hints {beta=lst} = lst

let general_hints {hint=lst} = lst

let inhabit_hints {inhabit=lst} = lst

let bound_names {bound=lst} = List.map fst lst

let primitives {primitive=lst} =
  List.map (fun (x, (yts, _)) -> (x, List.length yts)) lst

let used_names ctx =
  List.map fst ctx.free @ List.map fst ctx.bound @ List.map fst ctx.primitive

let lookup_free x {free=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_primitive x {primitive=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {bound=lst} =
  try
    snd (List.nth lst k)
  with
  | Failure _ -> Error.impossible "invalid de Bruijn index %d" k

let is_bound x ctx =
  match lookup_free x ctx with
  | None ->
    begin match lookup_primitive x ctx with
      | None -> false
      | Some _ -> true
    end
  | Some _ -> true

let add_free x t ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with free = (x,t) :: ctx.free }

let add_primitive x ytsu ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with primitive = (x, ytsu) :: ctx.primitive }

let add_beta h ctx = { ctx with beta = h :: ctx.beta }

let add_eta h ctx = { ctx with eta = h :: ctx.eta }

let add_hint h ctx = { ctx with hint = h :: ctx.hint }

let add_inhabit h ctx = { ctx with inhabit = h :: ctx.inhabit }

let add_fresh x t ctx =
  let y = Name.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

let add_file f ctx =
  { ctx with files = (Filename.basename f) :: ctx.files }

let included f { files } = List.mem (Filename.basename f) files

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---------@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>: %t@]@\n" (Name.print x) (Tt.print_ty forbidden_names t))
    (List.rev ctx.free) ;
  Print.print ppf "---END---@."