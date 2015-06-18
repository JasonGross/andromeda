(** Pattern matching support for hints. *)

(** A type which is exactly like [Tt.ty] except that its bound
    variables refer to pattern variables instead of the ordinary
    bound variables. *)
type pty = Tt.ty

type pterm = Tt.term

(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Name of Name.t
  | PrimApp of Name.t * term list
  | Spine of term * (pty, pty) Tt.abstraction * term list
  | Bracket of ty
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of pterm * pty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

(** A beta hint is an abstracted term pattern and a term. We match against
    the pattern and rewrite into the term. *)
type beta_pattern =
  | BetaName of Name.t
  | BetaPrimApp of Name.t * term list
  | BetaSpine of term * (pty, pty) Tt.abstraction * term list

type beta_hint = Name.t * (Tt.ty, beta_pattern * Tt.term) Tt.abstraction

(** An eta hint is an abstracted type pattern together with variables that match
    the lhs and rhs of an equation. *)
type eta_hint = Name.t * (Tt.ty, ty * Syntax.bound * Syntax.bound) Tt.abstraction

(** A general hint is an abstracted triple of patterns that match the type and both
    sides of equation. *)
type general_hint = Name.t * (Tt.ty, ty * term * term) Tt.abstraction

(** An inhabit hint is a universally quantified type. *)
type inhabit_hint = (Tt.ty, ty) Tt.abstraction

val print_pattern : ?max_level:int -> Name.t list -> t -> (Format.formatter -> unit)

val print_beta_hint : ?max_level:int -> Name.t list -> beta_hint -> Format.formatter -> unit

val print_eta_hint : ?max_level:int -> Name.t list -> eta_hint -> Format.formatter -> unit

val print_inhabit_hint : ?max_level:int -> Name.t list -> inhabit_hint -> Format.formatter -> unit

val print_hint : ?max_level:int -> Name.t list -> general_hint -> Format.formatter -> unit
