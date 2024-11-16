(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

type ty =
  | TVar of tvar
  | TArr of ty * ty
  | TPair of ty * ty
  | TUnit
  | TCoprod of ty * ty
  | TFalse

(** Terms. *)
type tm =
| Var of var
| App of tm * tm
| Abs of var * ty * tm
| Pair of tm * tm
| Fst of tm
| Snd of tm
| Unit
| Left of tm * ty
| Right of ty * tm
| Case of tm * tm * tm
| Absurd of tm * ty