namespace UFPL
namespace Core

/-- Logical sorts used by UFPL. Extend as needed. -/
inductive Ty where
  | ind | agt | act | wld | tim
deriving DecidableEq, Repr

/-- Heterogeneous lists for typed symbol arguments. -/
inductive HList {α : Type} (β : α → Type) : List α → Type where
  | nil  : HList β []
  | cons : {x : α} → β x → HList β xs → HList β (x :: xs)

namespace HList
  def map {α} {β γ : α → Type} :
      {xs : List α} → (∀ {a}, β a → γ a) → HList β xs → HList γ xs
  | [],       _, .nil       => .nil
  | (_::_),   f, .cons y ys => .cons (f y) (map f ys)
end HList

/-- Function, predicate, and constant symbols (multi‑sorted). -/
structure FuncSym where
  name : String
  dom  : List Ty
  cod  : Ty
deriving DecidableEq, Repr

structure PredSym where
  name : String
  dom  : List Ty
deriving DecidableEq, Repr

structure ConstSym where
  name : String
  τ    : Ty
deriving DecidableEq, Repr

/-- A signature is just a set of symbols. -/
structure Signature where
  funcs  : List FuncSym := []
  preds  : List PredSym := []
  consts : List ConstSym := []

end Core
end UFPL
