import UFPL.Core.Types
import UFPL.Core.Syntax
import UFPL.Core.Semantics

namespace UFPL
namespace Core
open HList

/--
`EvalSupport` packages *finite* enumerations and Boolean adapters needed to
compute `satB` (a Boolean semantics) for a given model `M`.
-/
structure EvalSupport {Sig : Signature} (M : Model Sig) where
  worlds : List M.W
  times  : List M.T
  dom    : (τ : Ty) → List (M.D τ)

  -- atomic predicate adapter (Bool)
  predB  :
    (p : PredSym) → (w : M.W) → (t : M.T) →
    HList (fun τ => M.D τ) p.dom → Bool

  -- equality & time order adapters
  decEqD : (τ : Ty) → DecidableEq (M.D τ)
  leB    : M.T → M.T → Bool

  -- relations as Bool
  rboxB  : M.W → M.W → Bool
  idealB : M.W → M.W → Bool
  rkB    : M.D Ty.agt → M.W → M.W → Bool
  rbB    : M.D Ty.agt → M.W → M.W → Bool

namespace EvalSupport
  /-- Boolean "for all" over a list given `p : α → Bool`. -/
  def all {α} (xs : List α) (p : α → Bool) : Bool :=
    xs.all p
  /-- Boolean "exists" over a list given `p : α → Bool`. -/
  def any {α} (xs : List α) (p : α → Bool) : Bool :=
    xs.any p
end EvalSupport

/-- Boolean semantics for UFPL over *finite* supports. -/
partial def satB {Sig} (M : Model Sig) (E : EvalSupport M)
    (w : M.W) (t : M.T) (ρ : Env M.D) : Form → Bool
  | .top      => true
  | .bot      => false
  | .pred p as =>
      E.predB p w t (evalArgs M ρ as)
  | .eq (τ := τ) t1 t2 =>
      -- decide equality at sort `τ` using the per-sort instance
      (by
        have _ := E.decEqD τ
        exact decide (Term.eval M ρ t1 = Term.eval M ρ t2))
  | .not φ    => !(satB M E w t ρ φ)
  | .and φ ψ  => (satB M E w t ρ φ) && (satB M E w t ρ ψ)
  | .or  φ ψ  => (satB M E w t ρ φ) || (satB M E w t ρ ψ)
  | .imp φ ψ  => !(satB M E w t ρ φ) || (satB M E w t ρ ψ)
  | .iff φ ψ  => (satB M E w t ρ φ) == (satB M E w t ρ ψ)
  | .forallE x τ φ =>
      EvalSupport.all (E.dom τ) (fun v => satB M E w t (ρ.set τ x v) φ)
  | .existsE x τ φ =>
      EvalSupport.any (E.dom τ) (fun v => satB M E w t (ρ.set τ x v) φ)
  | .box φ =>
      EvalSupport.all E.worlds (fun w' => if E.rboxB w w' then satB M E w' t ρ φ else true)
  | .dia φ =>
      EvalSupport.any E.worlds (fun w' => E.rboxB w w' && satB M E w' t ρ φ)
  | .knows a φ =>
      let av := Term.eval M ρ a
      EvalSupport.all E.worlds (fun w' => if E.rkB av w w' then satB M E w' t ρ φ else true)
  | .believes a φ =>
      let av := Term.eval M ρ a
      EvalSupport.all E.worlds (fun w' => if E.rbB av w w' then satB M E w' t ρ φ else true)
  | .obl φ =>
      EvalSupport.all E.worlds (fun w' => if E.idealB w w' then satB M E w' t ρ φ else true)
  | .G φ =>
      EvalSupport.all E.times (fun t' => if E.leB t t' then satB M E w t' ρ φ else true)
  | .F φ =>
      EvalSupport.any E.times (fun t' => E.leB t t' && satB M E w t' ρ φ)
  | .H φ =>
      EvalSupport.all E.times (fun t' => if E.leB t' t then satB M E w t' ρ φ else true)
  | .P φ =>
      EvalSupport.any E.times (fun t' => E.leB t' t && satB M E w t' ρ φ)

end Core
end UFPL
