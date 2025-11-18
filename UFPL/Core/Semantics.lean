import UFPL.Core.Types
import UFPL.Core.Syntax

namespace UFPL
namespace Core
open HList

/-- World/time‑sensitive interpretation. -/
structure Interp (Sig : Signature) (D : Ty → Type) (W T : Type) where
  constI : (c : ConstSym) → D c.τ
  funcI  : (f : FuncSym) → HList (fun τ => D τ) f.dom → D f.cod
  predI  : (p : PredSym) → W → T → HList (fun τ => D τ) p.dom → Prop

/-- A Kripke/relational model with deontic selection and temporal order. -/
structure Model (Sig : Signature) where
  D     : Ty → Type
  W     : Type
  T     : Type
  le    : T → T → Prop
  Rbox  : W → W → Prop
  RK    : D Ty.agt → W → W → Prop
  RB    : D Ty.agt → W → W → Prop
  ideal : W → W → Prop
  I     : Interp Sig D W T

/-- Variable environment by sort (name → denotation). -/
structure Env (D : Ty → Type) where
  ind : String → D Ty.ind
  agt : String → D Ty.agt
  act : String → D Ty.act
  wld : String → D Ty.wld
  tim : String → D Ty.tim

namespace Env
  def get {D} (ρ : Env D) : (τ : Ty) → String → D τ
  | .ind, x => ρ.ind x
  | .agt, x => ρ.agt x
  | .act, x => ρ.act x
  | .wld, x => ρ.wld x
  | .tim, x => ρ.tim x

  def set {D} (ρ : Env D) (τ : Ty) (x : String) (v : D τ) : Env D :=
    match τ with
    | .ind => {ρ with ind := fun y => if y = x then v else ρ.ind y}
    | .agt => {ρ with agt := fun y => if y = x then v else ρ.agt y}
    | .act => {ρ with act := fun y => if y = x then v else ρ.act y}
    | .wld => {ρ with wld := fun y => if y = x then v else ρ.wld y}
    | .tim => {ρ with tim := fun y => if y = x then v else ρ.tim y}
end Env

mutual
  def evalArgs {Sig} (M : Model Sig) (ρ : Env M.D) :
      {xs : List Ty} →
      HList (fun τ => Term τ) xs → HList (fun τ => M.D τ) xs
  | [],     .nil        => .nil
  | _::_,   .cons t ts  => .cons (Term.eval M ρ t) (evalArgs M ρ ts)

  def Term.eval {Sig} (M : Model Sig) (ρ : Env M.D) :
      {τ : Ty} → Term τ → M.D τ
  | _, .var τ x  => ρ.get τ x
  | _, .const c  => M.I.constI c
  | _, .app f as => M.I.funcI f (evalArgs M ρ as)
end

/-- Truth at world/time/environment (Prop semantics). -/
def sat {Sig} (M : Model Sig) (w : M.W) (t : M.T) (ρ : Env M.D) : Form → Prop
  | .top        => True
  | .bot        => False
  | .pred p as  => M.I.predI p w t (evalArgs M ρ as)
  | .eq t1 t2   => Term.eval M ρ t1 = Term.eval M ρ t2
  | .not φ      => ¬ sat M w t ρ φ
  | .and φ ψ    => sat M w t ρ φ ∧ sat M w t ρ ψ
  | .or  φ ψ    => sat M w t ρ φ ∨ sat M w t ρ ψ
  | .imp φ ψ    => sat M w t ρ φ → sat M w t ρ ψ
  | .iff φ ψ    => sat M w t ρ φ ↔ sat M w t ρ ψ
  | .forallE x τ φ => ∀ (v : M.D τ), sat M w t (ρ.set τ x v) φ
  | .existsE x τ φ => ∃ (v : M.D τ), sat M w t (ρ.set τ x v) φ
  | .box φ      => ∀ w', M.Rbox w w' → sat M w' t ρ φ
  | .dia φ      => ∃ w', M.Rbox w w' ∧ sat M w' t ρ φ
  | .knows a φ  =>
      let av := Term.eval M ρ a
      ∀ w', M.RK av w w' → sat M w' t ρ φ
  | .believes a φ =>
      let av := Term.eval M ρ a
      ∀ w', M.RB av w w' → sat M w' t ρ φ
  | .obl φ      => ∀ w', M.ideal w w' → sat M w' t ρ φ
  | .G φ        => ∀ t', M.le t t' → sat M w t' ρ φ
  | .F φ        => ∃ t', M.le t t' ∧ sat M w t' ρ φ
  | .H φ        => ∀ t', M.le t' t → sat M w t' ρ φ
  | .P φ        => ∃ t', M.le t' t ∧ sat M w t' ρ φ

/-- Validity in a fixed model. -/
def validIn (M : Model Sig) (φ : Form) : Prop :=
  ∀ (w : M.W) (t : M.T) (ρ : Env M.D), sat M w t ρ φ

end Core
end UFPL
