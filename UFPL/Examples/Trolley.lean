import UFPL.Core.Types
import UFPL.Core.Syntax
import UFPL.Core.Semantics
import UFPL.Core.EvalBool

namespace UFPL.Examples
open UFPL.Core
open HList

/-- Atoms for the trolley switch case (0-ary predicates). -/
def Divert : PredSym := { name := "Divert", dom := [] }
def Kill1  : PredSym := { name := "Kill1",  dom := [] }
def Kill5  : PredSym := { name := "Kill5",  dom := [] }

/-- Signature for this toy example. -/
def SigT : Signature := { preds := [Divert, Kill1, Kill5] }

/-- Worlds: decision `w0`, divert `wD`, no-divert `wN`. -/
inductive W where | w0 | wD | wN
deriving DecidableEq, Repr   -- `decide (w' = …)` uses this

/-- Domain per sort used in this example. -/
abbrev DT : Ty → Type
  | .ind => Unit
  | .agt => Unit
  | .act => Unit
  | .wld => Unit
  | .tim => Nat

/-- A default inhabitant for each sort (`DT τ`), used in the interpreter. -/
def defaultOfTy : (τ : Ty) → DT τ
  | .tim => (0 : Nat)
  | .ind | .agt | .act | .wld => ()

/-- World/time-sensitive interpretation (Prop semantics). -/
def interpT : Interp SigT DT W Nat := {
  constI := fun c => defaultOfTy c.τ,
  funcI  := fun f _ => defaultOfTy f.cod,
  predI  := fun p w _ _ =>
    match p.name, w with
    | "Divert", .wD => True  | "Divert", .wN => False | "Divert", .w0 => False
    | "Kill1",  .wD => True  | "Kill1",  .wN => False | "Kill1",  .w0 => False
    | "Kill5",  .wD => False | "Kill5",  .wN => True  | "Kill5",  .w0 => False
    | _, _ => False
}

/-- The concrete model for the trolley example (Prop semantics). -/
def M : Model SigT :=
  { D     := DT
  , W     := W
  , T     := Nat
  , le    := Nat.le
  , Rbox  := fun w w' => match w with
                | .w0 => w' = .w0 ∨ w' = .wD ∨ w' = .wN
                | .wD => w' = .wD
                | .wN => w' = .wN
  , RK    := fun _ _ _ => True
  , RB    := fun _ _ _ => True
  , ideal := fun w w' => match w with
                | .w0 => w' = .wD
                | .wD => w' = .wD
                | .wN => w' = .wN
  , I     := interpT
  }

/-- Default environment (no free variables are used here). -/
def ρ : Env M.D :=
  { ind := fun _ => ()
  , agt := fun _ => ()
  , act := fun _ => ()
  , wld := fun _ => ()
  , tim := fun _ => (0 : Nat) }

/-- UFPL formulas used in this scenario. -/
def φDivert : Form := Form.pred Divert HList.nil
def φKill1  : Form := Form.pred Kill1  HList.nil
def φKill5  : Form := Form.pred Kill5  HList.nil

/-- Scenario facts and exclusivity of outcomes. -/
def facts : Form :=
  let f1 := Form.imp φDivert (Form.and φKill1 (Form.not φKill5))
  let f2 := Form.imp (Form.not φDivert) (Form.and φKill5 (Form.not φKill1))
  Form.and f1 (Form.and f2 (Form.and (Form.or φKill1 φKill5)
                                     (Form.not (Form.and φKill1 φKill5))))

/-- "If exactly one dies, obligation is to avoid 5 deaths." -/
def lesserEvil : Form :=
  let xor := Form.and (Form.or φKill1 φKill5) (Form.not (Form.and φKill1 φKill5))
  Form.imp xor (Form.obl (Form.not φKill5))

def targetObligation : Form := Form.obl φDivert

/--
Boolean adapter for the trolley model: finite worlds/times/domains and Bool relations.
Times here are a single instant `[0]`; extend if you want temporal operators over a larger slice.
-/
def E : EvalSupport M :=
  { worlds := [W.w0, W.wD, W.wN]
  , times  := [(0 : Nat)]
  , dom    :=
      (fun
        | .ind => [()]
        | .agt => [()]
        | .act => [()]
        | .wld => [()]
        | .tim => [(0 : Nat)])
  , predB  := fun p w _ _ =>
      match p.name, w with
      | "Divert", .wD => true  | "Divert", .wN => false | "Divert", .w0 => false
      | "Kill1",  .wD => true  | "Kill1",  .wN => false | "Kill1",  .w0 => false
      | "Kill5",  .wD => false | "Kill5",  .wN => true  | "Kill5",  .w0 => false
      | _, _ => false
  , decEqD :=
      (fun τ => by
        cases τ <;> dsimp [M, DT] <;> exact inferInstance)
  , leB    := fun t t' =>
      Nat.ble t t'
  , rboxB  := fun w w' =>
      match w, w' with
      | .w0, .w0 => true
      | .w0, .wD => true
      | .w0, .wN => true
      | .wD, .wD => true
      | .wN, .wN => true
      | _,   _   => false
  , idealB := fun w w' =>
      match w, w' with
      | .w0, .wD => true
      | .wD, .wD => true
      | .wN, .wN => true
      | _,   _   => false
  , rkB    := fun _ _ _ => true
  , rbB    := fun _ _ _ => true
  }

/-- Prop-semantics queries (for proofs). -/
def FactsHoldAtW0P      : Prop := sat M W.w0 (0 : Nat) ρ facts
def LesserEvilAtW0P     : Prop := sat M W.w0 (0 : Nat) ρ lesserEvil
def ObligationToDivertP : Prop := sat M W.w0 (0 : Nat) ρ targetObligation

/-- Bool-semantics queries (for printing). -/
def FactsHoldAtW0B      : Bool := satB M E W.w0 (0 : Nat) ρ facts
def LesserEvilAtW0B     : Bool := satB M E W.w0 (0 : Nat) ρ lesserEvil
def ObligationToDivertB : Bool := satB M E W.w0 (0 : Nat) ρ targetObligation

end UFPL.Examples
