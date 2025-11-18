import UFPL.Core.Types
import UFPL.Core.Syntax
import UFPL.Core.Semantics

namespace UFPL
namespace Examples
open UFPL.Core

/-- Two individual-name constants for the classic Kripke case. -/
def H : ConstSym := { name := "Hesperus",  τ := Ty.ind }
def P : ConstSym := { name := "Phosphorus", τ := Ty.ind }

/-- Concrete necessity-of-identity instance for `H` and `P`. -/
def NecId_HP : Form :=
  Form.imp (Form.eq (Term.const H) (Term.const P))
           (Form.box (Form.eq (Term.const H) (Term.const P)))

/-- In our semantics, constants are rigid; thus a=b → □(a=b) is valid. -/
theorem necIdentity_HP_valid
  {Sig : Signature} (M : Model Sig) :
  validIn M NecId_HP := by
  intro w t ρ h
  intro w' _R
  simpa [sat, NecId_HP] using h

end Examples
end UFPL
