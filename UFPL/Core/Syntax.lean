import UFPL.Core.Types

namespace UFPL
namespace Core
open HList

/-- Terms (first‑order, multi‑sorted). -/
inductive Term : Ty → Type where
  | var   : (τ : Ty) → (name : String) → Term τ
  | const : (c : ConstSym) → Term c.τ
  | app   : (f : FuncSym) → HList (fun τ => Term τ) f.dom → Term f.cod
-- No `deriving Repr`: dependent fields break auto-deriving.

/-- UFPL formulas with modalities. -/
inductive Form : Type where
  | top    : Form | bot : Form
  | pred   : (p : PredSym) → HList (fun τ => Term τ) p.dom → Form
  | eq     : {τ : Ty} → Term τ → Term τ → Form
  | not    : Form → Form
  | and    : Form → Form → Form
  | or     : Form → Form → Form
  | imp    : Form → Form → Form
  | iff    : Form → Form → Form
  | forallE : (x : String) → (τ : Ty) → Form → Form
  | existsE : (x : String) → (τ : Ty) → Form → Form
  -- modal / epistemic / deontic / temporal
  | box    : Form → Form
  | dia    : Form → Form
  | knows  : Term Ty.agt → Form → Form
  | believes : Term Ty.agt → Form → Form
  | obl    : Form → Form
  | G      : Form → Form | F : Form → Form | H : Form → Form | P : Form → Form
-- No `deriving Repr` for the same reason.

namespace Form
  def perm (φ : Form) : Form := .not (.obl (.not φ))
  def forb (φ : Form) : Form := .obl (.not φ)
end Form

/-- Handy scoped notations for UFPL’s deep embedding. -/
scoped notation "□" φ => UFPL.Core.Form.box φ
scoped notation "◇" φ => UFPL.Core.Form.dia φ

end Core
end UFPL
