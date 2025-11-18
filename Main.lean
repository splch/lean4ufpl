import UFPL.Examples.Trolley
import UFPL.Examples.NecIdentity

open UFPL
open UFPL.Examples

def main : IO Unit := do
  IO.println "UFPL demo:"
  IO.println s!"  Facts□@w0 (Bool):          {FactsNecAtW0B}"
  IO.println s!"  LesserEvil@w0 (Bool):      {LesserEvilAtW0B}"
  IO.println s!"  ObligationToDivert (Bool): {ObligationToDivertB}"
  IO.println "  Necessity of identity theorem compiled (see Examples/NecIdentity.lean)."
