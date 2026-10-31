import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Access
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Reciprocity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.Disposal

/-! Source-native detection takes the raw current and finite emitted word.
No relation, witness path, future family or desired verdict is an input.
A failed search is explicitly inconclusive, never a no-capitalism result. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

private def firstSome {α β : Type u} (produce : α → Option β) : List α → Option β
  | [] => none
  | head :: tail => match produce head with
    | some value => some value
    | none => firstSome produce tail

def detect : Option (CapitalRelationKernel law current word) :=
  firstSome (fun access =>
    if access.Checks law current word then
      firstSome (fun reciprocity =>
        firstSome (fun disposal => Kernel.compile law current word ⟨access, reciprocity, disposal⟩)
          (disposals law current word access))
        (reciprocities law current word access)
    else none) (accesses law current word)

#print axioms detect

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery
