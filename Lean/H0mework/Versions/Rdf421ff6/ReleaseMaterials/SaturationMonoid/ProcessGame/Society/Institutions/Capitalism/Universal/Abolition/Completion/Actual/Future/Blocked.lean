import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- Exhaustion is a precise source-domain obstruction. It cannot turn the
old automatic word into an unchecked paid period or advance its clock. -/
theorem source_exhaustion_cannot_advance_an_unpaid_material_period
    (obstruction : Adaptive.Obstruction input depth count prefixLimit renewalLimit oldPast current) :
    (Macro.Public.Scope.actualResult input depth count prefixLimit renewalLimit oldPast current .advance).next =
      Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current := by
  cases inspected : Macro.Public.Scope.inspect input depth count prefixLimit renewalLimit oldPast current .advance with
  | rejected failed =>
      exact (Macro.Public.Scope.an_actual_scope_rejection_cannot_advance_the_physical_current input depth count
        prefixLimit renewalLimit oldPast current .advance failed inspected).1
  | accepted word selected checked =>
      cases phase : (Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current).phase with
      | seeking =>
          simp only [Macro.Public.Scope.periodWord?, Physical.Public.wordAt, phase] at selected
          cases selected
      | renewal raw =>
          have same : Adaptive.executable raw = word := by
            change PublicPlan.executable raw = word
            unfold PublicPlan.executable
            simpa only [Macro.Public.Scope.periodWord?, Physical.Public.wordAt, phase, Option.some.injEq] using selected
          have original : raw ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current := by
            simp [Adaptive.candidates, Adaptive.inheritedWords, Adaptive.actualState, phase]
          have passed : Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current raw := by
            change Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit oldPast current (Adaptive.executable raw)
            rw [same]
            exact checked
          exact (obstruction.excluded raw original passed).elim
  | delegated absent =>
      have forwarded := (Macro.Public.Scope.every_nonperiod_proposal_keeps_its_actual_route input depth count
        prefixLimit renewalLimit oldPast current .advance absent).1
      unfold Macro.Public.Scope.actualResult Macro.Public.Scope.selectedCursor
      rw [forwarded]
      change Physical.Public.wordAt
        (Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current) .advance = none at absent
      cases result : Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast
        (Physical.receive current .advance) with
      | metadata _ => rfl
      | accepted word selected _ =>
          change Physical.Public.wordAt
            (Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current) .advance = some word at selected
          rw [absent] at selected
          cases selected
      | refused word selected _ _ _ =>
          change Physical.Public.wordAt
            (Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit oldPast current) .advance = some word at selected
          rw [absent] at selected
          cases selected

#print axioms source_exhaustion_cannot_advance_an_unpaid_material_period

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future
