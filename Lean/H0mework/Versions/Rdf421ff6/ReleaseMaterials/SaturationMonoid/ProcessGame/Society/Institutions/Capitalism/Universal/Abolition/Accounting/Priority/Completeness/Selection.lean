import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness

open Source.Program Innovation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (proposal : RawEvent Party Good Port Technology Instrument)

/-- A resource producer supplies this permit downstream. The deterministic
source selector must then choose admission; no external chooser remains. -/
theorem a_generated_permit_forces_the_actual_selected_branch
    (permit : Selection.Permit claim state law members proposal) :
    ∃ selected, Selection.renewalVerdict claim state law members proposal = .admitted selected := by
  with_unfolding_all
    unfold Selection.renewalVerdict
    split
    next declared =>
      split
      next issue stopped =>
        have impossible := permit.noStop.symm.trans stopped
        cases impossible
      next stopped =>
        split
        next actor original unpaid selected => exact (unpaid (permit.needs actor original).1).elim
        next actor original unpaid selected => exact (unpaid (permit.needs actor original).2).elim
        next needs selected =>
          split
          next progress => exact ⟨permit,rfl⟩
          next noProgress => exact (noProgress permit.strictProgress).elim
    next undeclared => exact (undeclared permit.declared).elim

theorem an_actual_current_source_permit_cannot_be_ignored
    {oldN : WorldRelationNetwork}
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (permit : Selection.Permit claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal) : Root.Admitted claim frame proposal := by
  apply (Root.admitted_iff_the_original_source_verdict claim frame proposal).mpr
  obtain ⟨selected,actual⟩ := a_generated_permit_forces_the_actual_selected_branch claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members proposal permit
  rw [actual]
  trivial

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness
