import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Root.Face

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth sourceStart prefixLimit renewalLimit : Nat}
  (datum : Macro.Ingress.Datum input depth sourceStart)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Context (input := input) (review := review)
    depth (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit
    depth (Macro.Ingress.cut input depth sourceStart)}
  {admission : InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : Macro.Runtime.actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
    .enacted origin admission frame)

local notation "count" => Macro.Ingress.cut input depth sourceStart
local notation "oldPast" => origin.germ.snapshot.past
local notation "priority" => Dividend.Financial.Preference.Renewal.select
  input depth count prefixLimit renewalLimit oldPast frame.snapshot

include selected

set_option maxHeartbeats 600000 in
theorem the_actual_boundary_executes_a_strict_full_account_extension_whenever_the_source_has_one
    (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance) :
    match priority with
    | .selected _preferred =>
        ∃ plan, Adaptive.compile input depth count prefixLimit renewalLimit oldPast frame.snapshot = .accepted plan ∧
          frame.next.snapshot = Dividend.Financial.Preference.Renewal.successor frame.snapshot plan.rawWord ∧
          frame.next.account = frame.account ∧
          Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit oldPast frame.snapshot
            (Adaptive.executable plan.rawWord) ∧
          Dividend.Financial.Checks input depth count prefixLimit renewalLimit oldPast frame.next.snapshot ∧
          ∃ checked, Dividend.Root.installedAssessment frame.next = .accepted checked
    | .noStrict _report =>
        ∀ word ∈ Adaptive.candidates input depth count prefixLimit renewalLimit oldPast frame.snapshot,
          ¬ Dividend.Financial.Preference.Renewal.Checks input depth count prefixLimit renewalLimit oldPast frame.snapshot word := by
  cases generated : priority with
  | selected preferred =>
      obtain ⟨plan, compiled, _same, strict⟩ := Adaptive.an_available_full_account_extension_is_the_actual_renewal_plan
        input depth count prefixLimit renewalLimit oldPast frame.snapshot preferred generated
      obtain ⟨actualPlan, actualSource, next, account⟩ :=
        Macro.Runtime.the_actual_complete_source_executes_the_selected_period datum reader frame tick selected complete automatic
          ⟨plan.rawWord, plan.generated, plan.checked⟩
      have same : actualPlan = plan := Adaptive.Outcome.accepted.inj (actualSource.symm.trans compiled)
      cases same
      have paid : Dividend.Financial.Checks input depth count prefixLimit renewalLimit oldPast frame.next.snapshot := by
        rw [next]
        exact strict
      exact ⟨plan, actualSource, next, account, plan.checked, paid,
        Dividend.Financial.a_real_full_account_gain_is_accepted input depth count prefixLimit renewalLimit oldPast frame.next.snapshot paid⟩
  | noStrict report =>
      exact Dividend.Financial.Preference.Renewal.no_strict_report_keeps_every_original_candidate_issue
        input depth count prefixLimit renewalLimit oldPast frame.snapshot report

#print axioms the_actual_boundary_executes_a_strict_full_account_extension_whenever_the_source_has_one

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future
