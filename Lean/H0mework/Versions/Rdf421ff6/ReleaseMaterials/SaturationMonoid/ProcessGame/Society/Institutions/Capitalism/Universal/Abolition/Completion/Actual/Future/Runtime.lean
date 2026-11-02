import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future.Blocked
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Adaptive

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
local notation "outcome" => Adaptive.compile input depth count prefixLimit renewalLimit oldPast frame.snapshot

include selected

set_option maxHeartbeats 600000 in
theorem every_actual_automatic_boundary_generates_paid_life_or_a_visible_unpaid_obstruction
    (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance) :
    match outcome with
    | .accepted plan =>
        frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.execute plan.rawWord)) ∧
        frame.next.account = frame.account ∧
        Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit oldPast frame.snapshot
          (Adaptive.executable plan.rawWord) ∧
        ∀ person ∈ Epoch.Interface.Actors.PublicCensus.parties input depth count prefixLimit renewalLimit oldPast frame.snapshot,
          Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
            (Adaptive.actualState input depth count prefixLimit renewalLimit oldPast frame.snapshot).raw
            (Adaptive.executable plan.rawWord) person
            (input.law.necessities (Adaptive.actualState input depth count prefixLimit renewalLimit oldPast frame.snapshot).raw person) .necessity ∧
          Exit.Necessity.BundlePaid (Physical.Public.interpreter input)
            (Adaptive.actualState input depth count prefixLimit renewalLimit oldPast frame.snapshot).raw
            (Adaptive.executable plan.rawWord) person
            (input.law.mandatoryMaintenance (Adaptive.actualState input depth count prefixLimit renewalLimit oldPast frame.snapshot).raw person) .maintenance
    | .obstructed obstruction =>
        Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast frame.next.snapshot.past =
          Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast frame.snapshot.past ∧
        HEq (Macro.Public.Inquiry.rawCore origin admission frame.source frame.reader (.finite frame.visit)
          frame.actual frame.authority complete).receipt.2.down
          (Adaptive.Outcome.obstructed obstruction) := by
  cases generated : outcome with
  | accepted plan =>
      obtain ⟨actualPlan, actualSource, next, account⟩ :=
        Macro.Runtime.the_actual_complete_source_executes_the_selected_period datum reader frame tick selected complete automatic
          ⟨plan.rawWord, plan.generated, plan.checked⟩
      have same : actualPlan = plan := Adaptive.Outcome.accepted.inj (actualSource.symm.trans generated)
      cases same
      exact ⟨next, account, plan.checked, fun person present => Adaptive.the_selected_word_pays_every_current_member
        input depth count prefixLimit renewalLimit oldPast frame.snapshot plan person present⟩
  | obstructed obstruction =>
      have proposal := Macro.Runtime.every_actual_public_proposal_is_the_current_source_selection datum reader frame tick selected
      rw [automatic, Adaptive.selectedRaw, generated] at proposal
      constructor
      · rw [Macro.Public.Runtime.Frame.next, dif_neg complete]
        change Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast
          (Physical.next (Macro.Public.Scope.selectedCursor input depth count prefixLimit renewalLimit oldPast
            frame.snapshot (frame.actual.proposal frame.reader))).past = _
        rw [proposal]
        exact (Physical.Public.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit oldPast
          (Macro.Public.Scope.selectedCursor input depth count prefixLimit renewalLimit oldPast frame.snapshot .advance)).trans
          (source_exhaustion_cannot_advance_an_unpaid_material_period input depth count prefixLimit renewalLimit
            oldPast frame.snapshot obstruction)
      · change HEq (Adaptive.report input depth count prefixLimit renewalLimit oldPast frame.snapshot
          (Macro.Runtime.originalProposal frame)) (Adaptive.Outcome.obstructed obstruction)
        rw [automatic]
        change HEq outcome (Adaptive.Outcome.obstructed obstruction)
        rw [generated]

#print axioms every_actual_automatic_boundary_generates_paid_life_or_a_visible_unpaid_obstruction

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Future
