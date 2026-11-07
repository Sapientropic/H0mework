import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Receipt

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth sourceStart prefixLimit renewalLimit : Nat}
  (datum : Ingress.Datum input depth sourceStart)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart)}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
    .enacted origin admission frame)

def originalProposal := origin.reader frame.actual.readerCursor frame.account

include selected

theorem every_actual_public_proposal_is_the_current_source_selection :
    frame.actual.proposal frame.reader =
      Adaptive.selectedRaw input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot (originalProposal frame) := by
  have sourced := the_actual_public_reader_is_the_installed_source (review := review) input depth sourceStart datum
    prefixLimit renewalLimit reader tick origin admission frame selected
  change frame.reader frame.actual.readerCursor frame.account = _
  rw [sourced]
  exact Adaptive.the_reader_is_the_exact_current_source_selection input depth (Ingress.cut input depth sourceStart)
    prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot origin.reader frame.account

theorem every_available_automatic_source_word_is_actually_selected
    (automatic : originalProposal frame = .advance)
    (available : ∃ word ∈ Adaptive.candidates input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot,
      Adaptive.Checks input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot word) :
    ∃ plan, Adaptive.compile input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot =
        .accepted plan ∧ frame.actual.proposal frame.reader = .execute plan.rawWord ∧
      (Public.Scope.actualResult input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
        origin.germ.snapshot.past frame.snapshot (frame.actual.proposal frame.reader)).isAccepted = true := by
  obtain ⟨plan, generated⟩ := Adaptive.an_available_current_source_word_cannot_be_vetoed input depth
    (Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot available
  have proposal := every_actual_public_proposal_is_the_current_source_selection datum reader frame tick selected
  rw [automatic, Adaptive.selectedRaw, generated] at proposal
  refine ⟨plan, generated, proposal, ?_⟩
  rw [proposal]
  simp only [Public.Scope.actualResult, Public.Scope.selectedCursor]
  rw [Adaptive.the_selected_word_passes_the_actual_full_current_guard]
  exact Adaptive.the_actual_public_period_is_accepted input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
    origin.germ.snapshot.past frame.snapshot plan

theorem the_actual_complete_source_executes_the_selected_period
    (complete : ¬ frame.HasWork)
    (automatic : originalProposal frame = .advance)
    (available : ∃ word ∈ Adaptive.candidates input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot,
      Adaptive.Checks input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot word) :
    ∃ plan, Adaptive.compile input depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot =
        .accepted plan ∧
      frame.next.snapshot = Physical.next (Physical.receive frame.snapshot (.execute plan.rawWord)) ∧
      frame.next.account = frame.account := by
  obtain ⟨plan, generated, proposal, _⟩ :=
    every_available_automatic_source_word_is_actually_selected datum reader frame tick selected automatic available
  refine ⟨plan, generated, ?_, ?_⟩
  · rw [Public.Runtime.Frame.next, dif_neg complete]
    change Physical.next (Public.Scope.selectedCursor input depth (Ingress.cut input depth sourceStart)
      prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot (frame.actual.proposal frame.reader)) = _
    rw [proposal]
    simp only [Public.Scope.selectedCursor]
    rw [Adaptive.the_selected_word_passes_the_actual_full_current_guard]
  · rw [Public.Runtime.Frame.next, dif_neg complete]
    exact frame.raw_reentry_keeps_the_literal_complete_account complete

#print axioms every_actual_public_proposal_is_the_current_source_selection
#print axioms every_available_automatic_source_word_is_actually_selected
#print axioms the_actual_complete_source_executes_the_selected_period

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
