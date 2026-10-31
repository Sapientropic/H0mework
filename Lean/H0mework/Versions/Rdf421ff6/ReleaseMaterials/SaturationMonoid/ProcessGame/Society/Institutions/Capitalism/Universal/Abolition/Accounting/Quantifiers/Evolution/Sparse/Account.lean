import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Installation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

theorem the_entire_original_support_is_literal :
    (Current.support claim (nextCurrent claim current word)).1 = (Current.support claim current).1 :=
  raw_next_retains_the_entire_original_support claim (Source.native claim current word) (executedWord claim current word)

theorem every_old_claim_is_literal :
    (Current.state claim (nextCurrent claim current word)).raw.claims = (Current.state claim current).raw.claims := by
  rw [next_reads_the_actual_gated_state]
  exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _

theorem no_original_harm_cell_is_refilled (key : Party × Good) :
    (Current.state claim (nextCurrent claim current word)).remaining key ≤ (Current.state claim current).remaining key := by
  rw [next_reads_the_actual_gated_state]
  exact Responsibility.Family.State.actual_advance_never_refills_any_original_cell _ _ _ _ _

theorem the_actual_raw_interpreter_is_executed :
    (Current.state claim (nextCurrent claim current word)).raw =
      current.actualLaw.next (Current.state claim current).raw (Gate.executableWord claim current word) := by
  rw [next_reads_the_actual_gated_state,Gate.executableWord_eq]
  exact Priority.Policy.evaluation_updates_the_original_physical_cursor claim (Current.state claim current)
    current.actualLaw current.members (Priority.Policy.evaluate claim (Current.state claim current) current.actualLaw current.members word)

theorem the_executed_inventory_is_actually_accepted :
    ∀ item ∈ current.actualLaw.rawItems (Current.state claim current).raw (Gate.executableWord claim current word),
      current.actualLaw.Valid item.before item.request := by
  rw [Gate.executableWord_eq]
  exact Priority.Policy.accepted_prefix_is_valid_in_the_original_inventory claim (Current.state claim current)
    current.actualLaw current.members (Priority.Policy.evaluate claim (Current.state claim current) current.actualLaw current.members word).accepted

theorem the_source_context_and_phase_are_preserved :
    (nextCurrent claim current word).actualLaw = current.actualLaw ∧
      (nextCurrent claim current word).members = current.members ∧
      (Current.state claim (nextCurrent claim current word)).declared = (Current.state claim current).declared := by
  refine ⟨rfl,rfl,?_⟩
  rw [next_reads_the_actual_gated_state]
  rfl

theorem the_paid_original_row_stays_paid
    (paid : Responsibility.Family.State.isPaid claim (Current.state claim current)) :
    Responsibility.Family.State.isPaid claim (Current.state claim (nextCurrent claim current word)) := by
  intro key original
  exact le_antisymm (by simpa only [paid key original] using no_original_harm_cell_is_refilled claim current word key)
    ((Current.state claim (nextCurrent claim current word)).nonnegative key)

def nextReplyFace : SourceNativeRootSemanticFaceAt (nextCurrent claim current word).root
    (nextCurrent claim current word).visit where
  projection := oldProjection claim (Source.native claim current word) (executedWord claim current word)
    (Source.replyFace claim current word).projection
  active := (Source.replyFace claim current word).active
  classifier_eq := (Source.replyFace claim current word).classifier_eq

theorem the_next_retains_the_original_refusal_and_need_bearers :
    HEq (nextReplyFace claim current word).rootRead (Source.readReply claim current word) := HEq.rfl

def nextHistoryFace : SourceNativeRootSemanticFaceAt (nextCurrent claim current word).root
    (nextCurrent claim current word).visit where
  projection := oldProjection claim (Source.native claim current word) (executedWord claim current word)
    (Source.historyFace claim current word).projection
  active := (Source.historyFace claim current word).active
  classifier_eq := (Source.historyFace claim current word).classifier_eq

theorem the_next_retains_the_original_registered_temporal_past :
    HEq (nextHistoryFace claim current word).rootRead
      (TemporalMemory.read current.root.toAuthoritativeRoot.toLedgerRoot current.visit) := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
