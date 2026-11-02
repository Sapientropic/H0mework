import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionEnvelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionQuorum

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation AdmissionCode

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := lift base)) (law : StageReception.Law (lift base))

theorem an_issued_prefix_remains_in_every_actual_extension
    (cursor : Cursor (lift base)) (pastStages future : List (EventHistory.Stage (code := lift base)))
    (body : StageBudget.Ballot (code := lift base))
    (inside : body ∈ StageBudget.ledger vocabulary cursor pastStages) :
    body ∈ StageBudget.ledger vocabulary cursor (pastStages ++ future) := by
  induction pastStages generalizing cursor with
  | nil => simp [StageBudget.ledger, StageTrace.records] at inside
  | cons stage tail ih =>
    rcases stage with ⟨protocol, rival⟩
    change body ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) tail at inside
    change body ∈ StageTransport.ballots vocabulary (StageTrace.material cursor protocol rival) ++
      StageBudget.ledger vocabulary (cursor.after protocol rival) (tail ++ future)
    rcases List.mem_append.mp inside with now | later
    · exact List.mem_append_left _ now
    · exact List.mem_append_right _ (ih (cursor.after protocol rival) later)

/-- Only the completed prefix is supplied. Its safety envelope was already installed at genesis. -/
def produce (cursor : Cursor (lift base)) (pastStages : List (EventHistory.Stage (code := lift base)))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) : Quorum.ReadoutData Bool :=
  if base.sites + budget base < threshold + threshold then
    StageQuorum.readout (StageReception.run vocabulary encoding law cursor pastStages receiver pastStages.length) scope threshold
  else .blocked

theorem a_produced_decision_has_an_admitted_budget_and_actual_received_quorum
    (cursor : Cursor (lift base)) (pastStages : List (EventHistory.Stage (code := lift base)))
    (receiver : Fin base.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (decided : produce base vocabulary encoding law cursor pastStages receiver scope threshold = .decided value) :
    base.sites + budget base < threshold + threshold ∧
      StageQuorum.readout (StageReception.run vocabulary encoding law cursor pastStages receiver pastStages.length) scope threshold = .decided value ∧
      0 < threshold ∧ threshold ≤ (StageQuorum.support
        (StageReception.run vocabulary encoding law cursor pastStages receiver pastStages.length) scope value).card := by
  unfold produce at decided
  split at decided <;> try contradiction
  rename_i admitted
  exact ⟨admitted, decided, StageQuorum.decided_has_positive_quorum _ scope threshold value decided⟩

theorem conflicting_support_across_actual_prefixes_exposes_an_admitted_key
    (cursor : Cursor (lift base)) (pastStages future : List (EventHistory.Stage (code := lift base)))
    (left right : Fin base.sites) (scope : Scope) (a b : Bool) (different : a ≠ b) :
    StageQuorum.support (StageReception.run vocabulary encoding law cursor pastStages left pastStages.length) scope a ∩
      StageQuorum.support (StageReception.run vocabulary encoding law cursor (pastStages ++ future) right (pastStages ++ future).length) scope b ⊆
        affected base := by
  intro key inside
  obtain ⟨one, first, _, value₁, key₁⟩ := (StageQuorum.mem_support_iff _ scope a key).mp (Finset.mem_inter.mp inside).1
  obtain ⟨two, second, _, value₂, key₂⟩ := (StageQuorum.mem_support_iff _ scope b key).mp (Finset.mem_inter.mp inside).2
  have origin₁ := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor pastStages left pastStages.length one first
  have origin₂ := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor (pastStages ++ future) right (pastStages ++ future).length two second
  rw [← key₁]
  apply AdmissionEnvelope.every_actual_equivocator_is_in_the_genesis_admission_budget base vocabulary cursor (pastStages ++ future)
    one.wire.ballot two.wire.ballot (an_issued_prefix_remains_in_every_actual_extension base vocabulary cursor pastStages future _ origin₁)
    origin₂ (key₁.trans key₂.symm)
  intro same
  exact different (value₁.symm.trans (same.trans value₂))

theorem produced_decisions_agree_across_every_actual_extension
    (cursor : Cursor (lift base)) (pastStages future : List (EventHistory.Stage (code := lift base)))
    (left right : Fin base.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce base vocabulary encoding law cursor pastStages left scope threshold = .decided a)
    (two : produce base vocabulary encoding law cursor (pastStages ++ future) right scope threshold = .decided b) : a = b := by
  by_contra different
  have first := a_produced_decision_has_an_admitted_budget_and_actual_received_quorum base vocabulary encoding law cursor pastStages left scope threshold a one
  have second := a_produced_decision_has_an_admitted_budget_and_actual_received_quorum base vocabulary encoding law cursor (pastStages ++ future) right scope threshold b two
  have exposed := Finset.card_le_card (conflicting_support_across_actual_prefixes_exposes_an_admitted_key
    base vocabulary encoding law cursor pastStages future left right scope a b different)
  have unionBound : (StageQuorum.support (StageReception.run vocabulary encoding law cursor pastStages left pastStages.length) scope a ∪
      StageQuorum.support (StageReception.run vocabulary encoding law cursor (pastStages ++ future) right (pastStages ++ future).length) scope b).card ≤ base.sites := by
    simpa only [Fintype.card_fin] using
      (StageQuorum.support (StageReception.run vocabulary encoding law cursor pastStages left pastStages.length) scope a ∪
        StageQuorum.support (StageReception.run vocabulary encoding law cursor (pastStages ++ future) right (pastStages ++ future).length) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (StageQuorum.support (StageReception.run vocabulary encoding law cursor pastStages left pastStages.length) scope a)
    (StageQuorum.support (StageReception.run vocabulary encoding law cursor (pastStages ++ future) right (pastStages ++ future).length) scope b)
  dsimp only [budget] at first
  omega

theorem produced_decisions_agree
    (cursor : Cursor (lift base)) (stages : List (EventHistory.Stage (code := lift base)))
    (left right : Fin base.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce base vocabulary encoding law cursor stages left scope threshold = .decided a)
    (two : produce base vocabulary encoding law cursor stages right scope threshold = .decided b) : a = b := by
  exact produced_decisions_agree_across_every_actual_extension base vocabulary encoding law cursor stages [] left right scope threshold a b one
    (by simpa only [List.append_nil] using two)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionQuorum
