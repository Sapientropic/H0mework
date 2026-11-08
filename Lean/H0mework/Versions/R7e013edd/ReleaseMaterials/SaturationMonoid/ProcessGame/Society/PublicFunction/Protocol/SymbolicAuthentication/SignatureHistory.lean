import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureEligibility

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureHistory
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

def Quiet (past more : JointResponse.Stages model) : Prop :=
  ∀ n < more.length, SignatureEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = false

namespace Incident
open private register scan scan_append from H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse

theorem an_ineligible_slot_cannot_register_an_incident
    (past : JointResponse.Stages model) (stage : EventHistory.Stage (code := model.source.code))
    (quiet : SignatureEligibility.eligible model start vocabulary encoding law past = false) :
    IncidentResponse.journal model start (past ++ [stage]) vocabulary encoding law =
      IncidentResponse.journal model start past vocabulary encoding law := by
  unfold IncidentResponse.journal
  rw [scan_append]
  simp only [List.nil_append, scan]
  change register model start vocabulary encoding law past (IncidentResponse.journal model start past vocabulary encoding law) stage = _
  unfold register
  split
  · rename_i response selected
    have actual := SignatureEligibility.Incident.actual_ready_is_primitive model start vocabulary encoding law past response selected
    have yes : SignatureEligibility.eligible model start vocabulary encoding law past = true := by
      simp only [SignatureEligibility.eligible, actual, Bool.true_or]
    rw [quiet] at yes
    contradiction
  · rfl

end Incident

namespace Rejection
open private register scan scan_append from H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

theorem an_ineligible_slot_cannot_register_a_rejection
    (past : JointResponse.Stages model) (stage : EventHistory.Stage (code := model.source.code))
    (quiet : SignatureEligibility.eligible model start vocabulary encoding law past = false) :
    RejectionResponse.journal model start (past ++ [stage]) vocabulary encoding law =
      RejectionResponse.journal model start past vocabulary encoding law := by
  unfold RejectionResponse.journal
  rw [scan_append]
  simp only [List.nil_append, scan]
  change register model start vocabulary encoding law past (RejectionResponse.journal model start past vocabulary encoding law) stage = _
  unfold register
  split
  · rename_i response selected
    have actual := SignatureEligibility.Rejection.actual_ready_is_primitive model start vocabulary encoding law past response selected
    have yes : SignatureEligibility.eligible model start vocabulary encoding law past = true := by
      simp only [SignatureEligibility.eligible, actual, Bool.or_true]
    rw [quiet] at yes
    contradiction
  · rfl

end Rejection

theorem a_quiet_actual_extension_keeps_both_original_journals
    (past more : JointResponse.Stages model) (quiet : Quiet model start vocabulary encoding law past more) :
    IncidentResponse.journal model start (past ++ more) vocabulary encoding law = IncidentResponse.journal model start past vocabulary encoding law ∧
    RejectionResponse.journal model start (past ++ more) vocabulary encoding law = RejectionResponse.journal model start past vocabulary encoding law := by
  induction more generalizing past with
  | nil => simp only [List.append_nil, and_self]
  | cons stage tail ih =>
    have first : SignatureEligibility.eligible model start vocabulary encoding law past = false := by
      simpa only [List.take_zero, List.append_nil] using quiet 0 (by simp)
    have rest : Quiet model start vocabulary encoding law (past ++ [stage]) tail := by
      intro n inside
      simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using quiet (n + 1) (by simp; omega)
    have after := ih (past ++ [stage]) rest
    have one := Incident.an_ineligible_slot_cannot_register_an_incident model start vocabulary encoding law past stage first
    have two := Rejection.an_ineligible_slot_cannot_register_a_rejection model start vocabulary encoding law past stage first
    simpa only [List.append_assoc, List.singleton_append, one, two] using after

theorem the_first_unhandled_incident_survives_without_registration
    (past later : JointResponse.Stages model) (ordered : past <+: later)
    (head : StageAccountability.Incident start vocabulary encoding law)
    (first : (UnifiedResponse.incidents model start vocabulary encoding law past).head? = some head)
    (kept : IncidentResponse.journal model start later vocabulary encoding law = IncidentResponse.journal model start past vocabulary encoding law) :
    (UnifiedResponse.incidents model start vocabulary encoding law later).head? = some head := by
  obtain ⟨more, same⟩ := ordered
  unfold UnifiedResponse.incidents ResponseSweep.unhandled
  rw [kept, ← same, StageAccountability.ledger_extends_by_its_generated_next, List.filter_append]
  change ((UnifiedResponse.incidents model start vocabulary encoding law past) ++ _).head? = some head
  cases items : UnifiedResponse.incidents model start vocabulary encoding law past with
  | nil => rw [items] at first; cases first
  | cons top tail =>
    rw [items] at first
    exact first

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureHistory
