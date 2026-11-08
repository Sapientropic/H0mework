import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceWindow

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

def quiet : Rule model.source.code where
  work := ⟨fun _ _ => [], by
    apply model.source.code.every_local_policy_is_enumerated
    intro key inside
    exact (mem_words_iff _ _ _).mpr (by simp)⟩
  events := fun _ _ => ⟨none, List.mem_cons_self⟩

-- Each owned cut recompiles the existing local inquiry from its newly installed public prefix.
def rule (past : JointResponse.Stages model) : Rule model.source.code :=
  let cursor := EventHistory.execute start past
  match Distributed.Recall.Information.Agency.ownerAt model.source.code cursor.ownerStart
      (EventStep.seed cursor).history.length with
  | none => quiet model
  | some worker => WithdrawalInquiry.protocol model start (past.map Prod.fst) worker

def run (external : Opponent model.source.code) : Nat → JointResponse.Stages model → JointResponse.Stages model
  | 0, past => past
  | count + 1, past => run external count (past ++ [(rule model start past, external)])

def horizon (past : JointResponse.Stages model) :=
  min (2 * model.source.code.sites) (JointResponse.fuel model start past)
abbrev produce (past : JointResponse.Stages model) (external : Opponent model.source.code) :=
  run model start external (horizon model start past) past

theorem actual_window_keeps_every_original_stage (external : Opponent model.source.code)
    (count : Nat) (past : JointResponse.Stages model) : past <+: run model start external count past := by
  induction count generalizing past with
  | zero => exact List.prefix_refl _
  | succ count ih => exact (List.prefix_append _ _).trans (ih _)

theorem the_window_has_the_exact_generated_stage_count (external : Opponent model.source.code)
    (count : Nat) (past : JointResponse.Stages model) :
    (run model start external count past).length = past.length + count := by
  induction count generalizing past with
  | zero => simp only [run, Nat.add_zero]
  | succ count ih => simp only [run, ih, List.length_append, List.length_singleton]; omega

theorem the_actual_window_spends_exactly_its_stage_count (external : Opponent model.source.code)
    (count : Nat) (past : JointResponse.Stages model) :
    JointResponse.fuel model start (run model start external count past) =
      JointResponse.fuel model start past - count := by
  obtain ⟨tail, same⟩ := actual_window_keeps_every_original_stage model start external count past
  have length := the_window_has_the_exact_generated_stage_count model start external count past
  have tailLength : tail.length = count := by rw [← same, List.length_append] at length; omega
  have paid := UnifiedResponse.fuel_after_actual_extension model start past tail
  change JointResponse.fuel model start (past ++ tail) = JointResponse.fuel model start past - tail.length at paid
  rw [same, tailLength] at paid
  exact paid

theorem the_source_clock_pays_for_the_entire_window (past : JointResponse.Stages model)
    (external : Opponent model.source.code) :
    (produce model start past external).length - past.length ≤ JointResponse.fuel model start past ∧
      (produce model start past external).length - past.length ≤ 2 * model.source.code.sites := by
  simp only [produce, the_window_has_the_exact_generated_stage_count, Nat.add_sub_cancel_left]
  exact ⟨Nat.min_le_right _ _, Nat.min_le_left _ _⟩

theorem every_owned_cut_uses_its_own_fresh_local_inquiry (past : JointResponse.Stages model)
    (worker : Fin model.source.code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some worker) :
    rule model start past = WithdrawalInquiry.protocol model start (past.map Prod.fst) worker := by
  simp only [rule, owned]

inductive Result (past : JointResponse.Stages model) where
  | complete (closed : NativeReview.complete model start past = true)
  | exhausted (empty : JointResponse.fuel model start past = 0)
  | obstructed (reason : NativeRecoveryMaterial.Obstruction)
      (actual : NativeRecoveryMaterial.produce model start past = .blocked reason)
  | unresolved (material : NativeRecoveryMaterial.Ready model start past)
      (actual : NativeRecoveryMaterial.produce model start past = .ready material)

def inspect (past : JointResponse.Stages model) : Result model start past :=
  if closed : NativeReview.complete model start past = true then .complete closed else
  if empty : JointResponse.fuel model start past = 0 then .exhausted empty else
  match actual : NativeRecoveryMaterial.produce model start past with
  | .blocked reason => .obstructed reason actual
  | .ready material => .unresolved material actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceWindow
