import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialReentry
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open NativeMaterialPotentialSource

abbrev current (state : LiveRepaymentSource.Snapshot) := (EventStep.seed state.cursor).current
abbrev row (state : LiveRepaymentSource.Snapshot) (command : LiveRepaymentSource.Command state) :=
  LiveRepaymentSource.row state.emitter state.cursor command.enabled command.rival

theorem step_keeps_the_original_law_and_side (state : LiveRepaymentSource.Snapshot) (command : LiveRepaymentSource.Command state) :
    (LiveRepaymentSource.step state command).emitter.law = state.emitter.law ∧
      (LiveRepaymentSource.step state command).cursor.side = state.cursor.side := ⟨rfl,rfl⟩

theorem step_has_one_actual_material_account (state : LiveRepaymentSource.Snapshot) (command : LiveRepaymentSource.Command state)
    (same : state.emitter.law = law) (original : state.cursor.side = .original) :
    potential (current (LiveRepaymentSource.step state command)) + spent (StageTrace.items (row state command)) = potential (current state) := by
  have actual := NativeMaterialPotentialConsumer.every_actual_stage_retains_its_exact_original_material_balance
    (LiveRepaymentSource.code state.emitter state.cursor) same (LiveRepaymentSource.start state.emitter state.cursor)
    (AtomicWorkSource.protocol state.emitter (LiveRepaymentSource.batch state.emitter state.cursor)
      (LiveRepaymentSource.submit state.emitter state.cursor command.enabled)) command.rival
  change potential (current (LiveRepaymentSource.step state command)) + spent (StageTrace.items (row state command)) =
    potential (EventStep.seed (LiveRepaymentSource.start state.emitter state.cursor)).current at actual
  rw [LiveRepaymentSource.seed_is_the_same_actual_current state.emitter state.cursor original] at actual
  exact actual

theorem step_preserves_actual_nonnegative_stock (state : LiveRepaymentSource.Snapshot) (command : LiveRepaymentSource.Command state)
    (same : state.emitter.law = law) (original : state.cursor.side = .original)
    (stocks : ∀ party good, 0 ≤ (current state).stock party good) :
    ∀ party good, 0 ≤ (current (LiveRepaymentSource.step state command)).stock party good := by
  have prepared : ∀ party good, 0 ≤ (EventStep.seed (LiveRepaymentSource.start state.emitter state.cursor)).current.stock party good := by
    rw [LiveRepaymentSource.seed_is_the_same_actual_current state.emitter state.cursor original]
    exact stocks
  exact NativeMaterialPotentialConsumer.every_actual_next_preserves_nonnegative_stock
    (LiveRepaymentSource.code state.emitter state.cursor) same (LiveRepaymentSource.start state.emitter state.cursor)
    (AtomicWorkSource.protocol state.emitter (LiveRepaymentSource.batch state.emitter state.cursor)
      (LiveRepaymentSource.submit state.emitter state.cursor command.enabled)) command.rival prepared

variable (initial : LiveRepaymentSource.Snapshot) (control : LiveRepaymentSource.Controller)
def items : Nat → List (ExecutionItem Delegation.Funded.Party Repayment.Recovery.Good
    Delegation.Funded.Port (Mandate.State Delegation.Funded.Party Bool) Unit) :=
  Nat.rec [] fun count prior => prior ++
    StageTrace.items (row (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count)))

theorem every_generated_code_retains_the_original_material_law (count : Nat) :
    (LiveRepaymentSource.run initial control count).emitter.law = initial.emitter.law ∧
      (LiveRepaymentSource.run initial control count).cursor.side = initial.cursor.side := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    have step := step_keeps_the_original_law_and_side (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count))
    exact ⟨step.1.trans ih.1,step.2.trans ih.2⟩

theorem arbitrary_cross_code_controls_share_one_original_material_account
    (same : initial.emitter.law = law) (original : initial.cursor.side = .original) (count : Nat) :
    potential (current (LiveRepaymentSource.run initial control count)) + spent (items initial control count) = potential (current initial) := by
  induction count with
  | zero => simp [items,LiveRepaymentSource.run,spent]
  | succ count ih =>
    have provenance := every_generated_code_retains_the_original_material_law initial control count
    have actual := step_has_one_actual_material_account (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count))
      (provenance.1.trans same) (provenance.2.trans original)
    change potential (current (LiveRepaymentSource.run initial control (count+1))) +
      spent (StageTrace.items (row (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count)))) = _ at actual
    change potential (current (LiveRepaymentSource.run initial control (count+1))) +
      spent (items initial control count ++ StageTrace.items
        (row (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count)))) = _
    simp only [spent,List.map_append,List.sum_append]
    simp only [spent] at ih actual
    linarith

theorem no_control_or_code_expansion_refills_the_actual_stock_budget
    (same : initial.emitter.law = law) (original : initial.cursor.side = .original)
    (stocks : ∀ party good, 0 ≤ (current initial).stock party good) (count : Nat) :
    spent (items initial control count) ≤ potential (current initial) := by
  have nonnegative : ∀ count party good, 0 ≤ (current (LiveRepaymentSource.run initial control count)).stock party good := by
    intro count
    induction count with
    | zero => exact stocks
    | succ count ih =>
      have provenance := every_generated_code_retains_the_original_material_law initial control count
      exact step_preserves_actual_nonnegative_stock (LiveRepaymentSource.run initial control count) (control (LiveRepaymentSource.run initial control count))
        (provenance.1.trans same) (provenance.2.trans original) ih
  have account := arbitrary_cross_code_controls_share_one_original_material_account initial control same original count
  have remaining := nonnegative_potential _ (nonnegative count)
  linarith
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeMaterialPotentialReentry
