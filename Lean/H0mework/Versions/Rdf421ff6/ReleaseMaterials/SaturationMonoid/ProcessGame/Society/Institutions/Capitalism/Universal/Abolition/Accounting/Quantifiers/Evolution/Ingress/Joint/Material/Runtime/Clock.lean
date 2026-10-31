import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Answer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private theorem sameTypedCurrent {N : WorldRelationNetwork}
    (left right : SourceNativeAuthoritativeRootCurrentAt N)
    (same : (⟨N,left⟩ : AnyAuthoritativeRootCurrent) = ⟨N,right⟩) : left = right :=
  eq_of_heq (AnyAuthoritativeRootCurrent.mk.inj same).2

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def roundAt (current : SourceNativeAuthoritativeRootCurrentAt (Admission.N seed claim)) : Nat :=
  match (current.root.toRoot.supportAt current.visit.current).2 with
  | none => 0
  | some shared => shared.raw.round

theorem the_native_root_coordinate_is_the_original_source_iteration (stages : Nat) :
    (visitAt seed claim stages).current = Drain.stateAt seed claim (stages + 1) := by
  induction stages with
  | zero => rfl
  | succ stages earlier =>
      change next seed claim (visitAt seed claim stages).current =
        (next seed claim)^[(stages + 1) + 1] (initial seed)
      rw [earlier,Function.iterate_succ_apply']
      rfl

theorem the_single_executed_body_is_retained_at_every_native_visit (stages : Nat) :
    sharedAt seed claim (visitAt seed claim stages).current = Planning.actualNext seed claim (Material.shared seed claim) := by
  induction stages with
  | zero => exact the_first_material_next_is_the_source_selected_actual_next seed claim
  | succ stages earlier =>
      change sharedAt seed claim (next seed claim (visitAt seed claim stages).current) = _
      have paid : (visitAt seed claim stages).current.bodyPaid = true := by
        rw [the_native_root_coordinate_is_the_original_source_iteration]
        exact Drain.every_positive_native_stage_has_already_paid_the_single_body seed claim stages
      exact (native_bookkeeping_keeps_the_already_executed_material_state seed claim _ paid).trans earlier

theorem source_round :
    roundAt seed claim (presentation seed claim).erase.current = (Material.shared seed claim).raw.round := by
  have same := Inquiry.the_initial_support_is_the_literal_original_declared_whole_account seed claim
  exact congrArg (fun support : (Admission.N seed claim).Support =>
    match support.2 with | none => 0 | some shared => shared.raw.round) same

theorem every_native_visit_retains_the_one_actual_new_round (stages : Nat) :
    roundAt seed claim (answerPresentation seed claim stages).erase.current =
      (Material.shared seed claim).raw.round + 1 := by
  change (sharedAt seed claim (visitAt seed claim stages).current).raw.round = _
  rw [the_single_executed_body_is_retained_at_every_native_visit]
  rfl

theorem source_ne_target (stages : Nat) :
    (presentation seed claim).erase ≠ (answerPresentation seed claim stages).erase := by
  intro same
  have typed := sameTypedCurrent _ _ same
  have rounds := congrArg (roundAt seed claim) typed
  change roundAt seed claim (presentation seed claim).erase.current =
    roundAt seed claim (answerPresentation seed claim stages).erase.current at rounds
  rw [source_round,every_native_visit_retains_the_one_actual_new_round] at rounds
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
