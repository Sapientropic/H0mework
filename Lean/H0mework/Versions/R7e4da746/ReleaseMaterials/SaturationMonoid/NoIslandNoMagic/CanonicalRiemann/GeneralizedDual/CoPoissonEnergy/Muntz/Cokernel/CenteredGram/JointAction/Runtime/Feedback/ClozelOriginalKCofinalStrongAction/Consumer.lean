import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalStrongAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalStrongAction
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- A supplied equation recognizes a candidate; it does not construct the source occurrence.
theorem actual_source_equation_unique (ordinal : Nat) (candidate : BurnolL2)
    (equation : HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation (-shift / 2) candidate)
      ((observation.coordinate / 2 - 1 / 4) • candidate +
        D.raw observation nontrivial half depth ordinal) 0) :
    candidate = D.raw observation nontrivial half depth (ordinal + 1) := by
  rw [D.raw_successor, Paid.original_R_direct]
  exact burnolDirectRightResolvent_of_strongEquation (observation.coordinate / 2)
    (Paid.parameter_rightQuarter observation half) _ candidate equation

theorem actual_predecessor_unique (ordinal : Nat) (candidate : BurnolL2)
    (equation : HasDerivAt (fun shift : ℝ => burnolMultiplicativeDilation (-shift / 2)
      (D.raw observation nontrivial half depth (ordinal + 1)))
      ((observation.coordinate / 2 - 1 / 4) • D.raw observation nontrivial half depth (ordinal + 1) +
        candidate) 0) :
    candidate = D.raw observation nontrivial half depth ordinal := by
  have velocity := equation.unique (actual_source_strong observation nontrivial half depth ordinal)
  exact add_left_cancel velocity

theorem consume_actual_strong_source (ordinal steps : Nat) (shift : ℝ)
    (history : List PUnit.{1}) (target : Nat) :
    type_of% (D.raw_xi_source observation nontrivial half depth ordinal) ∧
    type_of% (Paid.actual_source_gap observation nontrivial half depth ordinal) ∧
    type_of% (D.next_pair observation nontrivial half depth ordinal) ∧
    type_of% (actual_source_boundary observation nontrivial half depth ordinal shift) ∧
    type_of% (actual_source_strong observation nontrivial half depth ordinal) ∧
    type_of% (actual_pair_source_recovery observation nontrivial half depth ordinal) ∧
    type_of% (actual_source_backward observation nontrivial half depth ordinal steps) ∧
    type_of% (OriginalKCombCofinalPaAction.actual_complete_reconstruction observation nontrivial half depth ordinal) ∧
    type_of% (actual_source_packet_index observation nontrivial half depth ordinal) ∧
    type_of% (actual_source_whole observation nontrivial half depth ordinal) ∧
    type_of% (D.full_history observation nontrivial half depth (ordinal + 1)) ∧
    type_of% (RC.original_compiles (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
      (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)) ∧
    type_of% (RC.original_whole (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
      (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)) ∧
    type_of% (RC.actual_generated_current (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
      (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)) ∧
    type_of% (RC.rooted_material_source (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
      (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)) ∧
    type_of% (D.original_root_future observation nontrivial half depth (ordinal + 1) history target) := by
  apply RC.actual_root_eliminate (D.factory observation nontrivial half) (D.initial observation nontrivial half depth)
    (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)
  intro request model compiles whole
  exact ⟨D.raw_xi_source _ _ _ _ _, Paid.actual_source_gap _ _ _ _ _, D.next_pair _ _ _ _ _,
    actual_source_boundary _ _ _ _ _ _, actual_source_strong _ _ _ _ _,
    actual_pair_source_recovery _ _ _ _ _, actual_source_backward _ _ _ _ _ _,
    OriginalKCombCofinalPaAction.actual_complete_reconstruction _ _ _ _ _,
    actual_source_packet_index _ _ _ _ _, actual_source_whole _ _ _ _ _, D.full_history _ _ _ _ _,
    compiles, whole, RC.actual_generated_current _ _ _ _ _, RC.rooted_material_source _ _ _ _ _,
    D.original_root_future _ _ _ _ _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalStrongAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
