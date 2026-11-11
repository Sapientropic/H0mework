import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "T2" => burnolMeanZeroTruncatedFourierSquare

/-- The error norm belongs to this source correction action; it supplies no physical positivity margin. -/
theorem actual_correction_source_tail_bound (value : BurnolL2) (N : ℕ) :
    ‖actualFirstCorrectionTail value N‖ ≤ (1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖ ∧
    ‖actualSecondCorrectionTail value N‖ ≤ (1/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖) := by
  have qnorm : ‖T2‖ ≤ (1/4:ℝ) := by
    apply (ContinuousLinearMap.opNorm_comp_le T T).trans
    exact (mul_le_mul burnolMeanZeroTruncatedFourier_opNorm_le_half
      burnolMeanZeroTruncatedFourier_opNorm_le_half (norm_nonneg T) (by norm_num : 0 ≤ (1/2:ℝ))).trans_eq (by norm_num)
  have first : ‖actualFirstCorrectionTail value N‖ ≤ (1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖ := by
    cases N with
    | zero => simp [actualFirstCorrectionTail]
    | succ n =>
      exact ((T2^(n+1)).le_opNorm (burnolAmbientMeanZeroFirstCorrection value)).trans
        (mul_le_mul_of_nonneg_right ((norm_pow_le' T2 (Nat.succ_pos n)).trans
          (pow_le_pow_left₀ (norm_nonneg T2) qnorm (n+1))) (norm_nonneg _))
  refine ⟨first,?_⟩
  unfold actualSecondCorrectionTail
  rw [norm_neg]
  exact (burnolMeanZeroTruncatedFourier_norm_le _).trans
    (mul_le_mul_of_nonneg_left first (by norm_num))

private theorem extension_norm (state : BurnolQuarterMeanZeroCarrier) :
    ‖burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2)‖ = ‖state‖ := by
  change ‖burnolRadiusZeroExtension (1/4:ℝ) (state : BurnolQuarterIntervalL2)‖ = ‖state‖
  rw [← burnolRadiusZeroExtensionExplicit_is_adjoint]
  exact burnolRadiusZeroExtensionValue_norm (state : BurnolQuarterIntervalL2)

private theorem even_part_norm_le (value : BurnolL2) : ‖burnolAmbientEvenPart value‖ ≤ ‖value‖ := by
  unfold burnolAmbientEvenPart
  rw [norm_smul]
  have normhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [normhalf]
  have bound := norm_add_le value (reflectL2 value)
  rw [reflectL2.norm_map] at bound
  linarith

theorem actual_physical_correction_tail_bound (value : BurnolL2) (N : ℕ) :
    ‖actualPhysicalCorrectionTail value N‖ ≤
      (3/2:ℝ)*((1/4:ℝ)^N * ‖burnolAmbientMeanZeroFirstCorrection value‖) := by
  have source := actual_correction_source_tail_bound value N
  unfold actualPhysicalCorrectionTail
  apply (even_part_norm_le _).trans
  apply (norm_add_le _ _).trans
  rw [extension_norm,fourierL2.norm_map,extension_norm]
  exact (add_le_add source.1 source.2).trans_eq (by ring)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
