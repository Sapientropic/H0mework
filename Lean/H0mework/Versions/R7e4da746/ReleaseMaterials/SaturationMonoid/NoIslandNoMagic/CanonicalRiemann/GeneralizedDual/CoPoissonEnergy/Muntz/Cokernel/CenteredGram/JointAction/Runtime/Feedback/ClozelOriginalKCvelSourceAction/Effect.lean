import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Integral
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Residual
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
local notation "T" => burnolMeanZeroTruncatedFourier

def actualVelocityIntegralTail (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) : BurnolL2 :=
  actualDilationIntegral h (actualVelocityTail coordinate N) +
  actualDilationIntegral (-h) (actualVelocityTail coordinate N)

def actualVelocityIntegralPriceTail (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (test : BurnolL2) (actualVelocityIntegralTail coordinate h N)

theorem actual_velocity_integral_complete (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityIntegral coordinate h =
      actualVelocityIntegralStock coordinate h N + actualVelocityIntegralTail coordinate h N := by
  change actualDilationIntegral h (OriginalKBoundarySourceAction.Source.velocity coordinate) +
    actualDilationIntegral (-h) (OriginalKBoundarySourceAction.Source.velocity coordinate) = _
  rw [actual_velocity_stock_complete coordinate N]
  simp only [map_add,actualVelocityIntegralStock,actualVelocityIntegralTail]
  abel

theorem actual_velocity_price_complete (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) (N : ℕ) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice coordinate test h =
      actualVelocityIntegralPriceStock coordinate test h N + actualVelocityIntegralPriceTail coordinate test h N := by
  rw [← OriginalKBoundarySourceAction.actual_corrected_velocity_integral_price,
    actual_velocity_integral_complete,inner_add_right]
  rfl

private theorem source_extension_norm (state : BurnolQuarterMeanZeroCarrier) :
    ‖actualStockExtension state‖ = ‖state‖ := by
  change ‖burnolRadiusZeroExtension (1/4:ℝ) (state : BurnolQuarterIntervalL2)‖ = ‖state‖
  rw [← burnolRadiusZeroExtensionExplicit_is_adjoint]
  exact burnolRadiusZeroExtensionValue_norm (state : BurnolQuarterIntervalL2)

theorem actual_velocity_tail_bound (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    ‖actualVelocityTail coordinate N‖ ≤
      ((3/2:ℝ)*(‖Kernel.A coordinate‖+‖Kernel.beta coordinate‖)) *
        ((1/4:ℝ)^N*‖Response.u‖) := by
  have u := actual_source_tail_bound N
  have v := burnolMeanZeroTruncatedFourier_norm_le (actualSourceTail N)
  have stockbound : ‖actualStockExtension (actualSourceTail N)‖ ≤ (1/4:ℝ)^N*‖Response.u‖ :=
    (source_extension_norm _).le.trans u
  have vbound : ‖actualStockExtension (T (actualSourceTail N))‖ ≤
      (1/2:ℝ)*((1/4:ℝ)^N*‖Response.u‖) := by
    rw [source_extension_norm]
    exact v.trans (mul_le_mul_of_nonneg_left u (by norm_num))
  unfold actualVelocityTail
  dsimp only
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul]
  have first : ‖fourierL2 (actualStockExtension (actualSourceTail N)) -
      actualStockExtension (T (actualSourceTail N))‖ ≤
      (1/4:ℝ)^N*‖Response.u‖ + (1/2:ℝ)*((1/4:ℝ)^N*‖Response.u‖) := by
    apply (norm_sub_le _ _).trans
    rw [fourierL2.norm_map]
    exact add_le_add stockbound vbound
  have second : ‖actualStockExtension (actualSourceTail N) -
      fourierL2 (actualStockExtension (T (actualSourceTail N)))‖ ≤
      (1/4:ℝ)^N*‖Response.u‖ + (1/2:ℝ)*((1/4:ℝ)^N*‖Response.u‖) := by
    apply (norm_sub_le _ _).trans
    rw [fourierL2.norm_map]
    exact add_le_add stockbound vbound
  exact (add_le_add (mul_le_mul_of_nonneg_left first (norm_nonneg _))
    (mul_le_mul_of_nonneg_left second (norm_nonneg _))).trans_eq (by ring)

theorem actual_velocity_integral_tail_bound (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) :
    ‖actualVelocityIntegralTail coordinate h N‖ ≤
      (2*|h|) * (((3/2:ℝ)*(‖Kernel.A coordinate‖+‖Kernel.beta coordinate‖)) *
        ((1/4:ℝ)^N*‖Response.u‖)) := by
  unfold actualVelocityIntegralTail
  apply (norm_add_le _ _).trans
  have first := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := h) (C := ‖actualVelocityTail coordinate N‖)
    (fun t _ => le_of_eq ((burnolMultiplicativeDilation t).norm_map _))
  have second := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := -h) (C := ‖actualVelocityTail coordinate N‖)
    (fun t _ => le_of_eq ((burnolMultiplicativeDilation t).norm_map _))
  change ‖actualDilationIntegral h _‖ ≤ _ at first
  change ‖actualDilationIntegral (-h) _‖ ≤ _ at second
  simp only [sub_zero,abs_neg] at first second
  have pair := add_le_add first second
  have same : ‖actualVelocityTail coordinate N‖ * |h| + ‖actualVelocityTail coordinate N‖ * |h| =
      (2*|h|)*‖actualVelocityTail coordinate N‖ := by ring
  rw [same] at pair
  exact pair.trans (mul_le_mul_of_nonneg_left (actual_velocity_tail_bound coordinate N) (by positivity))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
