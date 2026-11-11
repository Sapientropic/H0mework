import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.FullUnit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorCoPoissonAction
open Complex Filter FourierTransform MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open BurnolPhysicalState.OriginalRieszSource
open OriginalKCoefficientBFiniteAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "μq" => (volume.restrict (symmetricInterval q))
local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def actualFourierMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolTruncatedFourier (sourceB c : Hq))

/-- Every inverse-sampling channel acts on the same original coefficient B source. -/
def arithmeticReturnKernel (h x t : ℝ) : ℂ :=
  ∑ n ∈ burnolReciprocalStepChannels (bandLower h) 4 x,
    (n : ℂ)⁻¹ * Constructor.phase (Real.exp (-h) * |x| / (n : ℝ)) t

def arithmeticReturnEcho (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  (Real.exp (-h/2) : ℂ) *
    ((∫ t : ℝ in symmetricInterval q, arithmeticReturnKernel h x t * (sourceB c : Hq) t) -
      actualFourierMean c *
        (∑ n ∈ burnolReciprocalStepChannels (bandLower h) 4 x, (n : ℂ)⁻¹)) -
    nativeNormalization c h 1

private theorem actual_return_integral (c : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    burnolRieszReturnRaw c frequency =
      (∫ t : ℝ in symmetricInterval q, Constructor.phase frequency t * (sourceB c : Hq) t) -
        actualFourierMean c := by
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw burnolRadiusTruncatedFourierRaw
    VectorFourier.fourierIntegral actualFourierMean Constructor.phase
  congr 1

private theorem channel_integrable (c : BurnolCompletedMellinCoordinate) (frequency : ℝ) :
    Integrable (fun t : ℝ => Constructor.phase frequency t * (sourceB c : Hq) t) μq := by
  have original := (Lp.memLp (sourceB c : Hq)).integrable (by norm_num)
  apply original.norm.mono'
  · exact (Constructor.phaseContinuous frequency).aestronglyMeasurable.mul
      original.aestronglyMeasurable
  · filter_upwards with t
    simp only [Constructor.phase, norm_mul, Circle.norm_coe, one_mul]
    exact le_rfl

/-- The second column's complete finite arithmetic output is generated from b alone. -/
theorem actual_return_echo (c : BurnolCompletedMellinCoordinate) (h x : ℝ) :
    integerEcho c h 1 x = arithmeticReturnEcho c h x := by
  let channels := burnolReciprocalStepChannels (bandLower h) 4 x
  have calculated : (∑ n ∈ channels, (n:ℂ)⁻¹ *
      burnolRieszReturnRaw c (Real.exp (-h)*|x|/(n:ℝ))) =
      (∫ t : ℝ in symmetricInterval q, arithmeticReturnKernel h x t * (sourceB c : Hq) t) -
        actualFourierMean c * (∑ n ∈ channels, (n:ℂ)⁻¹) := by
    simp_rw [actual_return_integral, mul_sub]
    rw [Finset.sum_sub_distrib, ←Finset.sum_mul]
    rw [show (∫ t : ℝ in symmetricInterval q, arithmeticReturnKernel h x t * (sourceB c : Hq) t) =
      ∑ n ∈ channels, (n:ℂ)⁻¹ *
        (∫ t : ℝ in symmetricInterval q,
          Constructor.phase (Real.exp (-h)*|x|/(n:ℝ)) t * (sourceB c : Hq) t) from ?_]
    ring
    simp only [arithmeticReturnKernel, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum channels (fun (n : ℕ) _ =>
      (channel_integrable c (Real.exp (-h)*|x|/(n:ℝ))).const_mul (n:ℂ)⁻¹)]
    exact Finset.sum_congr rfl (fun n _ => integral_const_mul _ _)
  change (Real.exp (-h/2):ℂ) * (∑ n ∈ channels, (n:ℂ)⁻¹ *
    burnolRieszReturnRaw c (Real.exp (-h)*|x|/(n:ℝ))) - nativeNormalization c h 1 = _
  rw [calculated]
  rfl

theorem actual_return_arithmetic_read (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    inner ℂ test (exteriorWave c h 1) =
      ∫ x : ℝ, inner ℂ (test x) (arithmeticReturnEcho c h x) := by
  rw [actual_integer_wave_read c h nonnegative 1 test]
  exact integral_congr_ae (Eventually.of_forall (fun x =>
    congrArg (inner ℂ (test x)) (actual_return_echo c h x)))

/-- Whole-axis arithmetic action keeps the actual unit rather than assigning Pa to full loss. -/
theorem full_loss_return_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    inner ℂ test (FullUnit.fullForward c h 1) =
      (∫ x : ℝ, inner ℂ (test x) (arithmeticReturnEcho c h x)) +
        centeringMean c h 1 * inner ℂ test ConstantForward.value := by
  rw [FullUnit.fullForward, inner_add_right, inner_smul_right,
    actual_return_arithmetic_read c h nonnegative test]

theorem full_loss_coefficient_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (test : BurnolL2) :
    inner ℂ test (FullUnit.fullForward c h 0) =
      (∫ x : ℝ, inner ℂ (test x) (integerEcho c h 0 x)) +
        centeringMean c h 0 * inner ℂ test ConstantForward.value := by
  rw [FullUnit.fullForward, inner_add_right, inner_smul_right,
    actual_integer_wave_read c h nonnegative 0 test]

/-- Original Xi-zero orthogonality consumes the exact single-B arithmetic kernel. -/
theorem original_single_B_arithmetic_equation (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (∫ x : ℝ, inner ℂ (sourceKernel c x) (arithmeticReturnEcho c h x)) -
      (∫ x : ℝ, inner ℂ (fourierL2 (sourceKernel c) x) (integerEcho c h 0 x)) = 0 := by
  simpa only [actual_return_echo] using original_integer_echo_balance c zero h nonnegative bounded

/-- The literal full-loss integer sequences compute the remaining original unit prices. -/
theorem actual_full_loss_signed_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Tendsto (fun N : ℕ =>
      inner ℂ (sourceKernel c) (FiniteForcing.source N (FullUnit.fullSource c h 1)) -
      inner ℂ (fourierL2 (sourceKernel c)) (FiniteForcing.source N (FullUnit.fullSource c h 0)))
      atTop (𝓝 (centeringMean c h 1 * inner ℂ (sourceKernel c) ConstantForward.value -
        centeringMean c h 0 * inner ℂ (fourierL2 (sourceKernel c)) ConstantForward.value)) := by
  have first : Continuous (fun value : BurnolL2 => inner ℂ (sourceKernel c) value) := by fun_prop
  have second : Continuous (fun value : BurnolL2 => inner ℂ (fourierL2 (sourceKernel c)) value) := by fun_prop
  have actual := ((first.tendsto (FullUnit.fullForward c h 1)).comp
    (FullUnit.full_forward_tendsto c h nonnegative 1)).sub
      ((second.tendsto (FullUnit.fullForward c h 0)).comp
        (FullUnit.full_forward_tendsto c h nonnegative 0))
  have computed : inner ℂ (sourceKernel c) (FullUnit.fullForward c h 1) -
      inner ℂ (fourierL2 (sourceKernel c)) (FullUnit.fullForward c h 0) =
      centeringMean c h 1 * inner ℂ (sourceKernel c) ConstantForward.value -
        centeringMean c h 0 * inner ℂ (fourierL2 (sourceKernel c)) ConstantForward.value := by
    rw [full_loss_return_price c h nonnegative, full_loss_coefficient_price c h nonnegative]
    linear_combination original_single_B_arithmetic_equation c zero h nonnegative bounded
  rwa [computed] at actual

end OriginalKExteriorCoPoissonAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
