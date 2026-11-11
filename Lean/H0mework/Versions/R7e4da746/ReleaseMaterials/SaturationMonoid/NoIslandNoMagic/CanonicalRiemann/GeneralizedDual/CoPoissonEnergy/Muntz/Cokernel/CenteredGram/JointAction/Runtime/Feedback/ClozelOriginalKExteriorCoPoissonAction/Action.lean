import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKExteriorCoPoissonAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology

/-- The actual integer echo samples the original B column, not a target K or boundary. -/
def integerEcho (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) (x : ℝ) : ℂ :=
  (Real.exp (-h/2) : ℂ) *
    (∑ n ∈ burnolReciprocalStepChannels (bandLower h) 4 x,
      (n : ℂ)⁻¹ * sourceProfile c i (Real.exp (-h) * |x| / (n : ℝ))) -
    nativeNormalization c h i

def integerPrefixEcho (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (N : ℕ) (x : ℝ) : ℂ :=
  (Real.exp (-h/2) : ℂ) *
    (∑ n ∈ Prefix.prefixChannels (bandLower h) 4 N x,
      (n : ℂ)⁻¹ * sourceProfile c i (Real.exp (-h) * |x| / (n : ℝ))) -
    ∫ u : ℝ in Ioc (bandLower h) 4, if u * |x| < (N : ℝ) then positiveWeight c h i u else 0

private theorem integer_channel (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (n : ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    positiveWeight c h i ((n : ℝ)/|x|) * ((|x| : ℝ) : ℂ)⁻¹ =
      (Real.exp (-h/2) : ℂ) * ((n : ℂ)⁻¹ *
        sourceProfile c i (Real.exp (-h) * |x| / (n : ℝ))) := by
  simp only [positiveWeight, reciprocalWeight, neg_mul, neg_neg, div_div_eq_mul_div,
    Complex.ofReal_div, Complex.ofReal_natCast, inv_div]
  have nonzeroCast : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr nonzero).ne'
  field_simp

private theorem integer_sum (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (channels : Finset ℕ) (x : ℝ) (nonzero : x ≠ 0) :
    (∑ n ∈ channels, positiveWeight c h i ((n:ℝ)/|x|)) * ((|x| : ℝ) : ℂ)⁻¹ =
      (Real.exp (-h/2) : ℂ) * (∑ n ∈ channels,
        (n:ℂ)⁻¹ * sourceProfile c i (Real.exp (-h) * |x| / (n:ℝ))) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _ => integer_channel c h i n x nonzero)

theorem actual_integer_echo (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2)
    (x : ℝ) (nonzero : x ≠ 0) :
    Arithmetic.weightedCountingRaw (bandLower h) 4 (positiveWeight c h i) x =
      integerEcho c h i x := by
  unfold Arithmetic.weightedCountingRaw integerEcho nativeNormalization
  rw [integer_sum c h i _ x nonzero]

theorem actual_integer_prefix (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (N : ℕ) :
    (exteriorPrefix c h i N : ℝ → ℂ) =ᵐ[volume] integerPrefixEcho c h i N := by
  filter_upwards [exterior_prefix_arithmetic c h nonnegative i N, volume.ae_ne (0:ℝ)]
    with x read nonzero
  rw [read]
  unfold weightedPrefixRaw integerPrefixEcho
  rw [integer_sum c h i _ x nonzero]

theorem actual_integer_wave_read (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (i : Fin 2) (test : BurnolL2) :
    inner ℂ test (exteriorWave c h i) =
      ∫ x : ℝ, inner ℂ (test x) (integerEcho c h i x) := by
  rw [exterior_wave_arithmetic_read c h nonnegative i test]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0:ℝ)] with x nonzero
  rw [actual_integer_echo c h i x nonzero]

/-- Only the arithmetic outputs are Pa; the original exterior inputs are retained. -/
def paArithmeticWord (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  -(1/2 : ℂ) • (exteriorWave c h 1 - fourierL2 (exteriorWave c h 0))

def arithmeticCoreRemainder (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (elementarySource c) - (1/2 : ℂ) •
    ((exteriorSource c h 1 - exteriorWave c h 1) -
      fourierL2 (exteriorSource c h 0 - exteriorWave c h 0) +
      centeringMean c h 1 • ConstantDual.seed -
      centeringMean c h 0 • fourierL2 ConstantDual.seed)

theorem source_core_arithmetic_split (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) :
    sourceCore c h = arithmeticCoreRemainder c h + paArithmeticWord c h := by
  rw [actual_core_source_action c h nonnegative]
  simp only [arithmeticCoreRemainder, paArithmeticWord, map_sub]
  module

theorem arithmetic_word_inPa (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    paArithmeticWord c h ∈ burnolOriginalPaInL2 :=
  burnolOriginalPaInL2.smul_mem _ (burnolOriginalPaInL2.sub_mem
    (exterior_wave_inPa c h nonnegative bounded 1)
    (burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nonnegative bounded 0)))

private theorem K_pa_read (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (value : BurnolL2) (member : value ∈ burnolOriginalPaInL2) :
    inner ℂ (sourceKernel c) value = 0 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have read := (burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp
    orthogonal physical inPa
  change inner ℂ (physical : BurnolL2) (burnolCompletedMellinRieszVector c : BurnolL2) = 0 at read
  change (physical : BurnolL2) = value at actual
  rw [actual] at read
  rw [sourceKernel_original, ← inner_conj_symm, read, map_zero]

theorem original_core_arithmetic_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (sourceKernel c) (sourceCore c h) =
      inner ℂ (sourceKernel c) (arithmeticCoreRemainder c h) := by
  rw [source_core_arithmetic_split c h nonnegative, inner_add_right,
    K_pa_read c zero _ (arithmetic_word_inPa c h nonnegative bounded), add_zero]

theorem original_fixedResidual_arithmetic_cotest (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (fixed : h = Real.log stageZeroSonineQ) :
    burnolPaFixedShiftResidual c zero = -inner ℂ (sourceKernel c) (arithmeticCoreRemainder c h) := by
  rw [original_fixedResidual_core c zero h nonnegative fixed,
    original_core_arithmetic_cotest c zero h nonnegative bounded]

/-- The same original K consumes the complete integer echoes with their own normalization. -/
theorem original_integer_echo_balance (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (∫ x : ℝ, inner ℂ (sourceKernel c x) (integerEcho c h 1 x)) -
      (∫ x : ℝ, inner ℂ (fourierL2 (sourceKernel c) x) (integerEcho c h 0 x)) = 0 := by
  have first := K_pa_read c zero _ (exterior_wave_inPa c h nonnegative bounded 1)
  have second := K_pa_read c zero _
    (burnolOriginalPaInL2_fourier (exterior_wave_inPa c h nonnegative bounded 0))
  have evenK : fourierL2 (fourierL2 (sourceKernel c)) = sourceKernel c := by
    rw [sourceKernel_original, fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have fourierRead := fourierL2.inner_map_map (fourierL2 (sourceKernel c)) (exteriorWave c h 0)
  rw [evenK] at fourierRead
  rw [← actual_integer_wave_read c h nonnegative 1 (sourceKernel c),
    ← actual_integer_wave_read c h nonnegative 0 (fourierL2 (sourceKernel c)), first,
    ← fourierRead, second, sub_self]

end OriginalKExteriorCoPoissonAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
