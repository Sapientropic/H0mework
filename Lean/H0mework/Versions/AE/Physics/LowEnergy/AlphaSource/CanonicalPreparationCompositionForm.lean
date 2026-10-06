import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionWeightedPairs
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionBounded
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder PreparationVacuumWeylDomain
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal InnerProductSpace
attribute [local irreducible] actualFullCompositionKernelDefect

abbrev pairVolume : Measure (PhysicalMomentum × PhysicalMomentum) := volume.prod volume

def leftFactor (g : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  Real.sqrt (kernelWeight xy) * ‖g xy.1‖
def rightFactor (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  Real.sqrt (kernelWeight xy) * ‖f xy.2‖

theorem leftFactor_square (g : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    leftFactor g xy ^ 2 = leftSquare g xy := by
  simp only [leftFactor, leftSquare, mul_pow, Real.sq_sqrt (kernelWeight_nonnegative xy)]
theorem rightFactor_square (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    rightFactor f xy ^ 2 = rightSquare f xy := by
  simp only [rightFactor, rightSquare, mul_pow, Real.sq_sqrt (kernelWeight_nonnegative xy)]

theorem leftFactor_memLp (g : FourierHilbert) : MemLp (leftFactor g) 2 pairVolume := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_sqrt.comp_stronglyMeasurable kernelWeight_measurable).mul
      ((Lp.stronglyMeasurable g).comp_measurable measurable_fst).norm).aestronglyMeasurable).mpr
  change Integrable (fun xy => leftFactor g xy ^ 2) pairVolume
  simpa only [leftFactor_square] using leftSquare_integrable g

theorem rightFactor_memLp (f : FourierHilbert) : MemLp (rightFactor f) 2 pairVolume := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_sqrt.comp_stronglyMeasurable kernelWeight_measurable).mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd).norm).aestronglyMeasurable).mpr
  change Integrable (fun xy => rightFactor f xy ^ 2) pairVolume
  simpa only [rightFactor_square] using rightSquare_integrable f

def normPair (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  ‖g xy.1‖ * kernelWeight xy * ‖f xy.2‖

theorem normPair_factors (g f : FourierHilbert) :
    normPair g f = fun xy => leftFactor g xy * rightFactor f xy := by
  funext xy
  have h := Real.sq_sqrt (kernelWeight_nonnegative xy)
  dsimp [normPair, leftFactor, rightFactor]
  symm
  calc
    _ = (Real.sqrt (kernelWeight xy)) ^ 2 * (‖g xy.1‖ * ‖f xy.2‖) := by ring
    _ = _ := by rw [h]; ring

theorem normPair_integrable (g f : FourierHilbert) : Integrable (normPair g f) pairVolume := by
  rw [normPair_factors]
  exact (leftFactor_memLp g).integrable_mul (rightFactor_memLp f)

theorem realLp_square_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp ℝ 2 μ) : (∫ x, u x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp [pow_two]

theorem originalLp_square_integral (f : FourierHilbert) :
    (∫ x : PhysicalMomentum, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [L2.inner_def, ← integral_re (𝕜 := ℂ) (L2.integrable_inner f f)] at h
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using h

theorem factorLp_square_integral (g : FourierHilbert) :
    ‖(leftFactor_memLp g).toLp (leftFactor g)‖ ^ 2 =
      ∫ xy, leftSquare g xy ∂pairVolume := by
  rw [← realLp_square_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (leftFactor_memLp g)] with xy hxy
  rw [hxy, leftFactor_square]

theorem rightFactorLp_square_integral (f : FourierHilbert) :
    ‖(rightFactor_memLp f).toLp (rightFactor f)‖ ^ 2 =
      ∫ xy, rightSquare f xy ∂pairVolume := by
  rw [← realLp_square_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (rightFactor_memLp f)] with xy hxy
  rw [hxy, rightFactor_square]

theorem leftFactorLp_norm_bound (g : FourierHilbert) :
    ‖(leftFactor_memLp g).toLp (leftFactor g)‖ ≤ Real.sqrt sourceCompositionSchurBound * ‖g‖ := by
  have h := leftSquare_integral_bound g
  rw [originalLp_square_integral, ← factorLp_square_integral] at h
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg g))).mp
  simpa only [mul_pow, Real.sq_sqrt sourceCompositionSchurBound_nonnegative] using h

theorem rightFactorLp_norm_bound (f : FourierHilbert) :
    ‖(rightFactor_memLp f).toLp (rightFactor f)‖ ≤ Real.sqrt sourceCompositionSchurBound * ‖f‖ := by
  have h := rightSquare_integral_bound f
  rw [originalLp_square_integral, ← rightFactorLp_square_integral] at h
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  simpa only [mul_pow, Real.sq_sqrt sourceCompositionSchurBound_nonnegative] using h

theorem normPair_integral_bound (g f : FourierHilbert) :
    (∫ xy, normPair g f xy ∂pairVolume) ≤ sourceCompositionSchurBound * ‖g‖ * ‖f‖ := by
  let u := (leftFactor_memLp g).toLp (leftFactor g)
  let v := (rightFactor_memLp f).toLp (rightFactor f)
  have same : (∫ xy, normPair g f xy ∂pairVolume) = inner ℝ u v := by
    rw [L2.inner_def, normPair_factors]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (leftFactor_memLp g),
      MemLp.coeFn_toLp (rightFactor_memLp f)] with xy hxy hxy'
    simp only [u, v, hxy, hxy', Real.inner_apply]
  rw [same]
  calc
    inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (Real.sqrt sourceCompositionSchurBound * ‖g‖) *
        (Real.sqrt sourceCompositionSchurBound * ‖f‖) :=
      mul_le_mul (leftFactorLp_norm_bound g) (rightFactorLp_norm_bound f)
        (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = _ := by
      calc
        _ = (Real.sqrt sourceCompositionSchurBound)^2 * ‖g‖ * ‖f‖ := by ring
        _ = _ := by rw [Real.sq_sqrt sourceCompositionSchurBound_nonnegative]

def actualPair (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1) * actualFullCompositionKernelDefect xy.1 xy.2 * f xy.2

theorem actualPair_measurable (g f : FourierHilbert) : StronglyMeasurable (actualPair g f) :=
  ((Complex.continuous_conj.comp_stronglyMeasurable
    ((Lp.stronglyMeasurable g).comp_measurable measurable_fst)).mul
    actualFullCompositionKernelDefect_measurable).mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)

theorem actualPair_norm (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    ‖actualPair g f xy‖ = normPair g f xy := by
  simp [actualPair, normPair, kernelWeight]

theorem actualPair_integrable (g f : FourierHilbert) : Integrable (actualPair g f) pairVolume := by
  apply (normPair_integrable g f).mono' (actualPair_measurable g f).aestronglyMeasurable
  exact Eventually.of_forall fun xy => (actualPair_norm g f xy).le

theorem actualPair_absoluteIntegral_bound (g f : FourierHilbert) :
    (∫ xy, ‖actualPair g f xy‖ ∂pairVolume) ≤
      sourceCompositionSchurBound * ‖g‖ * ‖f‖ := by
  simp only [actualPair_norm]
  exact normPair_integral_bound g f

def sourceForm (g f : FourierHilbert) : ℂ := ∫ xy, actualPair g f xy ∂pairVolume

theorem sourceForm_norm_bound (g f : FourierHilbert) :
    ‖sourceForm g f‖ ≤ sourceCompositionSchurBound * ‖g‖ * ‖f‖ := by
  calc
    _ ≤ ∫ xy, ‖actualPair g f xy‖ ∂pairVolume := norm_integral_le_integral_norm _
    _ = ∫ xy, normPair g f xy ∂pairVolume := by simp only [actualPair_norm]
    _ ≤ _ := normPair_integral_bound g f

theorem sourceForm_add_right (g f h : FourierHilbert) :
    sourceForm g (f+h) = sourceForm g f + sourceForm g h := by
  rw [sourceForm, sourceForm, sourceForm, ← integral_add
    (actualPair_integrable g f) (actualPair_integrable g h)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add f h)] with xy hxy
  simp only [actualPair, Pi.add_apply] at *
  rw [hxy, mul_add]

theorem sourceForm_smul_right (g f : FourierHilbert) (c : ℂ) :
    sourceForm g (c • f) = c * sourceForm g f := by
  rw [sourceForm, sourceForm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c f)] with xy hxy
  simp only [actualPair, Pi.smul_apply, smul_eq_mul] at *
  rw [hxy]
  ring

theorem sourceForm_add_left (g h f : FourierHilbert) :
    sourceForm (g+h) f = sourceForm g f + sourceForm h f := by
  rw [sourceForm, sourceForm, sourceForm, ← integral_add
    (actualPair_integrable g f) (actualPair_integrable h f)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add g h)] with xy hxy
  simp only [actualPair, Pi.add_apply] at *
  rw [hxy, map_add]
  ring

theorem sourceForm_smul_left (g f : FourierHilbert) (c : ℂ) :
    sourceForm (c • g) f = conj c * sourceForm g f := by
  rw [sourceForm, sourceForm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c g)] with xy hxy
  simp only [actualPair, Pi.smul_apply, smul_eq_mul] at *
  rw [hxy, map_mul]
  ring

theorem sourceForm_hermitian (g f : FourierHilbert) :
    conj (sourceForm f g) = sourceForm g f := by
  rw [sourceForm, sourceForm, ← integral_conj]
  rw [← integral_prod_swap (fun xy => actualPair g f xy)]
  apply integral_congr_ae
  filter_upwards with xy
  simp only [actualPair, map_mul, Complex.conj_conj, Prod.swap]
  rw [actualFullCompositionKernelDefect_hermitian]
  ring

def sourceFormLinear : FourierHilbert →ₗ⋆[ℂ] FourierHilbert →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) sourceForm
    sourceForm_add_left
    (fun c g f => sourceForm_smul_left g f c)
    sourceForm_add_right
    (fun c g f => sourceForm_smul_right g f c)

def sourceContinuousForm : FourierHilbert →L⋆[ℂ] FourierHilbert →L[ℂ] ℂ :=
  sourceFormLinear.mkContinuous₂ sourceCompositionSchurBound sourceForm_norm_bound

theorem sourceContinuousForm_readback (g f : FourierHilbert) :
    sourceContinuousForm g f = ∫ xy, conj (g xy.1) *
      actualFullCompositionKernelDefect xy.1 xy.2 * f xy.2 ∂pairVolume := rfl

theorem sourceContinuousForm_norm_bound : ‖sourceContinuousForm‖ ≤ sourceCompositionSchurBound :=
  sourceFormLinear.mkContinuous₂_norm_le sourceCompositionSchurBound_nonnegative sourceForm_norm_bound

end LowEnergy.PreparationVacuumCompositionBounded
