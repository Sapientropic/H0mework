import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailWeightedPairs
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionForm
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailOperator
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder PreparationVacuumWeylDomain
open PreparationVacuumFrequencyN2 CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate FourierTransform ENNReal InnerProductSpace
open PreparationVacuumTailFourier PreparationVacuumTailSupport
open PreparationVacuumCompositionBounded (realLp_square_integral originalLp_square_integral)
variable (B : ℕ → Fin 5 → ArrayBound)
variable (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
attribute [local irreducible] tailWeylKernel

abbrev pairVolume : Measure (PhysicalMomentum × PhysicalMomentum) := volume.prod volume

def leftFactor (g : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  Real.sqrt (kernelWeight B xy) * ‖g xy.1‖
def rightFactor (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  Real.sqrt (kernelWeight B xy) * ‖f xy.2‖

theorem leftFactor_square (g : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    leftFactor B g xy ^ 2 = leftSquare B g xy := by
  simp only [leftFactor, leftSquare, mul_pow, Real.sq_sqrt (kernelWeight_nonnegative B xy)]
theorem rightFactor_square (f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    rightFactor B f xy ^ 2 = rightSquare B f xy := by
  simp only [rightFactor, rightSquare, mul_pow, Real.sq_sqrt (kernelWeight_nonnegative B xy)]

include positive input in
theorem leftFactor_memLp (g : FourierHilbert) : MemLp (leftFactor B g) 2 pairVolume := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_sqrt.comp_stronglyMeasurable (kernelWeight_measurable B)).mul
      ((Lp.stronglyMeasurable g).comp_measurable measurable_fst).norm).aestronglyMeasurable).mpr
  change Integrable (fun xy => leftFactor B g xy ^ 2) pairVolume
  simpa only [leftFactor_square B] using leftSquare_integrable B positive input g

include positive input in
theorem rightFactor_memLp (f : FourierHilbert) : MemLp (rightFactor B f) 2 pairVolume := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_sqrt.comp_stronglyMeasurable (kernelWeight_measurable B)).mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd).norm).aestronglyMeasurable).mpr
  change Integrable (fun xy => rightFactor B f xy ^ 2) pairVolume
  simpa only [rightFactor_square B] using rightSquare_integrable B positive input f

def normPair (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℝ :=
  ‖g xy.1‖ * kernelWeight B xy * ‖f xy.2‖

theorem normPair_factors (g f : FourierHilbert) :
    normPair B g f = fun xy => leftFactor B g xy * rightFactor B f xy := by
  funext xy
  have h := Real.sq_sqrt (kernelWeight_nonnegative B xy)
  dsimp [normPair, leftFactor, rightFactor]
  symm
  calc
    _ = (Real.sqrt (kernelWeight B xy)) ^ 2 * (‖g xy.1‖ * ‖f xy.2‖) := by ring
    _ = _ := by rw [h]; ring

include positive input in
theorem normPair_integrable (g f : FourierHilbert) : Integrable (normPair B g f) pairVolume := by
  rw [normPair_factors B]
  exact (leftFactor_memLp B positive input g).integrable_mul (rightFactor_memLp B positive input f)

include positive input in
theorem factorLp_square_integral (g : FourierHilbert) :
    ‖(leftFactor_memLp B positive input g).toLp (leftFactor B g)‖ ^ 2 =
      ∫ xy, leftSquare B g xy ∂pairVolume := by
  rw [← realLp_square_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (leftFactor_memLp B positive input g)] with xy hxy
  rw [hxy, leftFactor_square B]

include positive input in
theorem rightFactorLp_square_integral (f : FourierHilbert) :
    ‖(rightFactor_memLp B positive input f).toLp (rightFactor B f)‖ ^ 2 =
      ∫ xy, rightSquare B f xy ∂pairVolume := by
  rw [← realLp_square_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (rightFactor_memLp B positive input f)] with xy hxy
  rw [hxy, rightFactor_square B]

include positive input in
theorem leftFactorLp_norm_bound (g : FourierHilbert) :
    ‖(leftFactor_memLp B positive input g).toLp (leftFactor B g)‖ ≤ Real.sqrt (tailSchurBound B) * ‖g‖ := by
  have h := leftSquare_integral_bound B positive input g
  rw [originalLp_square_integral, ← factorLp_square_integral B positive input] at h
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg g))).mp
  simpa only [mul_pow, Real.sq_sqrt (tailSchurBound_nonnegative B positive)] using h

include positive input in
theorem rightFactorLp_norm_bound (f : FourierHilbert) :
    ‖(rightFactor_memLp B positive input f).toLp (rightFactor B f)‖ ≤ Real.sqrt (tailSchurBound B) * ‖f‖ := by
  have h := rightSquare_integral_bound B positive input f
  rw [originalLp_square_integral, ← rightFactorLp_square_integral B positive input] at h
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  simpa only [mul_pow, Real.sq_sqrt (tailSchurBound_nonnegative B positive)] using h

include positive input in
theorem normPair_integral_bound (g f : FourierHilbert) :
    (∫ xy, normPair B g f xy ∂pairVolume) ≤ (tailSchurBound B) * ‖g‖ * ‖f‖ := by
  let u := (leftFactor_memLp B positive input g).toLp (leftFactor B g)
  let v := (rightFactor_memLp B positive input f).toLp (rightFactor B f)
  have same : (∫ xy, normPair B g f xy ∂pairVolume) = inner ℝ u v := by
    rw [L2.inner_def, normPair_factors B]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (leftFactor_memLp B positive input g),
      MemLp.coeFn_toLp (rightFactor_memLp B positive input f)] with xy hxy hxy'
    simp only [u, v, hxy, hxy', Real.inner_apply]
  rw [same]
  calc
    inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (Real.sqrt (tailSchurBound B) * ‖g‖) *
        (Real.sqrt (tailSchurBound B) * ‖f‖) :=
      mul_le_mul (leftFactorLp_norm_bound B positive input g) (rightFactorLp_norm_bound B positive input f)
        (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = _ := by
      calc
        _ = (Real.sqrt (tailSchurBound B))^2 * ‖g‖ * ‖f‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (tailSchurBound_nonnegative B positive)]

def actualPair (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1) * tailWeylKernel B xy.1 xy.2 * f xy.2

theorem actualPair_measurable (g f : FourierHilbert) : StronglyMeasurable (actualPair B g f) :=
  ((Complex.continuous_conj.comp_stronglyMeasurable
    ((Lp.stronglyMeasurable g).comp_measurable measurable_fst)).mul
    (tailWeylKernel_measurable B)).mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)

theorem actualPair_norm (g f : FourierHilbert) (xy : PhysicalMomentum × PhysicalMomentum) :
    ‖actualPair B g f xy‖ = normPair B g f xy := by
  simp [actualPair, normPair, kernelWeight]

include positive input in
theorem actualPair_integrable (g f : FourierHilbert) : Integrable (actualPair B g f) pairVolume := by
  apply (normPair_integrable B positive input g f).mono' (actualPair_measurable B g f).aestronglyMeasurable
  exact Eventually.of_forall fun xy => (actualPair_norm B g f xy).le

include positive input in
theorem actualPair_absoluteIntegral_bound (g f : FourierHilbert) :
    (∫ xy, ‖actualPair B g f xy‖ ∂pairVolume) ≤
      (tailSchurBound B) * ‖g‖ * ‖f‖ := by
  simp only [actualPair_norm B]
  exact normPair_integral_bound B positive input g f

def sourceForm (g f : FourierHilbert) : ℂ := ∫ xy, actualPair B g f xy ∂pairVolume

include positive input in
theorem sourceForm_norm_bound (g f : FourierHilbert) :
    ‖sourceForm B g f‖ ≤ (tailSchurBound B) * ‖g‖ * ‖f‖ := by
  calc
    _ ≤ ∫ xy, ‖actualPair B g f xy‖ ∂pairVolume := norm_integral_le_integral_norm _
    _ = ∫ xy, normPair B g f xy ∂pairVolume := by simp only [actualPair_norm B]
    _ ≤ _ := normPair_integral_bound B positive input g f

include positive input in
theorem sourceForm_add_right (g f h : FourierHilbert) :
    sourceForm B g (f+h) = sourceForm B g f + sourceForm B g h := by
  rw [sourceForm, sourceForm, sourceForm, ← integral_add
    (actualPair_integrable B positive input g f) (actualPair_integrable B positive input g h)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add f h)] with xy hxy
  simp only [actualPair, Pi.add_apply] at *
  rw [hxy, mul_add]

theorem sourceForm_smul_right (g f : FourierHilbert) (c : ℂ) :
    sourceForm B g (c • f) = c * sourceForm B g f := by
  rw [sourceForm, sourceForm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c f)] with xy hxy
  simp only [actualPair, Pi.smul_apply, smul_eq_mul] at *
  rw [hxy]
  ring

include positive input in
theorem sourceForm_add_left (g h f : FourierHilbert) :
    sourceForm B (g+h) f = sourceForm B g f + sourceForm B h f := by
  rw [sourceForm, sourceForm, sourceForm, ← integral_add
    (actualPair_integrable B positive input g f) (actualPair_integrable B positive input h f)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add g h)] with xy hxy
  simp only [actualPair, Pi.add_apply] at *
  rw [hxy, map_add]
  ring

theorem sourceForm_smul_left (g f : FourierHilbert) (c : ℂ) :
    sourceForm B (c • g) f = conj c * sourceForm B g f := by
  rw [sourceForm, sourceForm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c g)] with xy hxy
  simp only [actualPair, Pi.smul_apply, smul_eq_mul] at *
  rw [hxy, map_mul]
  ring

theorem sourceForm_hermitian (g f : FourierHilbert) :
    conj (sourceForm B f g) = sourceForm B g f := by
  rw [sourceForm, sourceForm, ← integral_conj]
  rw [← integral_prod_swap (fun xy => actualPair B g f xy)]
  apply integral_congr_ae
  filter_upwards with xy
  simp only [actualPair, map_mul, Complex.conj_conj, Prod.swap]
  rw [tailWeylKernel_hermitian B]
  ring

def sourceFormLinear : FourierHilbert →ₗ⋆[ℂ] FourierHilbert →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (sourceForm B)
    (sourceForm_add_left B positive input)
    (fun c g f => sourceForm_smul_left B g f c)
    (sourceForm_add_right B positive input)
    (fun c g f => sourceForm_smul_right B g f c)

def sourceContinuousForm : FourierHilbert →L⋆[ℂ] FourierHilbert →L[ℂ] ℂ :=
  (sourceFormLinear B positive input).mkContinuous₂ (tailSchurBound B) (sourceForm_norm_bound B positive input)

theorem sourceContinuousForm_readback (g f : FourierHilbert) :
    sourceContinuousForm B positive input g f = ∫ xy, conj (g xy.1) *
      tailWeylKernel B xy.1 xy.2 * f xy.2 ∂pairVolume := rfl

include positive input in
theorem sourceContinuousForm_norm_bound : ‖sourceContinuousForm B positive input‖ ≤ (tailSchurBound B) :=
  (sourceFormLinear B positive input).mkContinuous₂_norm_le (tailSchurBound_nonnegative B positive) (sourceForm_norm_bound B positive input)

end LowEnergy.PreparationVacuumTailOperator
