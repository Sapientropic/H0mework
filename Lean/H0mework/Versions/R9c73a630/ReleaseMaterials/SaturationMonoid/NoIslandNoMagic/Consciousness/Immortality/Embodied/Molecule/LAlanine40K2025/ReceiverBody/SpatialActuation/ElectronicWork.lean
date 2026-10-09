import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation.GammaDynamics

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient MeasureTheory
open UnifiedOrbitals
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def originalKernelJet (D : Matrix Basis Basis ℂ) (left right : MultiIndex) (x y : Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, Frame.registeredAOState D i j*
    (orbital (sourceTerms i) left x : ℂ)*(orbital (sourceTerms j) right y : ℂ)

def spatialShift (phase : Phase) (t : ℝ) : Point := Function.update 0 0 (travel phase t)

theorem moving_point_pullback (phase : Phase) (t : ℝ) (x : Point) :
    movingPoint phase t x=x-spatialShift phase t := by
  funext k
  by_cases same : k=0
  · subst k
    simp [movingPoint,spatialShift]
  · simp [movingPoint,spatialShift,same]

theorem moving_kernel_pullback (D : Matrix Basis Basis ℂ) (left right : MultiIndex)
    (phase : Phase) (t : ℝ) (x y : Point) :
    movingKernelJet D left right phase t x y=
      originalKernelJet D left right (x-spatialShift phase t) (y-spatialShift phase t) := by
  simp only [movingKernelJet,movingJet,originalKernelJet,moving_point_pullback]

def translationMomentum (D : Matrix Basis Basis ℂ) : ℝ :=
  (∫ x : Point, -Complex.I*originalKernelJet D (raise zeroJet 0) zeroJet x x).re

def movingTranslationMomentum (D : Matrix Basis Basis ℂ) (phase : Phase) (t : ℝ) : ℝ :=
  (∫ x : Point, -Complex.I*movingKernelJet D (raise zeroJet 0) zeroJet phase t x x).re

theorem momentum_integrand_integrable (D : Matrix Basis Basis ℂ) :
    Integrable (fun x : Point => -Complex.I*originalKernelJet D (raise zeroJet 0) zeroJet x x) := by
  have each (i j : Basis) : Integrable (fun x : Point =>
      Frame.registeredAOState D i j*(orbital (sourceTerms i) (raise zeroJet 0) x : ℂ)*
        (orbital (sourceTerms j) zeroJet x : ℂ)) := by
    have h : Integrable (fun x : Point =>
        ((orbital (sourceTerms i) (raise zeroJet 0) x*orbital (sourceTerms j) zeroJet x : ℝ) : ℂ)) :=
      (source_product_integrable i j (raise zeroJet 0) zeroJet).ofReal
    simpa only [Complex.ofReal_mul,mul_assoc] using h.const_mul (Frame.registeredAOState D i j)
  exact (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => each i j))).const_mul (-Complex.I)

theorem translation_momentum_invariant (D : Matrix Basis Basis ℂ) (phase : Phase) (t : ℝ) :
    movingTranslationMomentum D phase t=translationMomentum D := by
  unfold movingTranslationMomentum translationMomentum
  simp only [moving_kernel_pullback]
  congr 1
  exact integral_sub_right_eq_self (μ := (volume : Measure Point))
    (fun x : Point => -Complex.I*originalKernelJet D (raise zeroJet 0) zeroJet x x) (spatialShift phase t)

-- The generator's momentum energy and the source controller's scalar storage are both retained.
def translationEnergy (D : Matrix Basis Basis ℂ) (phase : Phase) (t : ℝ) : ℝ :=
  travelRate phase t*movingTranslationMomentum D phase t
def electronicControlEnergy (phase : Phase) (t : ℝ) : ℝ :=
  -travelRate phase t*translationMomentum input.body.realized

theorem drive_gamma (t : ℝ) : FiniteContinuation.gammaPath input .drive t=input.body.realized := by
  simp only [FiniteContinuation.gammaPath,FiniteActuation.electronicTime,FiniteActuation.electron_flow_zero]

theorem transport_energy_on_fixed_state (phase : Phase) (time fixedTime : ℝ) :
    translationEnergy (FiniteContinuation.gammaPath input phase fixedTime) phase time+
      electronicControlEnergy phase time=0 := by
  rw [translationEnergy,translation_momentum_invariant,electronicControlEnergy]
  cases phase with
  | enter => simp only [travelRate,shiftRate,zero_mul,neg_zero,add_zero]
  | drive => rw [drive_gamma]; ring
  | leave => simp only [travelRate,shiftRate,zero_mul,neg_zero,add_zero]

theorem transport_energy_clock_partial (phase : Phase) (t : ℝ) :
    HasDerivAt (fun time =>
      translationEnergy (FiniteContinuation.gammaPath input phase t) phase time+
        electronicControlEnergy phase time) 0 t := by
  simp_rw [transport_energy_on_fixed_state]
  exact hasDerivAt_const t 0

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialActuation
