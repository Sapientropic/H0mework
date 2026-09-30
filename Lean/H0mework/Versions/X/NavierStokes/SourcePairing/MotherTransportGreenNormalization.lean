import H0mework.Versions.X.NavierStokes.SourcePairing.MotherTransportGreenAdjoint
import H0mework.Versions.X.NavierStokes.Friedrichs.Energy

set_option autoImplicit false
open scoped BigOperators Matrix ENNReal

namespace SaturationMonoid.NavierStokes.NativeCanonicalGreenNormalization

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineFullDiracAdjointMaterial StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open MeasureTheory Set NativeCanonicalFluidCoframe NativeMaterialMomentumJet
open NativeMaterialAdjointPrincipal NativeMaterialJetAction NativePauliCoframeAction
open NativeCanonicalGreenAdjoint NativePhysicalFourier NativePhysicalTimeAction
open NativeEndpointVelocityCarrier NativeForwardWindowEvolution

noncomputable section

def current (velocity : PhysicalSpace) (first last : DiracExteriorMatterCarrier) (direction : Fin 4) : ℂ :=
  (volumeFactor velocity : ℂ) * fullCanonicalDiracAdjoint first (principal velocity direction last)

def densityJet (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) : ℝ :=
  inner ℝ velocity (jet direction) / 4

theorem densityJet_actual {path : ℝ → PhysicalSpace} {time : ℝ}
    (jet : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (actual : HasDerivAt path (jet direction) time) :
    HasDerivAt (fun parameter => density (path parameter)) (densityJet (path time) jet direction) time := by
  convert! (actual.norm_sq.div_const 8).const_add 2 using 1
  unfold densityJet
  ring

theorem normalized_momentum_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) (actual : HasDerivAt path (jet direction) time)
    (last : DiracExteriorMatterCarrier) :
    HasDerivAt (fun parameter => (density (path parameter) : ℂ) *
      current (path parameter) (matter (path parameter)) last direction)
      ((density (path time) : ℂ) * NativeMaterialAdjointAction.momentumDerivative
        (path time) jet (matter (path time)) (NativeSourceMaterialAdjoint.rawDerivative jet) last direction +
        (densityJet (path time) jet direction : ℂ) * current (path time) (matter (path time)) last direction) time := by
  have scalar := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time (densityJet_actual jet direction actual)
  have momentum := NativeSourceMaterialAdjoint.momentum_hasDerivAt jet direction actual last
  convert! scalar.mul momentum using 1
  simp only [current, Function.comp_apply, Complex.ofRealCLM_apply]
  ring

/-- All four product-rule terms introduced by multiplying the original current by rho. -/
def remainder (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) : ℂ :=
  ∑ direction, (densityJet velocity jet direction : ℂ) * current velocity first last direction

def normalizedDerivative (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) (firstJet lastJet : Fin 4 → DiracExteriorMatterCarrier) : ℂ :=
  (density velocity : ℂ) * currentDerivative velocity jet first last firstJet lastJet +
    remainder velocity jet first last

/-- This is the same Green identity after normalization, with no omitted lower-order term. -/
theorem normalized_green (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) (firstJet lastJet : Fin 4 → DiracExteriorMatterCarrier) :
    normalizedDerivative velocity jet first last firstJet lastJet =
      ((density velocity * volumeFactor velocity : ℝ) : ℂ) *
        (fullCanonicalDiracAdjoint first (kinetic velocity jet last lastJet) -
          fullCanonicalDiracAdjoint (kinetic velocity jet first firstJet) last) +
      remainder velocity jet first last := by
  rw [normalizedDerivative, whole_green, Complex.ofReal_mul, mul_assoc]

theorem remainder_coefficients (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) :
    remainder velocity jet first last =
      ((densityJet velocity jet 0 / density velocity : ℝ) : ℂ) *
        fullCanonicalDiracAdjoint first (Complex.I • diracMatrixMatterAction (diracGamma 0) last) +
      ∑ direction : Fin 3, (densityJet velocity jet direction.succ : ℂ) *
        fullCanonicalDiracAdjoint first (Complex.I • diracMatrixMatterAction (diracGamma direction.succ) last) := by
  rw [remainder, Fin.sum_univ_succ]
  simp only [current, weighted_principal, coefficient_eq, Fin.succ_ne_zero,
    if_false, if_true, Complex.ofReal_one, one_mul, Complex.ofReal_inv, Complex.ofReal_div]
  ring

theorem current_source_im (velocity : PhysicalSpace) (direction : Fin 4) :
    (current velocity (matter velocity) (matter velocity) direction).im = densitizedCurrent velocity direction := by
  rw [current, ← NativeSourceMaterialAdjoint.source_dual]
  simp only [principal, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.I_re, Complex.I_im, one_mul, zero_add, densitizedCurrent]
  rfl

/-- Both the temporal and the full spatial density-transport terms remain in the source read. -/
theorem remainder_source_im (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) :
    (remainder velocity jet (matter velocity) (matter velocity)).im =
      inner ℝ velocity (jet 0) / 4 +
        ∑ direction : Fin 3, velocity direction * inner ℝ velocity (jet direction.succ) / 4 := by
  simp only [remainder, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, current_source_im]
  rw [Fin.sum_univ_succ]
  simp only [densitizedCurrent_temporal, densitizedCurrent_spatial, densityJet, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  ring

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity}

def sourceField (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) : PhysicalField :=
  realField (wholeVelocity (velocityJet seed order time))

theorem sourceField_derivative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    HasDerivAt (sourceField seed order) (sourceField seed (order + 1) time) time :=
  (realFieldCLM.comp wholeVelocityCLM).hasFDerivAt.comp_hasDerivAt time
    (velocityJet_hasDerivAt seed order time)

theorem sourceField_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    sourceField seed 0 time = NativeCanonicalFriedrichsEnergy.sourceVelocity seed time := by
  simp only [sourceField, NativeCanonicalFriedrichsEnergy.sourceVelocity, velocityJet,
    NativeForwardWindowJets.jet_zero]

def temporalWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ℝ :=
  inner ℝ (sourceField seed 0 time) (sourceField seed 1 time) / 4

theorem temporalWork_integral (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    temporalWork seed time = ∫ point : Torus,
      inner ℝ (sourceField seed 0 time point) (sourceField seed 1 time point) / 4 := by
  rw [temporalWork, L2.inner_def, integral_div]

theorem temporalWork_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    temporalWork seed time = (NativeViewEnergyWork.residualWork seed 0 time -
      nu.coeff * NativeViewEnergyWork.dissipation seed 0 time) / 4 := by
  have own := ((sourceField_derivative seed 0 time).norm_sq.div_const 8).const_add 2
  have source := ((NativeUnheatedEnergy.energy_hasDerivAt seed time valid).div_const 4).const_add 2
  have same : (fun parameter => 2 + ‖sourceField seed 0 parameter‖ ^ 2 / 8) =
      (fun parameter => 2 + NativeViewEnergyContent.resolved seed 0 parameter / 4) := by
    funext parameter
    rw [NativeUnheatedEnergy.resolved_original, sourceField_zero]
    unfold NativeCanonicalFriedrichsEnergy.sourceVelocity
    ring
  rw [same] at own
  have equal := own.unique source
  dsimp only [temporalWork, Nat.zero_add]
  linarith

theorem sourceField_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    ‖sourceField seed order time‖ ≤ Real.sqrt 3 * NativeForwardWindowJets.budget seed order :=
  (realField_norm_le _).trans (mul_le_mul_of_nonneg_left
    ((wholeVelocity_norm_le _).trans (velocityJet_bound seed order time)) (Real.sqrt_nonneg _))

theorem temporalWork_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    |temporalWork seed time| ≤
      3 / 4 * NativeForwardWindowJets.budget seed 0 * NativeForwardWindowJets.budget seed 1 := by
  rw [temporalWork, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply (div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) (by norm_num : (0 : ℝ) ≤ 4)).trans
  have product := mul_le_mul (sourceField_bound seed 0 time) (sourceField_bound seed 1 time)
    (norm_nonneg _) ((norm_nonneg _).trans (sourceField_bound seed 0 time))
  have root : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have simplify : Real.sqrt 3 * NativeForwardWindowJets.budget seed 0 *
      (Real.sqrt 3 * NativeForwardWindowJets.budget seed 1) =
        3 * NativeForwardWindowJets.budget seed 0 * NativeForwardWindowJets.budget seed 1 := by
    calc
      _ = (Real.sqrt 3 * Real.sqrt 3) *
          (NativeForwardWindowJets.budget seed 0 * NativeForwardWindowJets.budget seed 1) := by ring
      _ = _ := by rw [root]; ring
  rw [simplify] at product
  linarith

theorem sourceField_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) :
    Continuous (sourceField seed order) :=
  continuous_iff_continuousAt.mpr fun time => (sourceField_derivative seed order time).continuousAt

theorem temporalWork_integrable (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    IntervalIntegrable (temporalWork seed) volume first last :=
  (((sourceField_continuous seed 0).inner (𝕜 := ℝ) (sourceField_continuous seed 1)).div_const 4).intervalIntegrable _ _

theorem temporalWork_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    temporalWork seed (response.2.clockAdvance + time) = temporalWork response.1 time := by
  simp only [temporalWork, sourceField, velocityJet]
  rw [NativeForwardWindowJets.jet_next seed 0 response generated time nonnegative,
    NativeForwardWindowJets.jet_next seed 1 response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeCanonicalGreenNormalization
