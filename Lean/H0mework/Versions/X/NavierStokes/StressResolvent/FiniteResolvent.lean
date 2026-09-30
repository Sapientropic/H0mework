import H0mework.NavierStokes.InitialData.FiniteSupportRealityTrajectory
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import H0mework.Versions.X.NavierStokes.StressDynamics.CommonAdvector

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFiniteActionResolvent

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeCommonAdvectorAction

noncomputable section

def physicalSpace (modes : Finset IntegerWavevector) : Submodule ℝ ComplexVorticityHilbertState :=
  LinearMap.eqLocus (finiteTransverseSupportProjection modes).toLinearMap LinearMap.id ⊓
    LinearMap.eqLocus (complexFourierRealityReflection modes).toLinearMap LinearMap.id

theorem physical_supported {modes : Finset IntegerWavevector} (value : physicalSpace modes)
    (wave : IntegerWavevector) (outside : wave ∉ modes) : value.1 wave = 0 :=
  finiteTransverseSupportProjection_fixed_support value.2.1 outside

theorem physical_transverse {modes : Finset IntegerWavevector} (value : physicalSpace modes) :
    FiniteStateTransverseOn modes value.1 :=
  fun wave _ => finiteTransverseSupportProjection_fixed_transverse value.2.1 wave

theorem physical_reality {modes : Finset IntegerWavevector}
    (closed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes) (value : physicalSpace modes) :
    FiniteStateFourierReality value.1 :=
  finiteStateFourierReality_of_reflection_fixed closed (physical_supported value) value.2.2

def ofPhysical (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (value : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → value wave = 0)
    (transverse : FiniteStateTransverseOn modes value) (reality : FiniteStateFourierReality value) :
    physicalSpace modes := by
  refine ⟨value, ?_, ?_⟩
  · change finiteTransverseSupportProjection modes value = value
    apply lp.ext
    funext wave
    rw [finiteTransverseSupportProjection_apply]
    by_cases inside : wave ∈ modes
    · rw [if_pos inside]
      exact transverseProjection_eq_self_of_transverse (fun zero => zeroNotMem (zero ▸ inside))
        (transverse wave inside)
    · rw [if_neg inside, supported wave inside]
  · change complexFourierRealityReflection modes value = value
    apply lp.ext
    funext wave
    rw [complexFourierRealityReflection_apply]
    by_cases inside : wave ∈ modes
    · rw [if_pos inside, reality wave]
      funext coordinate
      simp only [vectorConj, star_star]
    · rw [if_neg inside, supported wave inside]

def coefficients (modes : Finset IntegerWavevector) :
    physicalSpace modes →ₗ[ℝ] EuclideanSpace ℂ (modes × Coordinate) where
  toFun := fun value => WithLp.toLp 2 (fun entry => value.1 entry.1.1 entry.2)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem coefficients_injective (modes : Finset IntegerWavevector) : Function.Injective (coefficients modes) := by
  intro first last same
  apply Subtype.ext
  apply lp.ext
  funext wave
  by_cases inside : wave ∈ modes
  · funext coordinate
    exact congrArg (fun value : EuclideanSpace ℂ (modes × Coordinate) => value (⟨wave, inside⟩, coordinate)) same
  · rw [physical_supported first wave inside, physical_supported last wave inside]

instance (modes : Finset IntegerWavevector) : FiniteDimensional ℝ (physicalSpace modes) :=
  FiniteDimensional.of_injective (coefficients modes) (coefficients_injective modes)

def pairing (modes : Finset IntegerWavevector) :
    physicalSpace modes →ₗ[ℝ] physicalSpace modes →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun first last => inner ℝ (coefficients modes first) (coefficients modes last))
    (fun _ _ _ => by simp only [map_add, inner_add_left])
    (fun _ _ _ => by simp only [map_smul, real_inner_smul_left, smul_eq_mul])
    (fun _ _ _ => by simp only [map_add, inner_add_right])
    (fun _ _ _ => by simp only [map_smul, real_inner_smul_right, smul_eq_mul])

theorem pairing_faithful (modes : Finset IntegerWavevector) (value : physicalSpace modes)
    (nonpositive : pairing modes value value ≤ 0) : value = 0 := by
  have zero : coefficients modes value = 0 := real_inner_self_nonpos.mp nonpositive
  apply coefficients_injective modes
  simpa only [map_zero] using zero

theorem pairing_eq (modes : Finset IntegerWavevector) (first last : physicalSpace modes) :
    pairing modes first last = ∑ wave ∈ modes, complexCoordinateRealInner (first.1 wave) (last.1 wave) := by
  have row_inner (left right : ComplexCoordinateVector) :
      (∑ coordinate : Coordinate, inner ℝ (left coordinate) (right coordinate)) =
        complexCoordinateRealInner left right := by
    unfold complexCoordinateRealInner
    apply Finset.sum_congr rfl
    intro coordinate _
    change (right coordinate * star (left coordinate)).re = _
    simp [Complex.mul_re, mul_comm]
  change inner ℝ (coefficients modes first) (coefficients modes last) = _
  calc
    _ = ∑ wave : modes, complexCoordinateRealInner (first.1 wave.1) (last.1 wave.1) := by
      rw [PiLp.inner_apply, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro wave _
      exact row_inner (first.1 wave.1) (last.1 wave.1)
    _ = _ := Finset.sum_coe_sort modes
      (fun wave : IntegerWavevector => complexCoordinateRealInner (first.1 wave) (last.1 wave))

theorem coefficients_mass (modes : Finset IntegerWavevector) (value : physicalSpace modes) :
    ‖coefficients modes value‖ ^ 2 = wholeVorticityEuclideanMass value.1 := by
  rw [← real_inner_self_eq_norm_sq]
  change pairing modes value value = _
  rw [pairing_eq]
  simp only [complexCoordinateRealInner_self]
  unfold wholeVorticityEuclideanMass
  simp only [vorticityRowAmplitude_sq]
  rw [tsum_eq_sum (s := modes) (fun wave outside => by
    rw [physical_supported value wave outside]
    simp [complexCoordinateVectorNormSq])]

section LinearResolution
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def implicitMap (action : V →ₗ[ℝ] V) (step : ℝ) : V →ₗ[ℝ] V := LinearMap.id - step • action

theorem implicitMap_injective (action : V →ₗ[ℝ] V) (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (faithful : ∀ value, form value value ≤ 0 → value = 0)
    (dissipative : ∀ value, form value (action value) ≤ 0) (step : ℝ) (nonnegative : 0 ≤ step) :
    Function.Injective (implicitMap action step) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro value zero
  have written : value - step • action value = 0 := zero
  have read := congrArg (form value) written
  rw [map_sub, map_smul, map_zero, smul_eq_mul] at read
  apply faithful value
  have sign := mul_nonpos_of_nonneg_of_nonpos nonnegative (dissipative value)
  linarith

variable [FiniteDimensional ℝ V]

def resolver (action : V →ₗ[ℝ] V) (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (faithful : ∀ value, form value value ≤ 0 → value = 0)
    (dissipative : ∀ value, form value (action value) ≤ 0) (step : ℝ) (nonnegative : 0 ≤ step) : V ≃ₗ[ℝ] V :=
  (LinearEquiv.ofInjectiveEndo (implicitMap action step)
    (implicitMap_injective action form faithful dissipative step nonnegative)).symm

theorem resolver_write (action : V →ₗ[ℝ] V) (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (faithful : ∀ value, form value value ≤ 0 → value = 0)
    (dissipative : ∀ value, form value (action value) ≤ 0) (step : ℝ) (nonnegative : 0 ≤ step) (load : V) :
    let solved := resolver action form faithful dissipative step nonnegative load
    solved - step • action solved = load :=
  (LinearEquiv.ofInjectiveEndo (implicitMap action step)
    (implicitMap_injective action form faithful dissipative step nonnegative)).apply_symm_apply load

end LinearResolution

theorem resolver_energy (modes : Finset IntegerWavevector)
    (action : physicalSpace modes →ₗ[ℝ] physicalSpace modes)
    (dissipative : ∀ value, pairing modes value (action value) ≤ 0)
    (step : ℝ) (nonnegative : 0 ≤ step) (load : physicalSpace modes) :
    let solved := resolver action (pairing modes) (pairing_faithful modes) dissipative step nonnegative load
    ‖coefficients modes load‖ ^ 2 = ‖coefficients modes solved‖ ^ 2 +
      ‖coefficients modes (load - solved)‖ ^ 2 - 2 * step * pairing modes solved (action solved) := by
  let solved := resolver action (pairing modes) (pairing_faithful modes) dissipative step nonnegative load
  change _ = ‖coefficients modes solved‖ ^ 2 + _ - _
  have written := resolver_write action (pairing modes) (pairing_faithful modes) dissipative step nonnegative load
  change solved - step • action solved = load at written
  have read := congrArg (pairing modes solved) written
  simp only [map_sub, map_smul, smul_eq_mul] at read
  change inner ℝ (coefficients modes solved) (coefficients modes solved) -
    step * pairing modes solved (action solved) =
    inner ℝ (coefficients modes solved) (coefficients modes load) at read
  rw [real_inner_self_eq_norm_sq] at read
  rw [map_sub, norm_sub_sq_real, real_inner_comm]
  linarith

theorem resolver_contraction (modes : Finset IntegerWavevector)
    (action : physicalSpace modes →ₗ[ℝ] physicalSpace modes)
    (dissipative : ∀ value, pairing modes value (action value) ≤ 0)
    (step : ℝ) (nonnegative : 0 ≤ step) (load : physicalSpace modes) :
    ‖coefficients modes (resolver action (pairing modes) (pairing_faithful modes)
      dissipative step nonnegative load)‖ ≤ ‖coefficients modes load‖ := by
  have balance := resolver_energy modes action dissipative step nonnegative load
  dsimp only at balance
  have sign := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative)
    (dissipative (resolver action (pairing modes) (pairing_faithful modes) dissipative step nonnegative load))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖coefficients modes (load - resolver action (pairing modes)
    (pairing_faithful modes) dissipative step nonnegative load)‖]

def physicalOperator (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) : physicalSpace modes →ₗ[ℝ] physicalSpace modes where
  toFun := fun value => ofPhysical modes zeroNotMem (frozenOperator modes nu advector value.1)
    (operator_supported modes nu advector value.1)
    (fun wave _ => operator_transverse modes nu advector value.1 wave)
    (operator_reality modes closed nu advector value.1 reality (physical_reality (fun {_} member => closed _ member) value))
  map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
  map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _)

theorem physicalOperator_pairing (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (value : physicalSpace modes) :
    pairing modes value (physicalOperator modes zeroNotMem closed nu advector reality value) =
      -nu.coeff * curlPair modes value.1 value.1 := by
  rw [pairing_eq]
  have original := cross_dissipation modes zeroNotMem closed nu advector value.1 value.1
    (physical_transverse value) (physical_transverse value)
    (physical_reality (fun {_} member => closed _ member) value)
    (physical_reality (fun {_} member => closed _ member) value)
  change velocityPair modes value.1 (frozenOperator modes nu advector value.1) = _
  linarith

theorem physicalOperator_dissipative (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (value : physicalSpace modes) :
    pairing modes value (physicalOperator modes zeroNotMem closed nu advector reality value) ≤ 0 := by
  rw [physicalOperator_pairing]
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr nu.coeff_pos.le)
  unfold curlPair
  exact Finset.sum_nonneg fun wave _ => by rw [complexCoordinateRealInner_self]; exact complexCoordinateVectorNormSq_nonneg _

def physicalResolver (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (nonnegative : 0 ≤ step) :
    physicalSpace modes ≃ₗ[ℝ] physicalSpace modes :=
  resolver (physicalOperator modes zeroNotMem closed nu advector reality) (pairing modes) (pairing_faithful modes)
    (physicalOperator_dissipative modes zeroNotMem closed nu advector reality) step nonnegative

theorem physicalResolver_balance (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
    (closed : FiniteModeNegClosed modes) (nu : Viscosity) (advector : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality advector) (step : ℝ) (nonnegative : 0 ≤ step) (load : physicalSpace modes) :
    let solved := physicalResolver modes zeroNotMem closed nu advector reality step nonnegative load
    ‖coefficients modes load‖ ^ 2 = ‖coefficients modes solved‖ ^ 2 +
      ‖coefficients modes (load - solved)‖ ^ 2 + 2 * step * nu.coeff * curlPair modes solved.1 solved.1 := by
  have original := resolver_energy modes (physicalOperator modes zeroNotMem closed nu advector reality)
    (physicalOperator_dissipative modes zeroNotMem closed nu advector reality) step nonnegative load
  dsimp only at original ⊢
  change _ = ‖coefficients modes (physicalResolver modes zeroNotMem closed nu advector reality step nonnegative load)‖ ^ 2 +
    _ - _ at original
  rw [physicalOperator_pairing] at original
  dsimp only [physicalResolver] at original ⊢
  convert original using 1
  ring

end
end SaturationMonoid.NavierStokes.NativeFiniteActionResolvent
