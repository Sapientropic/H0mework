import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import H0mework.Physics.GaugeStanding.ScalarPairingSkew
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The original fixed scalar vacuum generates its broken-orbit chart.

The Lie norm is the original native P286 pairing, not the Euclidean norm of
its chosen coordinate basis. No matrix, complement, or nondegeneracy witness
is supplied by the caller. This basis-free producer does not assert a numeric
rank or install the later residual gauge quotient.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceQuantumScalarChart

open SaturationMonoid.PhysicsCore
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineHolonomicField StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineGlobalIntegratedAction StageNineP286LinkedActiveScalarPairingSkew
open scoped RealInnerProductSpace

/-- A distinct normed carrier keeps the native pairing out of the arbitrary
Euclidean coordinate norm already installed on `P286CoordinateCarrier`. -/
def NativeLie := P286CoordinateCarrier

instance : AddCommGroup NativeLie := inferInstanceAs (AddCommGroup P286CoordinateCarrier)
instance : Module ℝ NativeLie := inferInstanceAs (Module ℝ P286CoordinateCarrier)
instance : FiniteDimensional ℝ NativeLie :=
  by
    let : FiniteDimensional ℝ SU7MotherLieAlgebra.P286LieBlockData :=
      FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
    exact inferInstanceAs (FiniteDimensional ℝ P286CoordinateCarrier)

private abbrev nativeCore : InnerProductSpace.Core ℝ NativeLie where
  inner := p286CoordinateLiePairing
  conj_inner_symm x y := p286CoordinateLiePairing_symmetric y x
  re_inner_nonneg := p286CoordinateLiePairing_self_nonnegative
  add_left x y z := p286CoordinateLiePairing_add_left x y z
  smul_left x y r := p286CoordinateLiePairing_smul_left r x y
  definite x := (p286CoordinateLiePairing_self_eq_zero_iff x).mp

instance : NormedAddCommGroup NativeLie := nativeCore.toNormedAddCommGroup
instance : InnerProductSpace ℝ NativeLie :=
  InnerProductSpace.ofCore nativeCore.toCore

abbrev Scalar := ScalarCoordinateCarrier

def vacuum : Scalar := sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource

def action (phi : Scalar) : NativeLie →ₗ[ℝ] Scalar where
  toFun a := scalarP286ActionBilinear a phi
  map_add' a b := LinearMap.congr_fun (map_add scalarP286ActionBilinear a b) phi
  map_smul' r a := LinearMap.congr_fun (map_smul scalarP286ActionBilinear r a) phi

def orbit : NativeLie →ₗ[ℝ] Scalar := action vacuum
def stabilizer : Submodule ℝ NativeLie := orbit.ker
def broken : Submodule ℝ NativeLie := stabilizerᗮ
def scalarSlice : Submodule ℝ Scalar := orbit.rangeᗮ

theorem original_scalar_pairing (phi psi : Scalar) :
    scalarCoordinatePairingRe phi psi = ⟪phi, psi⟫ := by
  simp [scalarCoordinatePairingRe, PiLp.inner_apply, mul_comm]

theorem vacuum_mem_scalarSlice : vacuum ∈ scalarSlice := by
  apply (Submodule.mem_orthogonal _ _).2
  rintro _ ⟨a, rfl⟩
  have h := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) vacuum vacuum
  rw [original_scalar_pairing, original_scalar_pairing] at h
  change ⟪orbit a, vacuum⟫ + ⟪vacuum, orbit a⟫ = 0 at h
  have hs := real_inner_comm vacuum (orbit a)
  linarith

theorem affine_slice_constraint (x : scalarSlice) (a : NativeLie) :
    ⟪orbit a, vacuum + (x : Scalar)⟫ = 0 := by
  exact (Submodule.mem_orthogonal _ _).1
    (scalarSlice.add_mem vacuum_mem_scalarSlice x.property) (orbit a) ⟨a, rfl⟩

def brokenAction (phi : Scalar) : broken →ₗ[ℝ] Scalar :=
  (action phi).comp broken.subtype

def brokenOrbit : broken →ₗ[ℝ] Scalar := brokenAction vacuum

theorem brokenOrbit_injective : Function.Injective brokenOrbit := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro a ha
    have hker : (a : NativeLie) ∈ stabilizer := ha
    have hz : (a : NativeLie) = 0 := by
      have : (a : NativeLie) ∈ stabilizer ⊓ stabilizerᗮ := ⟨hker, a.property⟩
      simpa only [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] using this
    exact Subtype.ext hz
  · exact bot_le

/-- The actual scalar-normal / broken-Gauss consistency operator. -/
def consistency (phi : Scalar) : broken →ₗ[ℝ] broken :=
  brokenOrbit.adjoint.comp (brokenAction phi)

theorem consistency_at_vacuum :
    consistency vacuum = brokenOrbit.adjoint.comp brokenOrbit := rfl

theorem consistency_pairing (phi : Scalar) (a b : broken) :
    ⟪a, consistency phi b⟫ = ⟪brokenOrbit a, brokenAction phi b⟫ := by
  exact LinearMap.adjoint_inner_right brokenOrbit a (brokenAction phi b)

theorem consistency_source_injective : Function.Injective (consistency vacuum) := by
  exact (LinearMap.adjoint_comp_self_injective_iff brokenOrbit).2 brokenOrbit_injective

theorem source_Gram_positive (a : broken) (ha : a ≠ 0) :
    0 < ⟪a, consistency vacuum a⟫ := by
  rw [consistency_pairing]
  exact real_inner_self_pos.mpr (fun h => ha (brokenOrbit_injective (by simpa using h)))

def sourceGramEquiv : broken ≃ₗ[ℝ] broken :=
  LinearEquiv.ofInjectiveEndo (consistency vacuum) consistency_source_injective

theorem sourceGram_left_inverse (a : broken) :
    sourceGramEquiv.symm (consistency vacuum a) = a :=
  sourceGramEquiv.symm_apply_apply a

theorem sourceGram_right_inverse (a : broken) :
    consistency vacuum (sourceGramEquiv.symm a) = a :=
  sourceGramEquiv.apply_symm_apply a

theorem source_determinant_ne_zero : (consistency vacuum).det ≠ 0 :=
  sourceGramEquiv.isUnit_det'.ne_zero

def consistencyFamily : Scalar →ₗ[ℝ] (broken →L[ℝ] broken) where
  toFun phi := (consistency phi).toContinuousLinearMap
  map_add' phi psi := by
    apply ContinuousLinearMap.ext
    intro a
    change brokenOrbit.adjoint (scalarP286ActionBilinear (a : NativeLie) (phi + psi)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r phi := by
    apply ContinuousLinearMap.ext
    intro a
    change brokenOrbit.adjoint (scalarP286ActionBilinear (a : NativeLie) (r • phi)) = _
    rw [map_smul, map_smul]
    rfl

theorem consistency_continuous : Continuous consistencyFamily :=
  consistencyFamily.toContinuousLinearMap.continuous

theorem determinant_continuous : Continuous (fun phi : Scalar => (consistency phi).det) :=
  ContinuousLinearMap.continuous_det.comp consistency_continuous

/-- An actual source-generated open noncharacteristic set, not a supplied
regularity hypothesis or a numeric-rank promise. -/
def regularScalars : TopologicalSpace.Opens Scalar :=
  ⟨{phi | (consistency phi).det ≠ 0}, isOpen_ne.preimage determinant_continuous⟩

theorem vacuum_mem_regularScalars : vacuum ∈ regularScalars := source_determinant_ne_zero

/-- The original scalar normal constraints leave the affine peripheral slice. -/
def scalarChart : TopologicalSpace.Opens scalarSlice :=
  ⟨{x | vacuum + (x : Scalar) ∈ regularScalars},
    regularScalars.isOpen.preimage (continuous_const.add continuous_subtype_val)⟩

theorem zero_mem_scalarChart : (0 : scalarSlice) ∈ scalarChart := by
  change (consistency (vacuum + (0 : scalarSlice))).det ≠ 0
  simpa using source_determinant_ne_zero

theorem scalarChart_nonempty : (scalarChart : Set scalarSlice).Nonempty :=
  ⟨0, zero_mem_scalarChart⟩

def chartConsistencyEquiv (x : scalarChart) : broken ≃ₗ[ℝ] broken :=
  LinearMap.equivOfDetNeZero (consistency (vacuum + (x.val : Scalar))) x.property

theorem chartConsistency_left_inverse (x : scalarChart) (a : broken) :
    (chartConsistencyEquiv x).symm (consistency (vacuum + (x.val : Scalar)) a) = a :=
  (chartConsistencyEquiv x).symm_apply_apply a

theorem chartConsistency_right_inverse (x : scalarChart) (a : broken) :
    consistency (vacuum + (x.val : Scalar)) ((chartConsistencyEquiv x).symm a) = a :=
  (chartConsistencyEquiv x).apply_symm_apply a

end LowEnergy.SourceQuantumScalarChart
