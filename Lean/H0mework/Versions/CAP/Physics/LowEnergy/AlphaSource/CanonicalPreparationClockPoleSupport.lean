import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockSquares
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationConeSupport
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockPole
open PreparationActualFactor PreparationPhaseSource PreparationPhaseBounds PreparationPhaseScalar PreparationCoordinates
open PreparationScalarCoordinates
open PreparationVacuumWeyl
open PreparationChartGuard CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart SourceQuantumNativeDimensions
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussHistoryHilbert
open PreparationVacuumClockJacobian PreparationVacuumEngineSource
open scoped BigOperators Matrix

theorem source_angular_frame_minor (u : FlatConfiguration)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) :
    0<u 67*u 80-u 69*u 78 := by
  have first := actual_angular_slot0_lower u ubox
  have sameCenter : sourceUnitMomentum 80=sourceUnitMomentum 67 := by
    norm_num [sourceUnitMomentum,Fin.ext_iff]
  have second := actual_angular_slot0_lower
    (fun i => if i=67 then u 80 else u i) (fun i => by
      by_cases selected : i=67
      · subst i
        simpa only [ite_true,←sameCenter] using ubox 80
      · simpa only [if_neg selected] using ubox i)
  simp only [ite_true] at second
  have offLeft : |u 69| ≤ sourceRadius := by
    simpa [sourceUnitMomentum,Fin.ext_iff] using ubox 69
  have offRight : |u 78| ≤ sourceRadius := by
    simpa [sourceUnitMomentum,Fin.ext_iff] using ubox 78
  have product := mul_lt_mul_of_pos_right first (by linarith : 0<u 80)
  have diagonal : (1/9 : ℝ)<u 67*u 80 := by nlinarith
  have off := mul_le_mul offLeft offRight (abs_nonneg _) radius_small.1.le
  have offProduct : u 69*u 78 ≤ sourceRadius^2 := by
    rw [←abs_mul] at off
    nlinarith [le_abs_self (u 69*u 78)]
  have radiusSquared := mul_self_lt_mul_self radius_small.1.le radius_small.2
  nlinarith

theorem actual_frame_parallel_zero (u : FlatConfiguration) (v : Fin 3 → ℝ)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius)
    (parallel : ∀ j : Fin 2,∀ i k : Fin 3,
      v i*u (gaugeSlot (frameFree k j))=v k*u (gaugeSlot (frameFree i j))) : v=0 := by
  have minor := source_angular_frame_minor u ubox
  have a := parallel 0 0 1
  have b := parallel 1 0 1
  have c := parallel 0 2 0
  change v 0*u 78=v 1*u 67 at a
  change v 0*u 80=v 1*u 69 at b
  change v 2*u 67=v 0*u 89 at c
  have zero0 : (u 67*u 80-u 69*u 78)*v 0=0 := by
    linear_combination u 67*b-u 69*a
  have zero1 : (u 67*u 80-u 69*u 78)*v 1=0 := by
    linear_combination u 78*b-u 80*a
  have v0 := (mul_eq_zero.mp zero0).resolve_left minor.ne'
  have v1 := (mul_eq_zero.mp zero1).resolve_left minor.ne'
  have positive : u 67≠0 := (by linarith [actual_angular_slot0_lower u ubox] : 0<u 67).ne'
  rw [v0,zero_mul] at c
  have v2 := (mul_eq_zero.mp c).resolve_right positive
  ext i
  fin_cases i <;> assumption

theorem actual_clockForm_zero (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) (v : Fin 3 → ℝ)
    (zero : clockForm (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) v=0) : v=0 := by
  let native := phaseChart z zbox
  have parallel := coloredGamma_parallel native u v zero
  have recovered := actual_frame_parallel_zero u ((triad native.val.1).transpose*ᵥv)
    ubox parallel
  have original := congrArg (fun w : Fin 3 → ℝ => (triadInverse native.val.1).transpose*ᵥw) recovered
  rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,triad_inverse_right native,
    Matrix.transpose_one,Matrix.one_mulVec,Matrix.mulVec_zero] at original
  exact original

theorem actual_clockForm_positive (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) (v : Fin 3 → ℝ)
    (nonzero : v≠0) : 0<clockForm (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u)) v := by
  have nonnegative := clockForm_nonnegative (phaseChart z zbox) (nativeCovector (WithLp.toLp 2 u)) v
  by_contra failure
  have zero := le_antisymm (le_of_not_gt failure) nonnegative
  exact nonzero (actual_clockForm_zero z u zbox ubox v zero)

theorem clockMatrix_isHermitian (z : SourceCoordinateSlice) (p : Cotangent) :
    (clockMatrix z p).IsHermitian := by
  ext i k
  simp only [clockMatrix,Matrix.conjTranspose_apply,Matrix.sub_apply,Matrix.smul_apply,
    Matrix.one_apply,smul_eq_mul,star_trivial]
  rw [S_symmetric z p k i]
  congr 1
  simp only [eq_comm]

theorem actual_clockMatrix_posDef (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) :
    (clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (clockMatrix_isHermitian _ _)
  intro v nonzero
  simpa only [clockForm,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
    Finset.mul_sum,mul_assoc] using actual_clockForm_positive z u zbox ubox v nonzero

theorem actual_clockMatrix_det_nonzero (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius) :
    (clockMatrix (fullCoordinates.symm z) (nativeCovector (WithLp.toLp 2 u))).det≠0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (actual_clockMatrix_posDef z u zbox ubox).isUnit).ne_zero

theorem clockMatrix_radial (z : SourceCoordinateSlice) (p : Cotangent) (r : ℝ) :
    clockMatrix z (r • p)=r^2 • clockMatrix z p := by
  ext i k
  simp only [clockMatrix,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,T_smul,S_smul]
  ring

theorem source_clockMatrix_posDef (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    (clockMatrix (fullCoordinates.symm z) (nativeCovector p)).PosDef := by
  rw [←original_radial_cotangent p nonzero,clockMatrix_radial]
  exact (actual_clockMatrix_posDef z (normalizedMomentum p) zbox ubox).smul
    (sq_pos_of_pos (norm_pos_iff.mpr nonzero))

theorem source_clockMatrix_det_nonzero (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    (clockMatrix (fullCoordinates.symm z) (nativeCovector p)).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp
    (source_clockMatrix_posDef z p zbox ubox nonzero).isUnit).ne_zero

theorem sourceM_det_nonzero (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    (sourceM (z,p)).det ≠ 0 := by
  simpa only [sourceM,actualT,actualS,nativePhase,clockMatrix] using
    source_clockMatrix_det_nonzero z p zbox ubox nonzero

theorem source_clock_inverse (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    (principalForceJacobian (z,p))⁻¹ = sourceInverse (z,p) :=
  sourceInverse_native (z,p) (source_support_positiveCone z p zbox ubox nonzero)
    (sourceM_det_nonzero z p zbox ubox nonzero)

theorem source_forceJacobian_inverse (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    (forceJacobian (z,p))⁻¹ = sourceInverse (z,p) :=
  sourceInverse_forceJacobian (z,p) (source_support_positiveCone z p zbox ubox nonzero)
    (sourceM_det_nonzero z p zbox ubox nonzero)

theorem source_generated_engine (k : ℕ) (a : Fin 4)
    (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z ∈ thetaPositionClosed)
    (ubox : normalizedMomentum p ∈ thetaDirectionClosed) (nonzero : p ≠ 0) :
    sourceEngine (k+1) a (Fin.last (k+1)) (z,p) =
      -∑ b : Fin 4,sourceInverse (z,p) a b*
        forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1)) (z,p) :=
  sourceEngine_generated_native k a (z,p)
    (source_support_positiveCone z p zbox ubox nonzero)
    (sourceM_det_nonzero z p zbox ubox nonzero)

end LowEnergy.PreparationVacuumClockPole
