import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarInverse
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylSlices

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseSource
open PreparationActualFactor PreparationScalarCoordinates PreparationPhaseScalar PreparationPhaseGuard
open PreparationVacuumWeyl CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open scoped BigOperators ContDiff

theorem actual_closed_phase_cone (z u : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i, |u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) :
    (fullCoordinates.symm z,nativeCovector (WithLp.toLp 2 u)) ∈ positiveCone :=
  ⟨theta_position_physical zbox,
    actual_closed_phase_A z u zbox ubox unit,actual_closed_phase_T z u zbox ubox⟩

theorem normalized_native_vector (p : PhysicalMomentum) :
    (WithLp.toLp 2 (normalizedMomentum p) : PhysicalMomentum)=‖p‖⁻¹ • p := by
  ext i
  simp only [normalizedMomentum,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem normalized_native_unit (p : PhysicalMomentum) (nonzero : p ≠ 0) :
    (∑ i : Fin 100,(normalizedMomentum p i)^2)=1 := by
  have normalized : ‖(WithLp.toLp 2 (normalizedMomentum p) : PhysicalMomentum)‖=1 := by
    rw [normalized_native_vector,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr nonzero)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]
  rw [←EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (normalizedMomentum p) : PhysicalMomentum),normalized]
  norm_num

theorem original_radial_cotangent (p : PhysicalMomentum) (nonzero : p ≠ 0) :
    ‖p‖ • nativeCovector (WithLp.toLp 2 (normalizedMomentum p))=nativeCovector p := by
  rw [normalized_native_vector,normalized_native_covector,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero),one_smul]

theorem source_support_positiveCone (z : FlatConfiguration) (p : PhysicalMomentum)
    (zbox : z∈thetaPositionClosed)
    (ubox : normalizedMomentum p∈thetaDirectionClosed) (nonzero : p ≠ 0) :
    nativePhase (z,p)∈positiveCone := by
  have unitCone := actual_closed_phase_cone z (normalizedMomentum p) zbox ubox
    (normalized_native_unit p nonzero)
  have positive := norm_pos_iff.mpr nonzero
  refine ⟨unitCone.1,?_,?_⟩
  · change 0 < A (fullCoordinates.symm z) (nativeCovector p)
    rw [←original_radial_cotangent p nonzero,A_smul]
    exact mul_pos (sq_pos_of_pos positive) unitCone.2.1
  · change 0 < T (fullCoordinates.symm z) (nativeCovector p)
    rw [←original_radial_cotangent p nonzero,T_smul]
    exact mul_pos (sq_pos_of_pos positive) unitCone.2.2

end LowEnergy.PreparationPhaseSource
