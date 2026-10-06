import H0mework.Physics.LowEnergy.Quantum.SourceQuantumScalarChart
import Mathlib.Tactic

/-! A subordinate source calculation for the original native history.
The scalar radius is orthogonal to every original orbit direction, before
any inverse constraint matrix is introduced. -/
set_option autoImplicit false
namespace LowEnergy.SourceNativeHistoryRadial
open SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore
open StageNineP286LinkedActiveScalarPairingSkew
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariationDensity
open scoped RealInnerProductSpace
noncomputable section

theorem radial_orbit_zero (x : scalarSlice) (a : NativeLie) :
    ⟪(x : Scalar), action (vacuum + (x : Scalar)) a⟫ = 0 := by
  have first : ⟪(x : Scalar), orbit a⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 x.property (orbit a) ⟨a, rfl⟩
  have skew := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a))
    (x : Scalar) (x : Scalar)
  rw [original_scalar_pairing, original_scalar_pairing] at skew
  change ⟪action (x : Scalar) a, (x : Scalar)⟫ +
    ⟪(x : Scalar), action (x : Scalar) a⟫ = 0 at skew
  have second : ⟪(x : Scalar), action (x : Scalar) a⟫ = 0 := by
    rw [real_inner_comm] at skew
    linarith
  change ⟪(x : Scalar), scalarP286ActionBilinear a (vacuum + (x : Scalar))⟫ = 0
  rw [map_add, inner_add_right]
  change ⟪(x : Scalar), orbit a⟫ + ⟪(x : Scalar), action (x : Scalar) a⟫ = 0
  rw [first, second, zero_add]

def sourceVacuum : scalarSlice := ⟨vacuum, vacuum_mem_scalarSlice⟩

theorem consistency_scale (r : ℝ) : consistency (r • vacuum) = r • consistency vacuum := by
  apply LinearMap.ext
  intro a
  change brokenOrbit.adjoint (scalarP286ActionBilinear (a : NativeLie) (r • vacuum)) =
    r • brokenOrbit.adjoint (scalarP286ActionBilinear (a : NativeLie) vacuum)
  rw [map_smul, map_smul]

theorem source_ray_regular (t : ℝ) (positive : 0 < 1+t) :
    t • sourceVacuum ∈ scalarChart := by
  change (consistency (vacuum + t • vacuum)).det ≠ 0
  have scaled : vacuum + t • vacuum = (1+t) • vacuum := by
    rw [add_smul, one_smul]
  rw [scaled, consistency_scale, LinearMap.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (ne_of_gt positive)) source_determinant_ne_zero

theorem radial_square_defect (x : Scalar) :
    2 * (‖vacuum‖ ^ 2 + ‖x‖ ^ 2) - ‖vacuum + x‖ ^ 2 = ‖x - vacuum‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_comm x vacuum]
  ring

theorem radial_square_bound (x : Scalar) :
    ‖vacuum + x‖ ^ 2 ≤ 2 * (‖vacuum‖ ^ 2 + ‖x‖ ^ 2) := by
  have h := radial_square_defect x
  nlinarith [sq_nonneg ‖x - vacuum‖]

#print axioms radial_orbit_zero
#print axioms source_ray_regular
#print axioms radial_square_bound
end
end LowEnergy.SourceNativeHistoryRadial
