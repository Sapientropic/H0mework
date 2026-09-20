import H0mework.Realization.RelaxationFlow.P236

/-!
# Proposition 237: phase slices as linear isometric automorphisms

P234-P236 prove that the zero-target phase slice of the unified relaxation

`relaxModule 0 (1 - u) x`

is scalar multiplication by the residual phase `u`, that nonzero phases have
inverse phase slices, and that unit-norm phases preserve distance.  This file
bundles the same fact as a Lean object:

`E ≃ₗᵢ[ℂ] E`.

Boundary: this proves the scalar unit-norm phase slice is a linear isometric
automorphism of any complex normed vector carrier.  It is still not a
Hamiltonian generator theorem, a general Hilbert-space unitary-group theorem,
Schrödinger evolution, tensor geometry, or gauge transport.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Bundled phase-slice automorphism -/

/-- A nonzero residual phase gives a linear automorphism of a complex module via
the zero-target relaxation slice. -/
noncomputable def phaseRelaxModuleLinearEquiv
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : ℂ) (hu : u ≠ 0) :
    E ≃ₗ[ℂ] E where
  toFun := fun x => relaxModule (0 : E) (1 - u) x
  invFun := fun x => relaxModule (0 : E) (1 - u⁻¹) x
  left_inv := phase_relaxModule_left_inverse u hu
  right_inv := phase_relaxModule_right_inverse u hu
  map_add' := by
    intro x y
    rw [relaxModule_zero_target_eq_residual_smul,
      relaxModule_zero_target_eq_residual_smul,
      relaxModule_zero_target_eq_residual_smul]
    exact smul_add u x y
  map_smul' := by
    intro a x
    rw [relaxModule_zero_target_eq_residual_smul,
      relaxModule_zero_target_eq_residual_smul]
    rw [smul_smul, smul_smul, mul_comm]
    simp

@[simp]
theorem phaseRelaxModuleLinearEquiv_apply
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : ℂ) (hu : u ≠ 0) (x : E) :
    phaseRelaxModuleLinearEquiv (E := E) u hu x =
      relaxModule (0 : E) (1 - u) x := rfl

@[simp]
theorem phaseRelaxModuleLinearEquiv_symm_apply
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (u : ℂ) (hu : u ≠ 0) (x : E) :
    (phaseRelaxModuleLinearEquiv (E := E) u hu).symm x =
      relaxModule (0 : E) (1 - u⁻¹) x := rfl

/-- A unit-norm residual phase bundles to a linear isometric automorphism. -/
noncomputable def phaseRelaxModuleLinearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) (hu : ‖u‖ = 1) :
    E ≃ₗᵢ[ℂ] E where
  toLinearEquiv :=
    phaseRelaxModuleLinearEquiv (E := E) u (by
      intro hz
      have hnorm_zero : ‖u‖ = 0 := by simp [hz]
      rw [hu] at hnorm_zero
      norm_num at hnorm_zero)
  norm_map' := by
    intro x
    rw [phaseRelaxModuleLinearEquiv_apply]
    rw [relaxModule_zero_target_eq_residual_smul]
    rw [norm_smul, hu, one_mul]

@[simp]
theorem phaseRelaxModuleLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) (hu : ‖u‖ = 1) (x : E) :
    phaseRelaxModuleLinearIsometryEquiv (E := E) u hu x =
      relaxModule (0 : E) (1 - u) x := rfl

/-- The bundled isometric automorphism is exactly the same map as the
zero-target phase slice. -/
theorem phaseRelaxModuleLinearIsometryEquiv_toFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℂ) (hu : ‖u‖ = 1) :
    (phaseRelaxModuleLinearIsometryEquiv (E := E) u hu : E → E) =
      fun x => relaxModule (0 : E) (1 - u) x := rfl

/-- The scalar time phase `exp(i t)` yields a bundled linear isometric
automorphism. -/
noncomputable def unitComplexPhaseLinearIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) :
    E ≃ₗᵢ[ℂ] E :=
  phaseRelaxModuleLinearIsometryEquiv
    (E := E) (unitComplexPhase t) (unitComplexPhase_norm t)

@[simp]
theorem unitComplexPhaseLinearIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (x : E) :
    unitComplexPhaseLinearIsometryEquiv (E := E) t x =
      relaxModule (0 : E) (1 - unitComplexPhase t) x := rfl

/-- The bundled `exp(i t)` phase automorphisms compose according to time
addition. -/
theorem unitComplexPhaseLinearIsometryEquiv_apply_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t s : ℝ) (x : E) :
    unitComplexPhaseLinearIsometryEquiv (E := E) s
        (unitComplexPhaseLinearIsometryEquiv (E := E) t x) =
      unitComplexPhaseLinearIsometryEquiv (E := E) (t + s) x := by
  simp [phase_relaxModule_time_add]


end AffineRelaxation
end SaturationMonoid
