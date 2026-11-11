import H0mework.Realization.Topology.EquivariantDual

/-!
# Hilbert boundary of an equivariant generalized-dual residual

If the actual Hilbert action is an isometric equivalence, a nonzero bounded
eigenfunctional has unit-modulus character. Consequently a nonzero source
functional with nonunit character has a canonical nonzero equivariant
extension residual. The character law and nonzeroness are derived from the
source functional and extension square, not supplied as a positivity field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem EquivariantBoundedExtension.extension_ne_zero
    {feature : C →ₗ[ℂ] H} {action : H →L[ℂ] H}
    {character : ℂ} {functional : TestDual C}
    (extension : EquivariantBoundedExtension
      feature action character functional)
    (functional_ne_zero : functional ≠ 0) :
    extension.extension ≠ 0 := by
  intro extension_zero
  apply functional_ne_zero
  rw [← extension.restricts, extension_zero]
  rfl

theorem EquivariantBoundedExtension.character_norm_eq_one
    {feature : C →ₗ[ℂ] H}
    (action : H ≃ₗᵢ[ℂ] H)
    {character : ℂ} {functional : TestDual C}
    (extension : EquivariantBoundedExtension feature
      action.toContinuousLinearEquiv.toContinuousLinearMap
      character functional)
    (functional_ne_zero : functional ≠ 0) :
    ‖character‖ = 1 := by
  let actionMap :=
    action.toContinuousLinearEquiv.toContinuousLinearMap
  have norm_comp :
      ‖extension.extension.comp actionMap‖ = ‖extension.extension‖ := by
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
      extension.extension action
  have map_eq :
      extension.extension.comp actionMap =
        character • extension.extension := by
    apply ContinuousLinearMap.ext
    intro value
    change extension.extension (action value) =
      character * extension.extension value
    exact extension.eigenlaw value
  have norm_eq :
      ‖extension.extension‖ =
        ‖character‖ * ‖extension.extension‖ := by
    calc
      ‖extension.extension‖ =
          ‖extension.extension.comp actionMap‖ := norm_comp.symm
      _ = ‖character • extension.extension‖ := congrArg norm map_eq
      _ = ‖character‖ * ‖extension.extension‖ :=
        norm_smul character extension.extension
  have extension_norm_ne_zero : ‖extension.extension‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (extension.extension_ne_zero functional_ne_zero)
  apply mul_right_cancel₀ extension_norm_ne_zero
  simpa [one_mul] using norm_eq.symm

theorem character_norm_eq_one_of_residual_zero
    {feature : C →ₗ[ℂ] H}
    (action : H ≃ₗᵢ[ℂ] H)
    (character : ℂ) (functional : TestDual C)
    (functional_ne_zero : functional ≠ 0)
    (residual_zero : canonicalEquivariantExtensionResidual feature
      action.toContinuousLinearEquiv.toContinuousLinearMap
      character functional = 0) :
    ‖character‖ = 1 := by
  obtain ⟨extension⟩ :=
    (canonicalEquivariantExtensionResidual_eq_zero_iff feature
      action.toContinuousLinearEquiv.toContinuousLinearMap
      character functional).mp residual_zero
  exact extension.character_norm_eq_one action functional_ne_zero

theorem residual_ne_zero_of_character_norm_ne_one
    {feature : C →ₗ[ℂ] H}
    (action : H ≃ₗᵢ[ℂ] H)
    (character : ℂ) (functional : TestDual C)
    (functional_ne_zero : functional ≠ 0)
    (character_norm_ne_one : ‖character‖ ≠ 1) :
    canonicalEquivariantExtensionResidual feature
      action.toContinuousLinearEquiv.toContinuousLinearMap
      character functional ≠ 0 := by
  intro residual_zero
  exact character_norm_ne_one
    (character_norm_eq_one_of_residual_zero action character functional
      functional_ne_zero residual_zero)

end

end SourceGeneratedTestHilbertGeneralizedDual
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
