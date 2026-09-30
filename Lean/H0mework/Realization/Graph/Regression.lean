import H0mework.Realization.Graph.Action

/-!
# Regression for source-generated functional graph perfectification

The identity functional behind a zero old feature has a nonzero generalized
dual residual.  The graph construction retains that exact functional as a
second source coordinate and therefore generates its unique bounded extension
on the graph completion.  A zero functional generates the zero coordinate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectificationRegression

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

def zeroFeature : ℂ →ₗ[ℂ] ℂ := 0

def identityFunctional : ℂ →ₗ[ℂ] ℂ := LinearMap.id

def identityFeature : ℂ →ₗ[ℂ] ℂ := LinearMap.id

theorem zeroFeature_identity_originalResidual_ne_zero :
    canonicalExtensionResidual zeroFeature identityFunctional ≠ 0 := by
  intro residualZero
  obtain ⟨extension⟩ :=
    (canonicalExtensionResidual_eq_zero_iff_nonempty
      zeroFeature identityFunctional).mp residualZero
  have readback := LinearMap.congr_fun extension.restricts 1
  norm_num [zeroFeature, identityFunctional] at readback

theorem zeroFeature_identity_graph_kernel_bot :
    LinearMap.ker (graphFeature zeroFeature identityFunctional) = ⊥ := by
  rw [graphFeature_ker]
  simp [zeroFeature, identityFunctional]

theorem zeroFeature_identity_graph_source_injective :
    Function.Injective
      (canonicalHilbertMap
        (graphFeature zeroFeature identityFunctional)) := by
  rw [← LinearMap.ker_eq_bot]
  rw [canonicalHilbertMap_ker]
  exact zeroFeature_identity_graph_kernel_bot

theorem zeroFeature_identity_graph_readback :
    graphHilbertFunctional zeroFeature identityFunctional
        (canonicalHilbertMap
          (graphFeature zeroFeature identityFunctional) 1) = 1 := by
  simpa [identityFunctional] using
    graphHilbertFunctional_source_readback
      zeroFeature identityFunctional 1

theorem zeroFeature_identity_graphResidual_zero :
    canonicalExtensionResidual
        (canonicalHilbertMap
          (graphFeature zeroFeature identityFunctional))
        identityFunctional = 0 :=
  graphExtensionResidual_zero zeroFeature identityFunctional

theorem zeroFeature_identity_graphExtension_unique
    (other : GraphHilbertAmbient zeroFeature identityFunctional →L[ℂ] ℂ)
    (readback : other.toLinearMap.comp
      (canonicalHilbertMap
        (graphFeature zeroFeature identityFunctional)) =
      identityFunctional) :
    other = graphHilbertFunctional zeroFeature identityFunctional :=
  graphHilbertFunctional_unique zeroFeature identityFunctional other readback

theorem zeroFunctional_generates_zero_coordinate :
    graphHilbertFunctional identityFeature (0 : ℂ →ₗ[ℂ] ℂ) = 0 := by
  symm
  apply graphHilbertFunctional_unique
  rfl

theorem identity_graph_universal :
    ∃! extension : GraphHilbertAmbient identityFeature identityFunctional →L[ℂ] ℂ,
      extension.toLinearMap.comp
        (canonicalHilbertMap
          (graphFeature identityFeature identityFunctional)) =
        identityFunctional :=
  graphHilbertFunctional_universal identityFeature identityFunctional

def identityCovariance :
    GraphCovariance identityFeature identityFunctional where
  sourceAction := LinearMap.id
  hilbertAction := ContinuousLinearMap.id ℂ ℂ
  character := 1
  feature_covariance := by rfl
  functional_eigenlaw := by simp [identityFunctional]

theorem identity_action_source_residual_zero (value : ℂ) :
    graphActionNormResidual identityCovariance value = 0 := by
  simp [graphActionNormResidual, identityCovariance]

def identityGraphAmbientIsometry :
    GraphHilbertAmbient identityFeature identityFunctional →ₗᵢ[ℂ]
      GraphHilbertAmbient identityFeature identityFunctional :=
  graphHilbertLinearIsometry identityCovariance
    identity_action_source_residual_zero

theorem identity_action_completed_norm (value :
    GraphHilbertAmbient identityFeature identityFunctional) :
    ‖graphHilbertAction identityCovariance value‖ = ‖value‖ :=
  graphHilbertAction_norm_of_source_residual_zero identityCovariance
    identity_action_source_residual_zero value

theorem identity_action_character_law (value :
    GraphHilbertAmbient identityFeature identityFunctional) :
    graphHilbertFunctional identityFeature identityFunctional
        (graphHilbertAction identityCovariance value) =
      graphHilbertFunctional identityFeature identityFunctional value := by
  simpa [identityCovariance] using
    graphHilbertFunctional_eigenlaw identityCovariance value

theorem identity_graph_equivariantResidual_zero :
    canonicalEquivariantExtensionResidual
        (canonicalHilbertMap
          (graphFeature identityFeature identityFunctional))
        (graphHilbertAction identityCovariance) 1 identityFunctional = 0 :=
  graphEquivariantExtensionResidual_zero identityCovariance

/-- A source action that kills the source, with character zero. -/
def collapsingCovariance :
    GraphCovariance zeroFeature identityFunctional where
  sourceAction := 0
  hilbertAction := 0
  character := 0
  feature_covariance := by rfl
  functional_eigenlaw := by simp

theorem collapsing_action_has_explicit_residual :
    graphActionNormResidual collapsingCovariance 1 ≠ 0 := by
  change ‖WithLp.toLp 2 ((0 : ℂ), 0)‖ -
      ‖WithLp.toLp 2 ((0 : ℂ), 1)‖ ≠ 0
  simp

def IsIsometricDisposition :
    GraphActionDisposition identityCovariance → Prop
  | .isometric _ _ => True
  | .residual _ => False

theorem identity_action_settles_isometric :
    IsIsometricDisposition (settleGraphAction identityCovariance) := by
  unfold settleGraphAction
  split
  · trivial
  · rename_i notPreserves
    exact False.elim (notPreserves identity_action_source_residual_zero)

inductive HasResidualCoordinates :
    GraphActionDisposition collapsingCovariance → Prop
  | intro (coordinates : Nonempty {value : ℂ //
      graphActionNormResidual collapsingCovariance value ≠ 0}) :
      HasResidualCoordinates (.residual coordinates)

theorem collapsing_action_settles_residual :
    HasResidualCoordinates (settleGraphAction collapsingCovariance) := by
  unfold settleGraphAction
  split
  · rename_i preserves
    exact False.elim
      (collapsing_action_has_explicit_residual (preserves 1))
  · rename_i notPreserves
    exact .intro _

#print axioms zeroFeature_identity_originalResidual_ne_zero
#print axioms zeroFeature_identity_graph_kernel_bot
#print axioms zeroFeature_identity_graph_source_injective
#print axioms zeroFeature_identity_graph_readback
#print axioms zeroFeature_identity_graphResidual_zero
#print axioms zeroFeature_identity_graphExtension_unique
#print axioms zeroFunctional_generates_zero_coordinate
#print axioms identity_graph_universal
#print axioms identity_action_completed_norm
#print axioms identity_action_character_law
#print axioms identity_graph_equivariantResidual_zero
#print axioms identity_action_settles_isometric
#print axioms collapsing_action_has_explicit_residual
#print axioms collapsing_action_settles_residual

end

end SourceGeneratedFunctionalGraphPerfectificationRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
