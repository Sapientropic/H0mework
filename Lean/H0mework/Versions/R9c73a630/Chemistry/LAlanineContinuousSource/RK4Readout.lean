import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.RK4ReplayChecks
import H0mework.Versions.R9c73a630.Chemistry.LAlanineParametric.Integrand
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSignedEvaluator.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay

open SourceGaussianModel SourceSignedEvaluator SourceCellGeometry SourceRectangle IntervalParameterMap
open ContinuousSeed ContinuousGradient ContinuousParameterMap SourceSignedField Set

noncomputable section

def SourceFieldLaw : Prop :=
  ∀ field : SourceRectangle.Field, ∀ x : Point, InRectangle (actualBox field) x → FieldHolds (recordedField field) x

theorem four_step_source_fields (fields : SourceFieldLaw) :
    fourStepFieldsCertified recordedFields initialJetBox stepSizeInterval stepDerivativeInterval := by
  intro step
  have each (stage : Fin 4) (x : Point) (inside : VectorHolds (generatedStageInput step stage).position x) :
      FieldHolds (recordedFields step stage) x := by
    rw [every_source_input] at inside
    exact fields (sourceCall step stage) x inside
  exact ⟨each 0, each 1, each 2, each 3⟩

theorem generated_target_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    JetHolds (generatedStates 4) (parameterMap 0 4 p) (parameterJacobian 0 4 p) := by
  have result := fourStep_contains recordedFields initialJetBox stepSizeInterval stepDerivativeInterval
    (four_step_source_fields fields) (initialMap 0 4 p) (bandSeedDerivative 4
      (Geometry.Source.epsilon 0) p) (parameterTimeLinear 0 p) (parameterTimeLinear 0)
    (cell_initial_jet p inside) (cell_step_size p inside) cell_step_derivative (4 : Fin 5)
  simpa [parameterMap, parameterJacobian, source_step_count, generatedStates] using result

theorem generated_target_in_final_field (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    InRectangle (actualBox 16) (parameterMap 0 4 p) := by
  have bounded := (generated_target_contains fields p inside).1
  intro axis
  rw [← final_field_is_generated_target axis]
  exact bounded axis

theorem final_laplacian_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    Holds generatedTargetLaplacian
      (laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix (parameterMap 0 4 p)) := by
  have hessian := (fields 16 _ (generated_target_in_final_field fields p inside)).2
  have hs := add_holds _ _ _ _ (add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds 0) (hessian 0 0)) (hessian 1 1)) (hessian 2 2)
  simp only [sourceHessian_diagonal] at hs
  change Holds _ (∑ axis : Fin 3, secondBilinear SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix zeroJet zeroJet axis _)
  simpa [generatedTargetLaplacian, recordedField, hessianIndex,
    Fin.sum_univ_three, add_assoc] using hs

theorem final_jacobian_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    Holds generatedTargetDeterminant (jacobianMatrix 0 4 p).det :=
  determinantPair_contains _ _ (generated_target_contains fields p inside).2

theorem final_integrand_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    Holds generatedTargetIntegrand (signedLaplacian 0 4 p) :=
  mul_holds _ _ _ _ (final_laplacian_contains fields p inside) (final_jacobian_contains fields p inside)

theorem cell_integral_from_source_fields (fields : SourceFieldLaw) :
    Holds (integralPair generatedTargetIntegrand cellLowerQ cellUpperQ)
      (∫ p in cellDomain, signedLaplacian 0 4 p) :=
  integralPair_contains generatedTargetIntegrand cellLowerQ cellUpperQ (fun axis => (cell_ordered axis).le)
    (signedLaplacian 0 4) (signedLaplacian_contDiff 0 4).continuous (final_integrand_contains fields)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRK4Replay
