import H0mework.Chemistry.LAlanineWholeCell.ReplayChecks
import H0mework.Chemistry.LAlanineParametric.Integrand
import H0mework.Chemistry.LAlanineSignedEvaluator.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData IntervalParameterMap WholeCellPartition
open ContinuousSeed ContinuousGradient ContinuousParameterMap SourceSignedField Set

noncomputable section

def SourceFieldLaw : Prop :=
  ∀ f : WholeCellSource.Field, ∀ x : Point, InRectangle (WholeCellSource.box f) x → FieldHolds (recordedField f) x

theorem four_step_source_fields (fields : SourceFieldLaw) (q : Quarter) :
    fourStepFieldsCertified (recordedFields q) SourceCellGeometry.initialJetBox (stepSizeInterval q)
      SourceCellGeometry.stepDerivativeInterval := by
  intro step
  have each (stage : Fin 4) (x : Point)
      (inside : VectorHolds (generatedStageInput q step stage).position x) :
      FieldHolds (recordedFields q step stage) x := by
    rw [every_source_input] at inside
    exact fields (sourceCall q step stage) x inside
  exact ⟨each 0, each 1, each 2, each 3⟩

theorem generated_target_contains (fields : SourceFieldLaw) (q : Quarter) (p : Point)
    (inside : p ∈ quarterDomain q) :
    JetHolds (generatedStates q 4) (parameterMap 0 4 p) (parameterJacobian 0 4 p) := by
  have result := fourStep_contains (recordedFields q) SourceCellGeometry.initialJetBox (stepSizeInterval q)
    SourceCellGeometry.stepDerivativeInterval (four_step_source_fields fields q)
    (initialMap 0 4 p) (bandSeedDerivative 4 (Geometry.Source.epsilon 0) p)
    (parameterTimeLinear 0 p) (parameterTimeLinear 0)
    (full_initial_jet p (quarter_subset_full q inside)) (quarter_step_size q p inside)
    SourceCellGeometry.cell_step_derivative (4 : Fin 5)
  simpa [parameterMap, parameterJacobian, SourceCellGeometry.source_step_count, generatedStates] using result

theorem generated_target_in_final_field (fields : SourceFieldLaw) (q : Quarter) (p : Point)
    (inside : p ∈ quarterDomain q) :
    InRectangle (WholeCellSource.box (finalField q)) (parameterMap 0 4 p) := by
  have bounded := (generated_target_contains fields q p inside).1
  intro axis
  rw [← final_field_is_generated_target]
  exact bounded axis

theorem final_laplacian_contains (fields : SourceFieldLaw) (q : Quarter) (p : Point)
    (inside : p ∈ quarterDomain q) :
    Holds (generatedTargetLaplacian q)
      (laplacian sourceTerms densityMatrix (parameterMap 0 4 p)) := by
  have hessian := (fields (finalField q) _ (generated_target_in_final_field fields q p inside)).2
  have hs := add_holds _ _ _ _ (add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds 0) (hessian 0 0)) (hessian 1 1)) (hessian 2 2)
  simp only [sourceHessian_diagonal] at hs
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis _)
  simpa [generatedTargetLaplacian, recordedField, hessianIndex,
    Fin.sum_univ_three, add_assoc] using hs

theorem final_jacobian_contains (fields : SourceFieldLaw) (q : Quarter) (p : Point)
    (inside : p ∈ quarterDomain q) :
    Holds (generatedTargetDeterminant q) (jacobianMatrix 0 4 p).det :=
  determinantPair_contains _ _ (generated_target_contains fields q p inside).2

theorem final_integrand_contains (fields : SourceFieldLaw) (q : Quarter) (p : Point)
    (inside : p ∈ quarterDomain q) : Holds (generatedTargetIntegrand q) (signedLaplacian 0 4 p) :=
  mul_holds _ _ _ _ (final_laplacian_contains fields q p inside) (final_jacobian_contains fields q p inside)

theorem quarter_integral_from_source_fields (fields : SourceFieldLaw) (q : Quarter) :
    Holds (integralPair (generatedTargetIntegrand q) (quarterLowerQ q) (quarterUpperQ q))
      (∫ p in quarterDomain q, signedLaplacian 0 4 p) :=
  integralPair_contains _ _ _ (fun axis => (quarter_ordered q axis).le)
    (signedLaplacian 0 4) (signedLaplacian_contDiff 0 4).continuous (final_integrand_contains fields q)

theorem common_jacobian_contains (fields : SourceFieldLaw) (p : Point) (inside : p ∈ fullDomain) :
    MatrixHolds commonJacobian (parameterJacobian 0 4 p) := by
  rw [fullDomain_eq_iUnion_quarters] at inside
  obtain ⟨q, hq⟩ := mem_iUnion.mp inside
  have localBound := (generated_target_contains fields q p hq).2
  intro i j
  have bound := localBound i j
  rw [target_derivative_recomputed] at bound
  exact ⟨(Rat.cast_le.mpr (quarter_inside_common_hull q i j).1).trans bound.1,
    bound.2.trans (Rat.cast_le.mpr (quarter_inside_common_hull q i j).2)⟩

theorem full_jacobian_positive (fields : SourceFieldLaw) (p : Point) (inside : p ∈ fullDomain) :
    0 < (jacobianMatrix 0 4 p).det := by
  rw [fullDomain_eq_iUnion_quarters] at inside
  obtain ⟨q, hq⟩ := mem_iUnion.mp inside
  have bound := (final_jacobian_contains fields q p hq).1
  rw [target_determinant_recomputed] at bound
  exact (Rat.cast_pos.mpr (determinant_positive q)).trans_le bound

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
