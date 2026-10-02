import H0mework.Versions.R2.Physics.MotherProgrammesFormationPotential.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.EffectsFaithfulness

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

theorem source_eq_iff_materials (visit : MotherVisit) (first last : Points) :
    sourceOf visit first = sourceOf visit last ↔ materials first = materials last := by
  constructor
  · intro equal
    funext slot
    refine Fin.cases ?_ ?_ slot
    · exact congrArg SmoothUnifiedSource.continuousContactResidual equal
    · intro coordinate
      have observed := congrArg (fun source : SmoothUnifiedSource =>
        source.stageEight.coframeLinearCoefficient
          (RationalSourceFormation.coframeIndex.symm coordinate).1
          (RationalSourceFormation.coframeIndex.symm coordinate).2.1
          (RationalSourceFormation.coframeIndex.symm coordinate).2.2) equal
      simpa [sourceOf, coframeMaterials] using observed
  · intro equal
    unfold sourceOf coframeMaterials
    rw [equal]

theorem source_effects_faithful (firstVisit lastVisit : MotherVisit) (first last : Points) :
    sourceOf firstVisit first = sourceOf lastVisit last ↔
      readMaterial (sourceOf firstVisit first) = readMaterial (sourceOf lastVisit last) ∧
      (sourceOf firstVisit first).legacy.coframeAt = (sourceOf lastVisit last).legacy.coframeAt ∧
      (generatedUnitaryFlow (sourceOf firstVisit first)).evolve =
        (generatedUnitaryFlow (sourceOf lastVisit last)).evolve :=
  SourceMaterialEffects.source_eq_iff_material_effects _ _

/-- The same actual potential displacement changes a native affine-coframe
effect at a common legal point or the original continuous unitary flow. -/
theorem nonzero_displacement_has_effect (visit : MotherVisit) (points displacement : Points)
    (nonzero : materials displacement ≠ 0) :
    (∃ point : BasePoint,
      Matrix.det ((sourceOf visit points).legacy.coframeAt point) ≠ 0 ∧
      Matrix.det ((sourceOf visit (points + displacement)).legacy.coframeAt point) ≠ 0 ∧
      (sourceOf visit points).legacy.coframeAt point ≠
        (sourceOf visit (points + displacement)).legacy.coframeAt point) ∨
      (∃ time : ℝ,
        (generatedUnitaryFlow (sourceOf visit points)).evolve time ≠
          (generatedUnitaryFlow (sourceOf visit (points + displacement))).evolve time) := by
  have changed : sourceOf visit (points + displacement) ≠ sourceOf visit points := by
    intro equal
    have read := (source_eq_iff_materials visit (points + displacement) points).1 equal
    rw [materials_increment] at read
    have zero : materials displacement = 0 :=
      add_left_cancel (show materials points + materials displacement = materials points + 0 by simpa using read)
    exact nonzero zero
  apply SourceMaterialEffects.different_continuous_material_has_effect
    (sourceOf visit points) (sourceOf visit (points + displacement))
  · rw [discrete_retained, discrete_retained]
  · exact Ne.symm changed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PotentialSourceFormation
