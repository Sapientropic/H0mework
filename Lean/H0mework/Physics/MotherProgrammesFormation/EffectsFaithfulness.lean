import H0mework.Physics.MotherProgrammesFormation.EffectsCoframe

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceMaterialEffects

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageEightDiscreteFormation

noncomputable section

theorem coframe_eq_iff_coefficients (first last : SmoothUnifiedSource) :
    first.legacy.coframeAt = last.legacy.coframeAt ↔
      first.stageEight.coframeLinearCoefficient = last.stageEight.coframeLinearCoefficient := by
  constructor
  · intro equal
    funext direction row column
    rw [← derivative_readback first direction row column 0,
      ← derivative_readback last direction row column 0, equal]
  · intro equal
    funext point row column
    simp only [ProofFreeRicherAnholonomicSource.Source.coframeAt, Matrix.of_apply]
    change _ + ∑ direction, first.stageEight.coframeLinearCoefficient direction row column * point direction =
      _ + ∑ direction, last.stageEight.coframeLinearCoefficient direction row column * point direction
    rw [equal]

theorem parent_eq_of_material (first last : SmoothUnifiedSource)
    (discrete : readMaterial first = readMaterial last)
    (coframe : first.stageEight.coframeLinearCoefficient = last.stageEight.coframeLinearCoefficient) :
    first.stageEight = last.stageEight := by
  have root : first.stageEight.sourceRoot = last.stageEight.sourceRoot :=
    congrArg (fun material : Material => fun index => material.1 (.inl index)) discrete
  have potential : first.stageEight.p506PhasePotential = last.stageEight.p506PhasePotential :=
    congrArg (fun material : Material => fun index => material.1 (.inr index)) discrete
  have moves : first.stageEight.sourceMoves = last.stageEight.sourceMoves :=
    congrArg (fun material : Material => material.2.1) discrete
  have sigma : first.stageEight.sigmaSeed = last.stageEight.sigmaSeed :=
    congrArg (fun material : Material => material.2.2.1) discrete
  have color : first.stageEight.colorScale = last.stageEight.colorScale :=
    congrArg (fun material : Material => material.2.2.2) discrete
  cases first with
  | mk first firstContact =>
    cases last with
    | mk last lastContact =>
      cases first
      cases last
      simp_all

/-- The homogeneous accepted Cartan field does not replace the earlier
source-native coframe and continuous bridge. Their own actual effects jointly
retain every continuous material coordinate. -/
theorem source_eq_iff_material_effects (first last : SmoothUnifiedSource) :
    first = last ↔ readMaterial first = readMaterial last ∧
      first.legacy.coframeAt = last.legacy.coframeAt ∧
      (generatedUnitaryFlow first).evolve = (generatedUnitaryFlow last).evolve := by
  constructor
  · intro equal
    subst last
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨discrete, coframe, flow⟩
    exact source_eq_of_actual_flow first last
      (parent_eq_of_material first last discrete ((coframe_eq_iff_coefficients first last).1 coframe)) flow

theorem different_continuous_material_has_effect (first last : SmoothUnifiedSource)
    (discrete : readMaterial first = readMaterial last) (different : first ≠ last) :
    (∃ point : BasePoint,
      Matrix.det (first.legacy.coframeAt point) ≠ 0 ∧
      Matrix.det (last.legacy.coframeAt point) ≠ 0 ∧
      first.legacy.coframeAt point ≠ last.legacy.coframeAt point) ∨
    (∃ time : ℝ, (generatedUnitaryFlow first).evolve time ≠ (generatedUnitaryFlow last).evolve time) := by
  by_cases coframe : first.stageEight.coframeLinearCoefficient = last.stageEight.coframeLinearCoefficient
  · right
    have parent := parent_eq_of_material first last discrete coframe
    have rate : first.continuousContactRate ≠ last.continuousContactRate := by
      intro equal
      exact different (source_eq_of_actual_flow first last parent ((flow_eq_iff_rate first last).2 equal))
    exact ⟨separatingTime first last, different_rate_separates_actual_flow first last rate⟩
  · left
    have coordinate : ∃ direction row column,
        first.stageEight.coframeLinearCoefficient direction row column ≠
          last.stageEight.coframeLinearCoefficient direction row column := by
      by_contra none
      push Not at none
      exact coframe (funext fun direction => funext fun row => funext fun column => none direction row column)
    obtain ⟨direction, row, column, differentCoordinate⟩ := coordinate
    obtain ⟨point, firstLegal, lastLegal, effect⟩ :=
      different_coframe_has_legal_effect first last direction row column differentCoordinate
    exact ⟨point, firstLegal, lastLegal, fun same => effect (congrArg (fun field => field row column) same)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceMaterialEffects
