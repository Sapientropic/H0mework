import H0mework.Physics.QuantumState.SourceRestriction
import H0mework.Physics.QuantumState.StateSource
import H0mework.Physics.Holonomic.GeneratedHolonomicChartAction
import H0mework.Physics.DualVariation.LocalSpinAction

/-! The occupied frame moves inside the full Dirac/exterior carrier.
Its dual coordinates use inverse pullback, so no full SU7 or Spin action is
assumed to preserve the original color doublet or its ambient Hermitian form.
All quantum stars and effects are read in the jointly transported preparation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Source.Frame

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair SU7ExteriorMatterRepresentation
open StageNineSpinMatterBundle StageNineGlobalBundle
open StageNineEnrichedProofFreeSource StageNineGlobalConnection
open StageNineSourceGeneratedHolonomicChartAction
open StageNineDiracDualFormNativeLocalSpinAction

noncomputable section

abbrev Action := DiracExteriorMatterCarrier ≃ₗ[ℂ] DiracExteriorMatterCarrier

def embedding : (Index → ℂ) →ₗ[ℂ] DiracExteriorMatterCarrier where
  toFun values := sourceColorDiracMatter (fun spin color => values (spin, color))
  map_add' first second := by
    funext spin
    simp [sourceColorDiracMatter, add_smul, Finset.sum_add_distrib]
  map_smul' scalar values := by
    funext spin
    simp [sourceColorDiracMatter, smul_smul]

def coordinates : DiracExteriorMatterCarrier →ₗ[ℂ] (Index → ℂ) where
  toFun matter index := sourceColorDoubletDual index.2 (matter index.1)
  map_add' first second := by
    funext index
    exact map_add _ _ _
  map_smul' scalar matter := by
    funext index
    exact (sourceColorDoubletDual index.2).map_smul scalar (matter index.1)

def movedEmbedding (frame : Action) : (Index → ℂ) →ₗ[ℂ] DiracExteriorMatterCarrier :=
  frame.toLinearMap.comp embedding

def movedCoordinates (frame : Action) : DiracExteriorMatterCarrier →ₗ[ℂ] (Index → ℂ) :=
  coordinates.comp frame.symm.toLinearMap

theorem movedCoordinates_embedding (frame : Action) (values : Index → ℂ) :
    movedCoordinates frame (movedEmbedding frame values) = values := by
  funext index
  simp only [movedCoordinates, movedEmbedding, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact sourceColorDoubletDual_diracMatter _ _ _

theorem transformed_actual_reconstruction (frame : Action) (point : BasePoint) :
    movedEmbedding frame (amplitude point) = frame (actual.matter point) := rfl

theorem transformed_actual_coordinates (frame : Action) (point : BasePoint) :
    movedCoordinates frame (frame (actual.matter point)) = amplitude point := by
  rw [← transformed_actual_reconstruction frame point]
  exact movedCoordinates_embedding frame (amplitude point)

def prepare (frame : Action) (matter : DiracExteriorMatterCarrier) (index : Index) : ℂ :=
  movedCoordinates frame matter index / 2

theorem transformed_actual_prepare (frame : Action) (point : BasePoint) :
    prepare frame (frame (actual.matter point)) = vector point := by
  funext index
  rw [prepare, transformed_actual_coordinates]
  rfl

/-- An occupied operator on the full ambient carrier. Its unit is the
occupied projection; this definition does not assert ambient unitality. -/
def observableAction (frame : Action) (observable : Matrix Index Index ℂ) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  (movedEmbedding frame).comp ((Matrix.mulVecLin observable).comp (movedCoordinates frame))

theorem observableAction_transformed (frame : Action) (observable : Matrix Index Index ℂ)
    (matter : DiracExteriorMatterCarrier) :
    observableAction frame observable (frame matter) =
      frame (observableAction (LinearEquiv.refl ℂ _) observable matter) := by
  simp only [observableAction, movedEmbedding, movedCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_toLinearMap, LinearEquiv.refl_symm, LinearMap.id_apply]

theorem observableAction_actual_coordinates (frame : Action) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    movedCoordinates frame (observableAction frame observable (frame (actual.matter point))) =
      observable *ᵥ amplitude point := by
  change movedCoordinates frame (movedEmbedding frame
    (observable *ᵥ movedCoordinates frame (frame (actual.matter point)))) = _
  rw [movedCoordinates_embedding, transformed_actual_coordinates]

theorem independentDual_response (frame : Action) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    ((actual.conjugateMatter point).comp frame.symm.toLinearMap)
        (observableAction frame observable (frame (actual.matter point))) =
      actual.conjugateMatter point
        (observableAction (LinearEquiv.refl ℂ _) observable (actual.matter point)) := by
  rw [observableAction_transformed]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

def effect (frame : Action) (reference : BasePoint) : State.Effect where
  matrix := State.pureMatrix (prepare frame (frame (actual.matter reference)))
  positive := State.pureMatrix_posSemidef _
  complement_positive := by
    rw [transformed_actual_prepare]
    exact State.pureMatrix_complement_posSemidef _ (vector_inner_self reference)

theorem effect_eq_source (frame : Action) (reference : BasePoint) :
    effect frame reference = State.sourceEffect reference := by
  simp only [effect, State.sourceEffect, transformed_actual_prepare]

theorem quantum_evaluation (frame : Action) (point reference : BasePoint) :
    State.vectorEvaluation (prepare frame (frame (actual.matter point)))
        (effect frame reference).matrix =
      State.evaluation point (State.sourceEffect reference).matrix := by
  rw [transformed_actual_prepare, effect_eq_source]
  rfl

theorem quantum_star_evaluation (frame : Action) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    State.vectorEvaluation (prepare frame (frame (actual.matter point))) (star observable) =
      State.evaluation point (star observable) := by
  rw [transformed_actual_prepare]
  rfl

def representationAction {G : Type*} [Group G]
    (representation : Representation ℂ G DiracExteriorMatterCarrier) (element : G) : Action where
  toLinearMap := representation element
  invFun := representation element⁻¹
  left_inv := representation.inv_self_apply element
  right_inv := representation.self_inv_apply element

def gaugeFrame (element : SU7MotherGroup) : Action :=
  representationAction diracExteriorMatterGaugeRepresentation element

def spinFrame (element : SpinPlus13) : Action :=
  representationAction spinDiracMatterRepresentation element

def totalFrame (element : TotalStructureGroup) : Action :=
  representationAction totalDiracExteriorMatterRepresentation element

theorem full_SU7_coordinates (element : SU7MotherGroup) (point : BasePoint) :
    movedCoordinates (gaugeFrame element)
        (diracExteriorMatterGaugeRepresentation element (actual.matter point)) = amplitude point :=
  transformed_actual_coordinates (gaugeFrame element) point

theorem total_spin_SU7_reconstruction (element : TotalStructureGroup) (point : BasePoint) :
    movedEmbedding (totalFrame element) (amplitude point) =
      totalDiracExteriorMatterRepresentation element (actual.matter point) := rfl

theorem total_spin_SU7_quantum_evaluation
    (element : TotalStructureGroup) (point reference : BasePoint) :
    State.vectorEvaluation
        (prepare (totalFrame element)
          (totalDiracExteriorMatterRepresentation element (actual.matter point)))
        (effect (totalFrame element) reference).matrix =
      State.evaluation point (State.sourceEffect reference).matrix :=
  quantum_evaluation (totalFrame element) point reference

theorem localSpin_prepare (spinField : BasePoint → SpinPlus13) (point : BasePoint) :
    prepare (spinFrame (spinField point))
        ((localSpinDiracDualFormNativeAction spinField actual).matter point) = vector point :=
  transformed_actual_prepare (spinFrame (spinField point)) point

theorem localSpin_quantum_evaluation
    (spinField : BasePoint → SpinPlus13) (point reference : BasePoint) :
    State.vectorEvaluation
        (prepare (spinFrame (spinField point))
          ((localSpinDiracDualFormNativeAction spinField actual).matter point))
        (effect (spinFrame (spinField reference)) reference).matrix =
      State.evaluation point (State.sourceEffect reference).matrix := by
  rw [localSpin_prepare, effect_eq_source]
  rfl

theorem localSpin_independentDual_response
    (spinField : BasePoint → SpinPlus13) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    (localSpinDiracDualFormNativeAction spinField actual).conjugateMatter point
        (observableAction (spinFrame (spinField point)) observable
          ((localSpinDiracDualFormNativeAction spinField actual).matter point)) =
      actual.conjugateMatter point
        (observableAction (LinearEquiv.refl ℂ _) observable (actual.matter point)) :=
  independentDual_response (spinFrame (spinField point)) point observable

def chartFrame (initial terminal : StageNineChart) (point : BasePoint) : Action :=
  gaugeFrame (generatedTransition positiveSmoothUnifiedSource initial terminal point)

theorem source_chart_prepare (initial terminal : StageNineChart) (point : BasePoint) :
    prepare (chartFrame initial terminal point)
        ((sourceGeneratedHolonomicChartAction positiveSmoothUnifiedSource initial terminal
          actual).matter point) = vector point :=
  transformed_actual_prepare (chartFrame initial terminal point) point

theorem source_chart_quantum_evaluation
    (initial terminal : StageNineChart) (point reference : BasePoint) :
    State.vectorEvaluation
        (prepare (chartFrame initial terminal point)
          ((sourceGeneratedHolonomicChartAction positiveSmoothUnifiedSource initial terminal
            actual).matter point))
        (effect (chartFrame initial terminal reference) reference).matrix =
      State.evaluation point (State.sourceEffect reference).matrix := by
  rw [source_chart_prepare, effect_eq_source]
  rfl

theorem source_chart_independentDual_response
    (initial terminal : StageNineChart) (point : BasePoint)
    (observable : Matrix Index Index ℂ) :
    (sourceGeneratedHolonomicChartAction positiveSmoothUnifiedSource initial terminal actual).conjugateMatter
        point
        (observableAction (chartFrame initial terminal point) observable
          ((sourceGeneratedHolonomicChartAction positiveSmoothUnifiedSource initial terminal
            actual).matter point)) =
      actual.conjugateMatter point
        (observableAction (LinearEquiv.refl ℂ _) observable (actual.matter point)) :=
  independentDual_response (chartFrame initial terminal point) point observable

theorem wrong_fixed_frame_reads_double :
    coordinates (spinDiracMatterRepresentation spinDilation (actual.matter 0)) (0, 1) = 2 := by
  change sourceColorDoubletDual 1
    (diracMatrixMatterAction (spinDiracMatrix spinDilation)
      (sourceColorDiracMatter (spinPairCoefficients (upperPhase 0) (lowerPhase 0))) 0) = 2
  rw [sourceColorDoubletDual_diracMatrix]
  simp only [StageNineDiracDualYukawaSpinJurisdiction.spinDiracMatrix_spinDilation_row_zero]
  simp [spinPairCoefficients, upperPhase, phase_zero]

theorem wrong_fixed_frame_changes_actual_coordinates :
    coordinates (spinDiracMatterRepresentation spinDilation (actual.matter 0)) ≠ amplitude 0 := by
  intro same
  have value := congrFun same (0, 1)
  rw [wrong_fixed_frame_reads_double] at value
  norm_num [amplitude, spinPairCoefficients, upperPhase, phase_zero] at value

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Source.Frame
