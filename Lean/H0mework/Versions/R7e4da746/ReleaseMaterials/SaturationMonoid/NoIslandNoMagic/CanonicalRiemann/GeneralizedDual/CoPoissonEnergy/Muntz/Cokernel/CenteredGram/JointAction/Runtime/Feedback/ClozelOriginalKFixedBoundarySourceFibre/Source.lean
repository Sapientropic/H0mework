import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
import H0mework.Versions.R7e4da746.Arithmetic.RieszFiniteSource.SourceBoundary

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFixedBoundarySourceFibre
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

/-- The same source forcing generates a preimage at c/2 without dividing by c-star(c). -/
def regularInput (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) : BurnolL2 :=
  -(1/2 : ℂ) • regularForcing coordinate i +
    ((1/4 : ℂ)*(coordinate.value-star coordinate.value)) •
      sourceResolvent coordinate (regularForcing coordinate i)

private theorem rightQuarter (coordinate : BurnolCompletedMellinCoordinate) :
    1/4 < (coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]

private theorem starRightQuarter (coordinate : BurnolCompletedMellinCoordinate) :
    1/4 < (star coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]

theorem regularInput_action (coordinate : BurnolCompletedMellinCoordinate) (i : Fin 2) :
    burnolDirectRightResolvent (coordinate.value/2) (regularInput coordinate i) = regularColumns coordinate i := by
  have identity := burnolDirectRightResolvent_identity (coordinate.value/2) (star coordinate.value/2)
    (rightQuarter coordinate) (starRightQuarter coordinate) (regularForcing coordinate i)
  change burnolDirectRightResolvent (coordinate.value/2) (regularForcing coordinate i) -
    sourceResolvent coordinate (regularForcing coordinate i) =
      (coordinate.value/2-star coordinate.value/2) •
        burnolDirectRightResolvent (coordinate.value/2)
          (sourceResolvent coordinate (regularForcing coordinate i)) at identity
  unfold regularInput regularColumns
  change (burnolDirectRightResolventCLM coordinate)
    (-(1/2 : ℂ) • regularForcing coordinate i +
      ((1/4 : ℂ)*(coordinate.value-star coordinate.value)) •
        sourceResolvent coordinate (regularForcing coordinate i)) = _
  rw [map_add,map_smul,map_smul]
  change -(1/2 : ℂ) • burnolDirectRightResolvent (coordinate.value/2) (regularForcing coordinate i) +
    ((1/4 : ℂ)*(coordinate.value-star coordinate.value)) •
      burnolDirectRightResolvent (coordinate.value/2)
        (sourceResolvent coordinate (regularForcing coordinate i)) = _
  linear_combination (norm := module) -(1/2 : ℂ) • identity

def regularSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∑ i : Fin 2,sourceCoefficients coordinate i • regularInput coordinate i

def wholeJump (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∑ i : Fin 2,sourceCoefficients coordinate i • jumpColumns i

theorem regular_source_action (coordinate : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (coordinate.value/2) (regularSource coordinate)+wholeJump coordinate =
      generatedK coordinate := by
  have generated : generatedK coordinate = ∑ i : Fin 2,sourceCoefficients coordinate i • sourceColumns coordinate i := by
    simp only [generatedK,Fin.sum_univ_two,sourceCoefficients,sourceColumns,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [generated]
  change (burnolDirectRightResolventCLM coordinate) (∑ i : Fin 2,sourceCoefficients coordinate i • regularInput coordinate i)+
    (∑ i : Fin 2,sourceCoefficients coordinate i • jumpColumns i) = _
  rw [map_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change sourceCoefficients coordinate i • burnolDirectRightResolvent (coordinate.value/2) (regularInput coordinate i)+_ = _
  rw [regularInput_action,←smul_add,←sourceColumns_from_regular_resolvent]

def finiteBoundaryAction (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) (value : BurnolL2) : BurnolL2 :=
  pairedMellinTranslationCharacter coordinate.value shift • value -
    (1/2 : ℂ) • (burnolMultiplicativeDilation shift value+burnolMultiplicativeDilation (-shift) value)

private theorem finiteBoundaryAction_add (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (left right : BurnolL2) :
    finiteBoundaryAction coordinate shift (left+right) =
      finiteBoundaryAction coordinate shift left+finiteBoundaryAction coordinate shift right := by
  unfold finiteBoundaryAction
  rw [map_add,map_add]
  module

theorem finiteBoundaryAction_R (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) (value : BurnolL2) :
    burnolDirectRightResolvent (coordinate.value/2) (finiteBoundaryAction coordinate shift value) =
      finiteBoundaryAction coordinate shift (burnolDirectRightResolvent (coordinate.value/2) value) := by
  unfold finiteBoundaryAction
  change (burnolDirectRightResolventCLM coordinate)
    (pairedMellinTranslationCharacter coordinate.value shift • value -
      (1/2 : ℂ) • (burnolMultiplicativeDilation shift value+burnolMultiplicativeDilation (-shift) value)) = _
  rw [map_sub,map_smul,map_smul,map_add]
  change pairedMellinTranslationCharacter coordinate.value shift •
    burnolDirectRightResolvent (coordinate.value/2) value - (1/2 : ℂ) •
      (burnolDirectRightResolvent (coordinate.value/2) (burnolMultiplicativeDilation shift value)+
        burnolDirectRightResolvent (coordinate.value/2) (burnolMultiplicativeDilation (-shift) value)) = _
  rw [burnolDirectRightResolvent_dilation,burnolDirectRightResolvent_dilation]

def boundaryInput (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  finiteBoundaryAction coordinate shift (regularSource coordinate)

def rawBoundaryJump (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  finiteBoundaryAction coordinate shift (wholeJump coordinate)

/-- Both signs and both translated endpoints of the original C/FC edges survive. -/
theorem rawBoundaryJump_source (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    rawBoundaryJump coordinate shift =
      sourceCoefficients coordinate 0 •
        (pairedMellinTranslationCharacter coordinate.value shift • ConstantDual.seed -
          (1/2 : ℂ) • (burnolMultiplicativeDilation shift ConstantDual.seed+
            burnolMultiplicativeDilation (-shift) ConstantDual.seed))-
      sourceCoefficients coordinate 1 •
        (pairedMellinTranslationCharacter coordinate.value shift • fourierL2 ConstantDual.seed -
          (1/2 : ℂ) • (burnolMultiplicativeDilation shift (fourierL2 ConstantDual.seed)+
            burnolMultiplicativeDilation (-shift) (fourierL2 ConstantDual.seed))) := by
  unfold rawBoundaryJump finiteBoundaryAction wholeJump
  simp only [Fin.sum_univ_two,jumpColumns,Matrix.cons_val_zero,Matrix.cons_val_one,
    smul_neg,map_add,map_smul,map_neg]
  module

def sourceNormal (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolDirectRightResolvent (coordinate.value/2) (boundaryInput coordinate shift)+rawBoundaryJump coordinate shift

theorem sourceNormal_generated (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    sourceNormal coordinate shift = finiteBoundaryAction coordinate shift (generatedK coordinate) := by
  unfold sourceNormal boundaryInput rawBoundaryJump
  rw [finiteBoundaryAction_R,←finiteBoundaryAction_add,regular_source_action]

/-- The correction is computed by the original two source gaps and the original B block. -/
def sourceGaps (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :=
  burnolAmbientMeanZeroBlockRhs (sourceNormal coordinate shift)

def sourceBCorrection (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  burnolAmbientEvenPart
    (burnolQuarterZeroExtension (burnolMeanZeroBlockFirst (sourceGaps coordinate shift) : BurnolQuarterIntervalL2)+
      fourierL2 (burnolQuarterZeroExtension (burnolMeanZeroBlockSecond (sourceGaps coordinate shift) : BurnolQuarterIntervalL2)))

def sourceProjectionLoss (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  sourceNormal coordinate shift-burnolAmbientEvenPart (sourceNormal coordinate shift)+sourceBCorrection coordinate shift

def boundaryJump (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolL2 :=
  rawBoundaryJump coordinate shift-sourceProjectionLoss coordinate shift

theorem sourceProjectionLoss_actual (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    sourceProjectionLoss coordinate shift = sourceNormal coordinate shift-
      (burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2) := by
  rw [show (burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2) =
    burnolAmbientExtendedSonineProjectionFormula (sourceNormal coordinate shift) from
      burnolEvenOrthogonalProjectionOnto_eq_resolventFormula _]
  change sourceNormal coordinate shift-burnolAmbientEvenPart (sourceNormal coordinate shift)+
    burnolAmbientEvenMeanZeroCorrection (sourceNormal coordinate shift) = _
  unfold burnolAmbientExtendedSonineProjectionFormula
  module

theorem sourceProjectionLoss_orthogonal (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (sourceProjectionLoss coordinate shift) (value : BurnolL2) = 0 := by
  rw [sourceProjectionLoss_actual]
  exact (evenBurnolClosedFace (1/4 : ℝ)).toSubmodule.starProjection_inner_eq_zero _ _ value.property

theorem source_fibre_projection (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2) =
      burnolDirectRightResolvent (coordinate.value/2) (boundaryInput coordinate shift)+boundaryJump coordinate shift := by
  rw [boundaryJump,sourceProjectionLoss_actual]
  unfold sourceNormal
  module

theorem source_fibre_loss_energy (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    ‖sourceNormal coordinate shift‖^2 =
      ‖burnolDirectRightResolvent (coordinate.value/2) (boundaryInput coordinate shift)+boundaryJump coordinate shift‖^2+
        ‖sourceProjectionLoss coordinate shift‖^2 := by
  have orthogonal := sourceProjectionLoss_orthogonal coordinate shift (burnolEvenAmbientProjection (sourceNormal coordinate shift))
  have paired := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2) (sourceProjectionLoss coordinate shift)
    (inner_eq_zero_symm.mp orthogonal)
  rw [sourceProjectionLoss_actual] at paired
  have total : (burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2)+
    (sourceNormal coordinate shift-(burnolEvenAmbientProjection (sourceNormal coordinate shift) : BurnolL2)) =
      sourceNormal coordinate shift := by module
  rw [total] at paired
  rw [source_fibre_projection] at paired
  rw [sourceProjectionLoss_actual,source_fibre_projection]
  simpa only [pow_two] using paired

private theorem paired_character (coordinate : ℂ) (shift : ℝ) :
    (1/2 : ℂ)*(fullMellinTranslationCharacter coordinate shift+fullMellinTranslationCharacter coordinate (-shift)) =
      pairedMellinTranslationCharacter coordinate shift := by
  rw [pairedMellinTranslationCharacter,reciprocalMellinTranslationCharacter_eq_negativeShift]
  ring

theorem finiteBoundaryAction_source (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    finiteBoundaryAction coordinate shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      (pairedMellinTranslationCharacter coordinate.value shift-
        pairedMellinTranslationCharacter (star coordinate.value) shift) •
          (burnolCompletedMellinRieszVector coordinate : BurnolL2)-
      (1/2 : ℂ) • (OriginalRieszFiniteSource.forcingIntegral coordinate shift+
        OriginalRieszFiniteSource.forcingIntegral coordinate (-shift)) := by
  unfold finiteBoundaryAction
  rw [OriginalRieszFiniteSource.original_finite_action,OriginalRieszFiniteSource.original_finite_action]
  have character := paired_character (star coordinate.value) shift
  rw [←character]
  module

/-- Complete same-source boundary fibre; the full B correction remains in J. -/
theorem boundary_source_fibre (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolL2) =
      burnolDirectRightResolvent (coordinate.value/2) (boundaryInput coordinate shift)+boundaryJump coordinate shift := by
  rw [←source_fibre_projection,sourceNormal_generated,generatedK_eq_original,finiteBoundaryAction_source]
  have source := OriginalRieszFiniteSource.original_boundary coordinate zero shift
  have ambient := congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) source
  rw [map_sub,map_smul,map_smul]
  have fixed : burnolEvenAmbientProjection
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) = burnolCompletedMellinRieszVector coordinate := by
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (burnolCompletedMellinRieszVector coordinate)
  rw [fixed]
  change _ = (pairedMellinTranslationCharacter coordinate.value shift-
    pairedMellinTranslationCharacter (star coordinate.value) shift) •
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)-
    (1/2 : ℂ) • (burnolEvenAmbientProjection (OriginalRieszFiniteSource.forcingIntegral coordinate shift+
      OriginalRieszFiniteSource.forcingIntegral coordinate (-shift)) : BurnolL2)
  exact ambient

theorem fixedShiftBoundary_source_fibre (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero (Real.log stageZeroSonineQ) : BurnolL2) =
      burnolDirectRightResolvent (coordinate.value/2) (boundaryInput coordinate (Real.log stageZeroSonineQ))+
        boundaryJump coordinate (Real.log stageZeroSonineQ) :=
  boundary_source_fibre coordinate zero _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFixedBoundarySourceFibre
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
