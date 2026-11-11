import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.FourierAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction
open scoped InnerProductSpace

/-- The complete original four-entry source matrix aggregates to its actual vector and one common unit/shell. -/
theorem sourceGram_aggregate_position (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients coordinate i)*sourceCoefficients coordinate j*
      calculatedSourceGram coordinate h i j) =
    finitePair coordinate h (gapZeroPart coordinate) (gapZeroPart coordinate) +
    (∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i)*
      inner ℂ (gapZeroPart coordinate) (outwardConstantShell h)/2 +
    star (∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i)*
      star (inner ℂ (gapZeroPart coordinate) (outwardConstantShell h))/2 +
    star (∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i)*
      (∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i)*
      ((Real.exp (-h/2) : ℂ)-pairedMellinTranslationCharacter coordinate.value h)/2 := by
  simp only [Fin.sum_univ_two,calculatedSourceGram,gapZeroPart,finitePair,map_add,map_smul,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,starRingEnd_apply,
    star_add,star_mul,star_star]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
 (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf
local notation "h" => Real.log stageZeroSonineQ
local notation "Gamma" => ∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i
local notation "X" => gapZeroPart c

/-- The original receipt residual consumes the complete matrix and both actual source means. -/
theorem installed_residual_aggregate_position :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual =
 finitePair c h X X + Gamma*inner ℂ X (outwardConstantShell h)/2 +
 star Gamma*star (inner ℂ X (outwardConstantShell h))/2 +
 star Gamma*Gamma*((Real.exp (-h/2) : ℂ)-pairedMellinTranslationCharacter (c).value h)/2 := by
  rw [installed_residual_calculated_position]
  exact sourceGram_aggregate_position c h

/-- Replacing the original kernel by X would discard these complete common-unit and shell terms. -/
theorem installed_unit_removal_effect :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual - finitePair c h X X =
 Gamma*inner ℂ X (outwardConstantShell h)/2 +
 star Gamma*star (inner ℂ X (outwardConstantShell h))/2 +
 star Gamma*Gamma*((Real.exp (-h/2) : ℂ)-pairedMellinTranslationCharacter (c).value h)/2 := by
  rw [installed_residual_aggregate_position]
  ring

/-- The explicit zero-coefficient override removes the unit in both the actual residual and actual L² energy. -/
theorem installed_gap_coefficient_zero (coefficientZero : Gamma=0) :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual = finitePair c h X X ∧
 ‖(installedOriginalKReceiptAt observation nontrivial rightHalf).kernel‖^2 = ‖X‖^2 := by
  constructor
  · rw [installed_residual_aggregate_position,coefficientZero]
    simp only [star_zero,zero_mul,zero_div,add_zero]
  · have energy := installed_kernel_gap_energy observation nontrivial rightHalf
    simpa only [coefficientZero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_div,add_zero] using energy

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
