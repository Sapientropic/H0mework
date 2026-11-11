import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusUnitSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRActionSource
open Complex MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalKCrossParameterRAdjointSource OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
local notation "q" => (1 / 4 : ℝ)
local notation "F" => fourierL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coordinate" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "response" => OriginalWholeDebtRJointMobiusUnitSource.response coordinate
local notation "programme" => OriginalNextEndpointProgramme.programmePrice coordinate (Real.log stageZeroSonineQ)

def sourceInput : BurnolPaAmbientCarrier :=
  evenFaceFourierEquiv q
    ⟨response, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩

/-- Actual R acts on this source's Fourier face; no value is admitted to the old actor sequence. -/
def sourceNext : BurnolL2 :=
  burnolDirectRightResolventCLM coordinate (sourceInput observation nontrivial half : BurnolL2)

private theorem input_price :
    inner ℂ (F (OriginalKSourceResolventReconstruction.generatedK coordinate))
      (sourceInput observation nontrivial half : BurnolL2) = -programme := by
  calc
    _ = inner ℂ (K coordinate : BurnolL2) response := by
      change inner ℂ (F (OriginalKSourceResolventReconstruction.generatedK coordinate)) (F response) = _
      rw [fourierL2.inner_map_map, OriginalKSourceResolventReconstruction.generatedK_eq_original]
    _ = -programme := by
      rw [OriginalWholeDebtRJointMobiusUnitSource.actual_programme_price observation nontrivial half, neg_neg]

/-- The complete existing original R/B producer emits the original programme as its outside coefficient. -/
theorem actual_source_effect :
    outside (sourceNext observation nontrivial half) =
      (2 * programme) • PhysicalOutsideSource.physicalOutsideColumn coordinate := by
  have actual := PhysicalOutsideSource.original_R_physical_outside_source coordinate
    (sourceInput observation nontrivial half)
  change outside (sourceNext observation nontrivial half) =
    (-2 * inner ℂ (F (OriginalKSourceResolventReconstruction.generatedK coordinate))
      (sourceInput observation nontrivial half : BurnolL2)) • _ at actual
  rw [input_price observation nontrivial half] at actual
  have scalar : (-2 : ℂ) * (-programme) = 2 * programme := by ring
  rw [scalar] at actual
  exact actual

theorem actual_complete_update :
    sourceNext observation nontrivial half =
      (burnolEvenAmbientProjection (sourceNext observation nontrivial half) : BurnolL2) +
        (2 * programme) • PhysicalOutsideSource.physicalOutsideColumn coordinate := by
  have split := (evenBurnolClosedFace q).toSubmodule.starProjection_add_starProjection_orthogonal
    (sourceNext observation nontrivial half)
  change (burnolEvenAmbientProjection (sourceNext observation nontrivial half) : BurnolL2) +
    outside (sourceNext observation nontrivial half) = sourceNext observation nontrivial half at split
  rw [actual_source_effect observation nontrivial half] at split
  exact split.symm

/-- The independent full Cayley consumer retains the entire original B-power cost. -/
theorem actual_programme_energy :
    ‖(sourceInput observation nontrivial half : BurnolL2)‖ ^ 2 -
      ‖(sourceInput observation nontrivial half : BurnolL2) +
        (CayleyEnergySource.sourceDamping coordinate : ℂ) •
          (burnolEvenAmbientProjection (sourceNext observation nontrivial half) : BurnolL2)‖ ^ 2 =
      4 * CayleyEnergySource.sourceDamping coordinate ^ 2 *
        ‖hPowerPhysicalCorrection (barC coordinate)‖ ^ 2 * ‖programme‖ ^ 2 := by
  have actual := CayleyEnergySource.physical_forward_exact_loss coordinate
    (sourceInput observation nontrivial half)
  rw [input_price observation nontrivial half, norm_neg] at actual
  exact actual

private theorem outsideColumn_ne_zero : PhysicalOutsideSource.physicalOutsideColumn coordinate ≠ 0 := by
  unfold PhysicalOutsideSource.physicalOutsideColumn
  intro zero
  apply UnweightedCayleySource.powerCorrection_ne_zero (barC coordinate)
  have read := congrArg F zero
  simpa only [fourierL2.apply_symm_apply, map_zero] using read

/-- This reads the generated full effect; no terminal condition selects its source action. -/
theorem actual_effect_zero_iff :
    outside (sourceNext observation nontrivial half) = 0 ↔ programme = 0 := by
  rw [actual_source_effect observation nontrivial half, smul_eq_zero]
  simp only [outsideColumn_ne_zero observation nontrivial half, or_false,
    mul_eq_zero, two_ne_zero, false_or]

end OriginalWholeDebtRJointMobiusRActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
