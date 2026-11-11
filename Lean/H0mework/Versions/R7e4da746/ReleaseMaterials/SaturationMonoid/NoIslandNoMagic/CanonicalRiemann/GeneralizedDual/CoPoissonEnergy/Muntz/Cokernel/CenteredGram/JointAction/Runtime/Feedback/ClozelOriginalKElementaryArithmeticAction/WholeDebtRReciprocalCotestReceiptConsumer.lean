import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestReturnSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveRegisteredReceiptConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option cleanup.letToHave false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRReciprocalCotestReceiptConsumer
open Complex MeasureTheory BurnolPhysicalState OriginalRieszFiniteSynthesis FiniteMobiusResolventFlux
open OriginalWholeDebtRPowerWaveDilationSource OriginalKSourceResolventReconstruction
open OriginalWholeDebtRAdjointContactSource OriginalKPairedBEulerJunctionSource
open OriginalPaPhysicalGreen
open scoped InnerProductSpace
namespace A
export OriginalWholeDebtRReciprocalCotestActionSource
  (weight weightedField weighted_field_action actual_defect_fee)
end A
export OriginalWholeDebtRReciprocalCotestReturnSource (returnPrice)
namespace Q
export OriginalWholeDebtRReciprocalCotestReturnSource (actual_weighted_wave actual_rho)
end Q
namespace W
export OriginalKPowerWaveSourceWriteback (actualValue)
end W
open private actual_wave_source actual_return actual_pa_release from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveRegisteredReceiptConsumer
open private actualPaDelta from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRAdjointContactReceiptConsumer
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "wave" => W.actualValue observation nontrivial half depth
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation

private theorem actual_weighted_wave :
    A.weight c * inner ℂ (fourierL2 (generatedK c)) wave =
      returnPrice observation nontrivial half := by
  rw [actual_wave_source observation nontrivial half depth]
  exact Q.actual_weighted_wave observation nontrivial half

private theorem actual_pa_return :
    (∀ k : Nat, k < m → inner ℂ (sourceEffect c c)
      (CombSource.Division.rawIterate observation half.down k
        (actualPaDelta observation nontrivial half depth ordinal : BurnolL2)) = 0) ∧
    (A.weight c * (2 * kernelMass c)) * inner ℂ (sourceEffect c c)
      (CombSource.Division.rawIterate observation half.down m
        (actualPaDelta observation nontrivial half depth ordinal : BurnolL2)) =
      star (sigma c c) *
        (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3) -
          OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)) *
        ((-2 * e) * returnPrice observation nontrivial half) := by
  have paid := actual_pa_release observation nontrivial half depth ordinal
  refine ⟨paid.1, ?_⟩
  calc
    _ = A.weight c * ((2 * kernelMass c) * inner ℂ (sourceEffect c c)
        (CombSource.Division.rawIterate observation half.down m
          (actualPaDelta observation nontrivial half depth ordinal : BurnolL2))) := by ring
    _ = A.weight c * (star (sigma c c) *
        (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3) -
          OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)) *
          ((-2 * e) * inner ℂ (fourierL2 (generatedK c)) wave)) := congrArg _ paid.2
    _ = star (sigma c c) *
        (OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+3) -
          OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)) *
          ((-2 * e) * (A.weight c * inner ℂ (fourierL2 (generatedK c)) wave)) := by ring
    _ = _ := by rw [actual_weighted_wave]

private noncomputable def Result : Sort _ :=
  Σ' prior : type_of% (OriginalWholeDebtRPowerWaveRegisteredReceiptConsumer.actual_power_wave_registered_whole_next
      observation nontrivial half depth ordinal),
    PProd (prior = OriginalWholeDebtRPowerWaveRegisteredReceiptConsumer.actual_power_wave_registered_whole_next
      observation nontrivial half depth ordinal) (
  Σ' field : BurnolL2, PProd (field = A.weightedField c)
    ((type_of% (A.weighted_field_action c)) ∧
     (type_of% (A.actual_defect_fee observation nontrivial half)) ∧
     (type_of% (actual_weighted_wave observation nontrivial half depth)) ∧
     (type_of% (Q.actual_rho observation nontrivial half)) ∧
     (type_of% (actual_pa_return observation nontrivial half depth ordinal))))

/-- The source-generated cotest field pays the complete second-column defect fee. -/
noncomputable opaque actual_reciprocal_cotest_return : Result observation nontrivial half depth ordinal := by
  exact ⟨OriginalWholeDebtRPowerWaveRegisteredReceiptConsumer.actual_power_wave_registered_whole_next
      observation nontrivial half depth ordinal, rfl, A.weightedField c, rfl,
    A.weighted_field_action c, A.actual_defect_fee observation nontrivial half,
    actual_weighted_wave observation nontrivial half depth,
    Q.actual_rho observation nontrivial half,
    actual_pa_return observation nontrivial half depth ordinal⟩

end OriginalWholeDebtRReciprocalCotestReceiptConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
