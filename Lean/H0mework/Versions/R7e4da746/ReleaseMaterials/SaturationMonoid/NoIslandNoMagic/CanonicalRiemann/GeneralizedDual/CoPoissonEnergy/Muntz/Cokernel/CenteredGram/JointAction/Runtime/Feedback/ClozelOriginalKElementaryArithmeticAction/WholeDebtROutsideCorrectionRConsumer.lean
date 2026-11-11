import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusContactPsiPriceSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtROutsideCorrectionRConsumer
open BurnolPhysicalState
open OriginalKPairedBEulerJunctionSource OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open scoped InnerProductSpace
open private correction_B from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
namespace S
export OriginalKOutsideCorrectionRSource
  (rResult rInput r_input_binding final_correction_value)
end S
namespace C
export OriginalWholeDebtRCorrectionActionSource
  (nativeAlpha nativeFirst nativeSecond nativeOutside actual_native_feet actual_correction_action)
end C
namespace Gamma
export OriginalWholeDebtRJointMobiusContactPsiPriceSource (nativeGamma actual_native_gamma)
export OriginalWholeDebtRJointMobiusContactClosureSource (actual_finite_price)
export OriginalWholeDebtRAdjointContactSource (sigma)
end Gamma
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualInput : BurnolL2 := (S.rInput observation nontrivial half depth ordinal).1
def actualResult : BurnolL2 := (S.rResult observation nontrivial half depth ordinal).2.2.1

theorem actual_input_source : actualInput observation nontrivial half depth ordinal =
    BandFullStockEuler.correctionRaw c :=
  (S.r_input_binding observation nontrivial half depth ordinal).trans
    (S.final_correction_value observation nontrivial half depth ordinal)

theorem actual_source_equation : actualResult observation nontrivial half depth ordinal =
    burnolDirectRightResolventCLM c (actualInput observation nontrivial half depth ordinal) :=
  (S.rInput observation nontrivial half depth ordinal).2.2.down.symm

private theorem actual_result_source : actualResult observation nontrivial half depth ordinal =
    burnolDirectRightResolventCLM c (BandFullStockEuler.correctionRaw c) :=
  (actual_source_equation observation nontrivial half depth ordinal).trans
    (congrArg (burnolDirectRightResolventCLM c) (actual_input_source observation nontrivial half depth ordinal))

theorem actual_input_feet :
    burnolAmbientMeanZeroFirstCorrection (actualInput observation nontrivial half depth ordinal) = sourceFirst c ∧
    burnolAmbientMeanZeroSecondCorrection (actualInput observation nontrivial half depth ordinal) = sourceSecond c := by
  rw [actual_input_source]
  exact correction_B c

theorem actual_output_feet :
    burnolAmbientMeanZeroFirstCorrection (actualResult observation nontrivial half depth ordinal) = C.nativeFirst c ∧
    burnolAmbientMeanZeroSecondCorrection (actualResult observation nontrivial half depth ordinal) = C.nativeSecond c := by
  rw [actual_result_source]
  exact C.actual_native_feet c

theorem actual_complete_update : actualResult observation nontrivial half depth ordinal =
    (-2*C.nativeAlpha c) •
      (burnolCompletedMellinRieszVector (OriginalPrimitiveRankBalance.conjugateCoordinate c) : BurnolL2) +
        C.nativeOutside c :=
  (actual_result_source observation nontrivial half depth ordinal).trans (C.actual_correction_action c)

/-- The original finite Gamma price reads the same complete correction supplied to this R. -/
theorem actual_input_Gamma : Gamma.nativeGamma c c =
    -2*Gamma.sigma c c * inner ℂ (physicalOutsideColumn c) (actualInput observation nontrivial half depth ordinal) := by
  rw [actual_input_source]
  exact (Gamma.actual_native_gamma c c).trans
    (congrArg (fun value : ℂ => -2*Gamma.sigma c c*value) (Gamma.actual_finite_price c c).symm)

end OriginalWholeDebtROutsideCorrectionRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtROutsideCorrectionRConsumer"
