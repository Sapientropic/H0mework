import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantSeedWholeRAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)




def actualSingleSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
 burnolRieszSingleFourierSource coordinate

def actualSingleReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
 burnolMeanZeroTruncatedFourier (actualSingleSource coordinate)

def actualWholeSingleSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 burnolQuarterZeroExtension (actualSingleSource coordinate : BurnolQuarterIntervalL2)

def actualWholeSingleReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 burnolQuarterZeroExtension (actualSingleReturn coordinate : BurnolQuarterIntervalL2)

theorem actual_single_source_equation (coordinate : BurnolCompletedMellinCoordinate) :
 burnolMeanZeroOneMinusSquare (actualSingleSource coordinate)=
 burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) :=
 burnolRieszSingleFourierSource_equation coordinate

theorem actual_single_source_even (coordinate : BurnolCompletedMellinCoordinate) :
 reflectL2 (actualWholeSingleSource coordinate)=actualWholeSingleSource coordinate ∧
 reflectL2 (actualWholeSingleReturn coordinate)=actualWholeSingleReturn coordinate := by
 constructor
 · change reflectL2 (burnolRadiusZeroExtension q (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))=_
   rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
   rfl
 · change reflectL2 (burnolRadiusZeroExtension q (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2))=_
   rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierReturn_reflection_fixed]
   rfl

theorem actual_original_K_single_source (coordinate : BurnolCompletedMellinCoordinate) :
 (burnolCompletedMellinRieszVector coordinate : BurnolL2)=
 burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)+
 (actualWholeSingleReturn coordinate-fourierL2 (actualWholeSingleSource coordinate)) := by
 have source:=burnolCompletedMellinRieszVector_eq_singleFourierSource coordinate
 change (burnolCompletedMellinRieszVector coordinate : BurnolL2)=
 burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)+
 burnolAmbientEvenPart (actualWholeSingleReturn coordinate-fourierL2 (actualWholeSingleSource coordinate)) at source
 unfold burnolAmbientEvenPart at source
 rw [map_sub,←fourierL2_reflectL2_commute,(actual_single_source_even coordinate).1,
   (actual_single_source_even coordinate).2] at source
 unfold burnolAmbientEvenPart
 linear_combination (norm:=module) source

theorem actual_original_FK_single_source (coordinate : BurnolCompletedMellinCoordinate) :
 fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)=
 fourierL2 (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))+
 (fourierL2 (actualWholeSingleReturn coordinate)-actualWholeSingleSource coordinate) := by
 rw [actual_original_K_single_source,map_add,map_sub,fourierL2_fourierL2,(actual_single_source_even coordinate).1]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
