import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
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

namespace RPaid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction (actual_resonant_repeated_R)
end RPaid

/-- The actual finite whole source inverse is consumed a second time before any physical projection. -/
theorem actual_U_Jordan_source_action (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 OriginalKFourierKernelDependentRAction.actualResonantField (coordinate.value/2)
  (actualUVelocity n+(coordinate.value-1/2) • actualUCorrected n)=
 (-2:ℂ) • burnolDirectRightResolvent (coordinate.value/2) (actualUCorrected n) :=by
 have second:=congrArg (burnolDirectRightResolvent (coordinate.value/2)) (actual_U_R_source_inverse coordinate n)
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 rw [RPaid.actual_resonant_repeated_R (coordinate.value/2) right] at second
 have smul:burnolDirectRightResolvent (coordinate.value/2) ((-2:ℂ) • actualUCorrected n)=
  (-2:ℂ) • burnolDirectRightResolvent (coordinate.value/2) (actualUCorrected n) :=
  (burnolDirectRightResolventCLM coordinate).map_smul _ _
 exact second.trans smul

theorem actual_V_Jordan_source_action (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 OriginalKFourierKernelDependentRAction.actualResonantField (coordinate.value/2)
  (actualVVelocity n+(coordinate.value-1/2) • actualVCorrected n)=
 (-2:ℂ) • burnolDirectRightResolvent (coordinate.value/2) (actualVCorrected n) :=by
 have second:=congrArg (burnolDirectRightResolvent (coordinate.value/2)) (actual_V_R_source_inverse coordinate n)
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 rw [RPaid.actual_resonant_repeated_R (coordinate.value/2) right] at second
 exact second.trans ((burnolDirectRightResolventCLM coordinate).map_smul _ _)

def actualJordanAction (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2→L[ℂ]BurnolL2:=
 (burnolDirectRightResolventCLM coordinate).comp (burnolDirectRightResolventCLM coordinate)

theorem actual_Jordan_action_source (coordinate : BurnolCompletedMellinCoordinate) (material : BurnolL2) :
 actualJordanAction coordinate material=
 OriginalKFourierKernelDependentRAction.actualResonantField (coordinate.value/2) material :=by
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 exact RPaid.actual_resonant_repeated_R _ right _

/-- The source-generated finite derivative eliminates an independent Jordan input while retaining the endpoint/seed response. -/
theorem actual_U_Jordan_Euler_inventory (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 actualJordanAction coordinate (actualWholeUEuler n)+
 (coordinate.value-1/2) • actualJordanAction coordinate (actualWholeU n)=
 (-2:ℂ) • burnolDirectRightResolvent (coordinate.value/2) (actualUCorrected n)+
 ((coordinate.value-1)*actualURaw n q) • actualJordanAction coordinate OriginalKConstantSeedWholeRAction.ConstantSource.seed :=by
 have source:=actual_U_Jordan_source_action coordinate n
 rw [←actual_Jordan_action_source] at source
 unfold actualUVelocity actualUCorrected at source
 rw [map_add,map_add,map_smul,map_smul,map_sub,map_smul] at source
 unfold actualUCorrected
 linear_combination (norm:=module) source

theorem actual_V_Jordan_Euler_inventory (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
 actualJordanAction coordinate (actualWholeVEuler n)+
 (coordinate.value-1/2) • actualJordanAction coordinate (actualWholeV n)=
 (-2:ℂ) • burnolDirectRightResolvent (coordinate.value/2) (actualVCorrected n)+
 ((coordinate.value-1)*actualVRaw n q) • actualJordanAction coordinate OriginalKConstantSeedWholeRAction.ConstantSource.seed :=by
 have source:=actual_V_Jordan_source_action coordinate n
 rw [←actual_Jordan_action_source] at source
 unfold actualVVelocity actualVCorrected at source
 rw [map_add,map_add,map_smul,map_smul,map_sub,map_smul] at source
 unfold actualVCorrected
 linear_combination (norm:=module) source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
