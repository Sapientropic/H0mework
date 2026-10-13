import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteResponseEulerSource.Jordan
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

/-- Source qualification is paid by the original right-half coordinate, not a target price. -/
theorem actual_source_rate_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
 coordinate.value-1/2≠0 :=by
 intro zero
 have real:=congrArg Complex.re zero
 norm_num at real
 linarith [coordinate.rightHalf]

def actualFiniteEulerJordanPrice (coordinate : BurnolCompletedMellinCoordinate)
 (material : BurnolL2) (physical : BurnolPaAmbientCarrier) : ℂ:=
 inner ℂ (actualJordanAction coordinate material)
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)

def actualFiniteEulerUPrice (coordinate : BurnolCompletedMellinCoordinate)
 (n : Nat) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (-2:ℂ)*inner ℂ (burnolDirectRightResolvent (coordinate.value/2) (actualUCorrected n))
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)-
 actualFiniteEulerJordanPrice coordinate (actualWholeUEuler n) physical+
 star ((coordinate.value-1)*actualURaw n q)*
 actualFiniteEulerJordanPrice coordinate OriginalKConstantSeedWholeRAction.ConstantSource.seed physical

def actualFiniteEulerVPrice (coordinate : BurnolCompletedMellinCoordinate)
 (n : Nat) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (-2:ℂ)*inner ℂ (burnolDirectRightResolvent (coordinate.value/2) (actualVCorrected n))
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2)-
 actualFiniteEulerJordanPrice coordinate (actualWholeVEuler n) physical+
 star ((coordinate.value-1)*actualVRaw n q)*
 actualFiniteEulerJordanPrice coordinate OriginalKConstantSeedWholeRAction.ConstantSource.seed physical

/-- Actual finite Euler source action generates the Jordan price from true derivative, R field and endpoint/seed stocks. -/
theorem actual_U_Jordan_Euler_price (coordinate : BurnolCompletedMellinCoordinate)
 (n : Nat) (physical : BurnolPaAmbientCarrier) :
 star (coordinate.value-1/2)*actualFiniteEulerJordanPrice coordinate (actualWholeU n) physical=
 actualFiniteEulerUPrice coordinate n physical :=by
 have source:=congrArg (fun field:BurnolL2=>inner ℂ field
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2))
  (actual_U_Jordan_Euler_inventory coordinate n)
 simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_neg,star_ofNat] at source
 unfold actualFiniteEulerUPrice actualFiniteEulerJordanPrice
 linear_combination source

theorem actual_V_Jordan_Euler_price (coordinate : BurnolCompletedMellinCoordinate)
 (n : Nat) (physical : BurnolPaAmbientCarrier) :
 star (coordinate.value-1/2)*actualFiniteEulerJordanPrice coordinate (actualWholeV n) physical=
 actualFiniteEulerVPrice coordinate n physical :=by
 have source:=congrArg (fun field:BurnolL2=>inner ℂ field
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical : BurnolL2))
  (actual_V_Jordan_Euler_inventory coordinate n)
 simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_neg,star_ofNat] at source
 unfold actualFiniteEulerVPrice actualFiniteEulerJordanPrice
 linear_combination source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteResponseEulerSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
