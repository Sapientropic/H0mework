import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierSectorRGramSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance sectorPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

namespace Sector
export OriginalKFourierSectorRGramSource (actualPlusSource actualMinusSource actualPlusPrice actualMinusPrice actualMixedLeft actualMixedRight)
end Sector
namespace NativeK
export OriginalKConstantContactSourceAction.ConstantSource (value velocity strong_derivative seed)
end NativeK
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "s" => NativeK.seed

def actualPlusCorrected (c : BurnolCompletedMellinCoordinate) : BurnolL2:=NativeK.value c+fourierL2 (NativeK.value c)
def actualMinusCorrected (c : BurnolCompletedMellinCoordinate) : BurnolL2:=NativeK.value c-fourierL2 (NativeK.value c)
def actualPlusVelocity (c : BurnolCompletedMellinCoordinate) : BurnolL2:=NativeK.velocity c-fourierL2 (NativeK.velocity c)
def actualMinusVelocity (c : BurnolCompletedMellinCoordinate) : BurnolL2:=NativeK.velocity c+fourierL2 (NativeK.velocity c)
def actualPlusForcing (c : BurnolCompletedMellinCoordinate) : BurnolL2:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
 (fourierL2 (U+V)-(U+V)+(1/2:ℂ) • (s-fourierL2 s)-(c.value-1/2) • (s+fourierL2 s))
def actualMinusForcing (c : BurnolCompletedMellinCoordinate) : BurnolL2:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
 (fourierL2 (U-V)+(U-V)+(1/2:ℂ) • (s+fourierL2 s)-(c.value-1/2) • (s-fourierL2 s))

theorem actual_source_two_corrected_fields (c : BurnolCompletedMellinCoordinate) :
 actualPlusCorrected c=(Sector.actualPlusSource c:BurnolL2)-
  (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) • (s+fourierL2 s) ∧
 actualMinusCorrected c=(Sector.actualMinusSource c:BurnolL2)-
  (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) • (s-fourierL2 s) :=by
 unfold actualPlusCorrected actualMinusCorrected NativeK.value
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,OriginalKGapProjectionEulerSource.actual_seed_even]
 change _=((K c:BurnolL2)+fourierL2 (K c:BurnolL2))-_ ∧
  _=((K c:BurnolL2)-fourierL2 (K c:BurnolL2))-_ 
 constructor <;> module

/-- Same two whole source actions generate the coupled sector strong fields. -/
theorem actual_source_two_strong_fields (c : BurnolCompletedMellinCoordinate) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualPlusCorrected c)) (actualPlusVelocity c) 0 ∧
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualMinusCorrected c)) (actualMinusVelocity c) 0 :=by
 have actual:=NativeK.strong_derivative c
 have Fourier:=OriginalKCommonGapKernelSource.actual_Fourier_K_corrected_strong c
 constructor
 · have generated:=actual.add Fourier
   change HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (NativeK.value c)+
    burnolMultiplicativeDilation shift (fourierL2 (NativeK.value c))) _ 0 at generated
   simpa only [actualPlusCorrected,actualPlusVelocity,map_add,sub_eq_add_neg] using generated
 · have generated:=actual.sub Fourier
   change HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (NativeK.value c)-
    burnolMultiplicativeDilation shift (fourierL2 (NativeK.value c))) _ 0 at generated
   simpa only [actualMinusCorrected,actualMinusVelocity,map_sub,sub_neg_eq_add] using generated

/-- The source velocity is expanded before the resolvent inverse is consumed. -/
theorem actual_source_coupled_forcing (c : BurnolCompletedMellinCoordinate) :
 actualPlusVelocity c+(c.value-1/2) • actualPlusCorrected c=
 -(star c.value-1/2) • (Sector.actualMinusSource c:BurnolL2)+
 (c.value-1/2) • (Sector.actualPlusSource c:BurnolL2)+actualPlusForcing c ∧
 actualMinusVelocity c+(c.value-1/2) • actualMinusCorrected c=
 -(star c.value-1/2) • (Sector.actualPlusSource c:BurnolL2)+
 (c.value-1/2) • (Sector.actualMinusSource c:BurnolL2)+actualMinusForcing c :=by
 have fields:=actual_source_two_corrected_fields c
 rw [fields.1,fields.2]
 unfold actualPlusVelocity actualMinusVelocity NativeK.velocity actualPlusForcing actualMinusForcing
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,fourierL2_fourierL2,fourierL2_fourierL2,
  OriginalRieszSource.Response.wholeU_reflection,OriginalRieszSource.Response.wholeV_reflection,
  OriginalKGapProjectionEulerSource.actual_seed_even]
 have plusCast:(Sector.actualPlusSource c:BurnolL2)=(K c:BurnolL2)+fourierL2 (K c:BurnolL2):=rfl
 have minusCast:(Sector.actualMinusSource c:BurnolL2)=(K c:BurnolL2)-fourierL2 (K c:BurnolL2):=rfl
 rw [plusCast,minusCast]
 constructor <;> module

elab "paid189ActualRInverse" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCommonGapKernelSource.Inverse".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource.actual_source_R_inverse".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

/-- Actual source strong action generates the two complete coupled R fields, before any physical price. -/
theorem actual_source_coupled_R_fields (c : BurnolCompletedMellinCoordinate) :
 (star c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2)=
 (c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2)+
 burnolDirectRightResolvent (c.value/2) (actualPlusForcing c)+(2:ℂ) • actualPlusCorrected c ∧
 (star c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2)=
 (c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2)+
 burnolDirectRightResolvent (c.value/2) (actualMinusForcing c)+(2:ℂ) • actualMinusCorrected c :=by
 have strong:=actual_source_two_strong_fields c
 have forcing:=actual_source_coupled_forcing c
 have plus:=paid189ActualRInverse c _ _ strong.1
 have minus:=paid189ActualRInverse c _ _ strong.2
 rw [forcing.1,burnolDirectRightResolvent_smul] at plus
 rw [forcing.2,burnolDirectRightResolvent_smul] at minus
 change actualPlusCorrected c=(-1/2:ℂ) • burnolDirectRightResolventCLM c _ at plus
 change actualMinusCorrected c=(-1/2:ℂ) • burnolDirectRightResolventCLM c _ at minus
 rw [map_add,map_add,map_smul,map_smul] at plus minus
 change actualPlusCorrected c=(-1/2:ℂ) •
  (-(star c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2)+
  (c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2)+
  burnolDirectRightResolvent (c.value/2) (actualPlusForcing c)) at plus
 change actualMinusCorrected c=(-1/2:ℂ) •
  (-(star c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2)+
  (c.value-1/2) • burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2)+
  burnolDirectRightResolvent (c.value/2) (actualMinusForcing c)) at minus
 constructor
 · linear_combination (norm:=module) (-2:ℂ) • plus
 · linear_combination (norm:=module) (-2:ℂ) • minus

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
