import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoupledPhysicalRFieldSource.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance coupledPhysicalEffectComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

namespace Sector
export OriginalKFourierSectorRGramSource (actualPlusSource actualMinusSource)
end Sector
local notation "P" => burnolEvenAmbientProjection
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

def actualPlusProjectedForcing (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
 (-(actualCompactProjectedRField c U+actualCompactProjectedRField c V)+
 (1-c.value) • actualCompactProjectedRField c s+Fphysical G)
def actualMinusProjectedForcing (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
 (actualCompactProjectedRField c U-actualCompactProjectedRField c V+
 (1-c.value) • actualCompactProjectedRField c s-Fphysical G)

/-- Complete source-projected forcing retains its actual Tate/dualK/G fields and the original Fourier seed unit. -/
theorem actual_two_projected_forcing_fields (c : BurnolCompletedMellinCoordinate) :
 P (burnolDirectRightResolvent (c.value/2) (OriginalKSectorEulerMixedSource.actualPlusForcing c))=actualPlusProjectedForcing c ∧
 P (burnolDirectRightResolvent (c.value/2) (OriginalKSectorEulerMixedSource.actualMinusForcing c))=actualMinusProjectedForcing c :=by
 have qualified:=actual_original_UV_projected_R_fields c
 have seeds:=actual_original_seed_projected_R_fields c
 have up:P (burnolDirectRightResolventCLM c U)=actualCompactProjectedRField c U:=qualified.1
 have vp:P (burnolDirectRightResolventCLM c V)=actualCompactProjectedRField c V:=qualified.2.1
 have fu:P (burnolDirectRightResolventCLM c (fourierL2 U))=0:=qualified.2.2.1
 have fv:P (burnolDirectRightResolventCLM c (fourierL2 V))=0:=qualified.2.2.2
 have seed:P (burnolDirectRightResolventCLM c s)=actualCompactProjectedRField c s:=seeds.1
 have Fseed:P (burnolDirectRightResolventCLM c (fourierL2 s))=-c.value⁻¹ • Fphysical G:=seeds.2
 have unit:=(OriginalKCommonGapKernelSource.actual_common_source_units c).1
 have plusForcing:OriginalKSectorEulerMixedSource.actualPlusForcing c=
  (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
  (fourierL2 U+fourierL2 V-U-V+(1-c.value) • s-c.value • fourierL2 s) :=by
  unfold OriginalKSectorEulerMixedSource.actualPlusForcing
  rw [map_add]
  module
 have minusForcing:OriginalKSectorEulerMixedSource.actualMinusForcing c=
  (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
  (fourierL2 U-fourierL2 V+U-V+(1-c.value) • s+c.value • fourierL2 s) :=by
  unfold OriginalKSectorEulerMixedSource.actualMinusForcing
  rw [map_sub]
  module
 rw [plusForcing,minusForcing]
 change P (burnolDirectRightResolventCLM c _)=_ ∧ P (burnolDirectRightResolventCLM c _)=_
 simp only [map_smul,map_add,map_sub]
 rw [up,vp,fu,fv,seed,Fseed]
 simp only [smul_neg,neg_smul,smul_smul,mul_inv_cancel₀ unit,one_smul]
 unfold actualPlusProjectedForcing actualMinusProjectedForcing
 constructor <;> module

def actualPlusProjectedUpdate (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 actualPlusProjectedForcing c+(2:ℂ) • Sector.actualPlusSource c-
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) • (G+Fphysical G)
def actualMinusProjectedUpdate (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 actualMinusProjectedForcing c+(2:ℂ) • Sector.actualMinusSource c-
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) • (G-Fphysical G)

/-- Existing raw coupled source equations are projected after the original R action; all contact projections are generated by the same source. -/
theorem actual_coupled_physical_R_updates (c : BurnolCompletedMellinCoordinate) :
 (star c.value-1/2) • P (burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2))=
 (c.value-1/2) • P (burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2))+actualPlusProjectedUpdate c ∧
 (star c.value-1/2) • P (burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2))=
 (c.value-1/2) • P (burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2))+actualMinusProjectedUpdate c :=by
 have source:=OriginalKSectorEulerMixedSource.actual_source_coupled_R_fields c
 have plus:=congrArg P source.1
 have minus:=congrArg P source.2
 simp only [map_smul,map_add] at plus minus
 rw [(actual_two_projected_forcing_fields c).1] at plus
 rw [(actual_two_projected_forcing_fields c).2] at minus
 have corrected:=OriginalKSectorEulerMixedSource.actual_source_two_corrected_fields c
 rw [corrected.1,map_sub,map_smul,map_add,actual_seed_projected_field,actual_Fourier_seed_projected_field] at plus
 rw [corrected.2,map_sub,map_smul,map_sub,actual_seed_projected_field,actual_Fourier_seed_projected_field] at minus
 have plusMem:P (Sector.actualPlusSource c:BurnolL2)=Sector.actualPlusSource c:=by
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 have minusMem:P (Sector.actualMinusSource c:BurnolL2)=Sector.actualMinusSource c:=by
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [plusMem] at plus
 rw [minusMem] at minus
 unfold actualPlusProjectedUpdate actualMinusProjectedUpdate
 constructor
 · linear_combination (norm:=module) plus
 · linear_combination (norm:=module) minus

def actualResponseKappa (c : BurnolCompletedMellinCoordinate) : ℂ:=
 (star c.value-1/2)^2-(c.value-1/2)^2

theorem actual_response_kappa_source (c : BurnolCompletedMellinCoordinate) :
 actualResponseKappa c=(star c.value-c.value)*(star c.value+c.value-1) :=by
 unfold actualResponseKappa
 ring

def actualWeightedPlusRField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (star c.value-1/2) • actualMinusProjectedUpdate c+(c.value-1/2) • actualPlusProjectedUpdate c
def actualWeightedMinusRField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (star c.value-1/2) • actualPlusProjectedUpdate c+(c.value-1/2) • actualMinusProjectedUpdate c

/-- The two same-source projected equations generate both weighted whole R fields without dividing kappa or presupposing cancellation. -/
theorem actual_joint_weighted_R_source_fields (c : BurnolCompletedMellinCoordinate) :
 actualResponseKappa c • P (burnolDirectRightResolvent (c.value/2) (Sector.actualPlusSource c:BurnolL2))=actualWeightedPlusRField c ∧
 actualResponseKappa c • P (burnolDirectRightResolvent (c.value/2) (Sector.actualMinusSource c:BurnolL2))=actualWeightedMinusRField c :=by
 have actual:=actual_coupled_physical_R_updates c
 unfold actualResponseKappa actualWeightedPlusRField actualWeightedMinusRField
 constructor
 · linear_combination (norm:=module) (star c.value-1/2) • actual.2+(c.value-1/2) • actual.1
 · linear_combination (norm:=module) (star c.value-1/2) • actual.1+(c.value-1/2) • actual.2

def actualWeightedKResponseField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (1/2:ℂ) • (actualWeightedPlusRField c+actualWeightedMinusRField c)
def actualWeightedFKResponseField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (1/2:ℂ) • (actualWeightedPlusRField c-actualWeightedMinusRField c)

/-- The complete original K and actual Fourier K responses consume the joint source fields before any scalar price. -/
theorem actual_original_weighted_R_fields (c : BurnolCompletedMellinCoordinate) :
 actualResponseKappa c • P (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2))=actualWeightedKResponseField c ∧
 actualResponseKappa c • P (burnolDirectRightResolvent (c.value/2) (fourierL2 (K c:BurnolL2)))=actualWeightedFKResponseField c :=by
 have source:=actual_joint_weighted_R_source_fields c
 have Rfields:=OriginalKFourierSectorRGramSource.actual_two_source_R_fields c
 rw [Rfields.1,map_add] at source
 rw [Rfields.2,map_sub] at source
 unfold actualWeightedKResponseField actualWeightedFKResponseField
 constructor
 · linear_combination (norm:=module) (1/2:ℂ) • source.1+(1/2:ℂ) • source.2
 · linear_combination (norm:=module) (1/2:ℂ) • source.1-(1/2:ℂ) • source.2

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCoupledPhysicalRFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
