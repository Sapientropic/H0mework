import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSectorEulerMixedSource.Foot
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierSectorRGramSource.Consumer
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
local instance sectorMixedPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed
local notation "μ" => FiniteMobiusResolventFlux.actualMean

def actualPlusRightForcingPrice (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
 (-(actualCompactRightPrice c U physical+actualCompactRightPrice c V physical)+
 (1-c.value)*actualSeedRightPrice c physical-c.value*actualFourierSeedRightPrice c physical)
def actualMinusRightForcingPrice (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) : ℂ:=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)*
 (actualCompactRightPrice c U physical-actualCompactRightPrice c V physical+
 (1-c.value)*actualSeedRightPrice c physical+c.value*actualFourierSeedRightPrice c physical)

/-- Actual mean-zero projection, source compact prices and both seed actions read the full sector forcing. -/
theorem actual_two_forcing_R_right_prices (c : BurnolCompletedMellinCoordinate) (physical : BurnolPaAmbientCarrier) :
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2) (actualPlusForcing c))=actualPlusRightForcingPrice c physical ∧
 inner ℂ (physical:BurnolL2) (burnolDirectRightResolvent (c.value/2) (actualMinusForcing c))=actualMinusRightForcingPrice c physical :=by
 have qualified:=OriginalKCompactAdjointRSource.actual_original_UV_compact_even
 have up:=actual_compact_R_right_price c U qualified.1 qualified.2.1 physical
 have vp:=actual_compact_R_right_price c V qualified.2.2.1 qualified.2.2.2 physical
 have fu:=actual_compact_F_R_right_price c U qualified.1 qualified.2.1 physical
 have fv:=actual_compact_F_R_right_price c V qualified.2.2.1 qualified.2.2.2 physical
 have meanU:μ U=0:=actual_quarter_mean_zero_source OriginalRieszSource.Response.u
 have meanV:μ V=0:=actual_quarter_mean_zero_source OriginalRieszSource.Response.v
 rw [meanU,mul_zero,zero_div] at fu
 rw [meanV,mul_zero,zero_div] at fv
 have seeds:=actual_original_seed_R_right_prices c physical
 have forcingPlus:actualPlusForcing c=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
 (fourierL2 U+fourierL2 V-U-V+(1-c.value) • s-c.value • fourierL2 s) :=by
  unfold actualPlusForcing
  rw [map_add]
  module
 have forcingMinus:actualMinusForcing c=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
 (fourierL2 U-fourierL2 V+U-V+(1-c.value) • s+c.value • fourierL2 s) :=by
  unfold actualMinusForcing
  rw [map_sub]
  module
 rw [forcingPlus,forcingMinus]
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c _)=_ ∧
  inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c _)=_
 simp only [map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c U)=_ at up
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c V)=_ at vp
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c (fourierL2 U))=0 at fu
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c (fourierL2 V))=0 at fv
 change inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c s)=_ ∧
  inner ℂ (physical:BurnolL2) (burnolDirectRightResolventCLM c (fourierL2 s))=_ at seeds
 rw [up,vp,fu,fv,seeds.1,seeds.2]
 unfold actualPlusRightForcingPrice actualMinusRightForcingPrice
 constructor <;> ring

def actualPlusCorrectedInputPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (Sector.actualPlusSource c:BurnolL2) (Sector.actualPlusSource c:BurnolL2)-
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)/2*
 (star (μ (Sector.actualPlusSource c:BurnolL2))+star (μ (fourierL2 (Sector.actualPlusSource c:BurnolL2))))
def actualMinusCorrectedInputPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 inner ℂ (Sector.actualMinusSource c:BurnolL2) (Sector.actualMinusSource c:BurnolL2)-
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c)/2*
 (star (μ (Sector.actualMinusSource c:BurnolL2))-star (μ (fourierL2 (Sector.actualMinusSource c:BurnolL2))))

private theorem actual_seed_right_input (physical : BurnolPaAmbientCarrier) :
 inner ℂ (physical:BurnolL2) s=(1/2:ℂ)*star (μ (physical:BurnolL2)) ∧
 inner ℂ (physical:BurnolL2) (fourierL2 s)=(1/2:ℂ)*star (μ (fourierL2 (physical:BurnolL2))) :=by
 have first:=congrArg star (OriginalKConstantContactSourceAction.actual_constant_seed_input_price physical)
 have second:=congrArg star (OriginalKConstantContactSourceAction.actual_constant_seed_input_price
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical))
 rw [←OriginalKGapProjectionEulerSource.actual_source_fourier_input s physical] at second
 simp only [star_mul,star_div₀,star_ofNat,star_one] at first second
 have firstRead:inner ℂ (physical:BurnolL2) s=star (μ (physical:BurnolL2))*(1/2:ℂ):=by
  exact ((inner_conj_symm (physical:BurnolL2) s).symm).trans first
 have secondRead:inner ℂ (physical:BurnolL2) (fourierL2 s)=
  star (μ (fourierL2 (physical:BurnolL2)))*(1/2:ℂ):=by
  exact ((inner_conj_symm (physical:BurnolL2) (fourierL2 s)).symm).trans second
 constructor
 · rw [firstRead];ring
 · rw [secondRead];ring

/-- Actual contact-corrected sector input retains both original mean faces and its same source self Gram. -/
theorem actual_two_corrected_input_prices (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (Sector.actualPlusSource c:BurnolL2) (actualPlusCorrected c)=actualPlusCorrectedInputPrice c ∧
 inner ℂ (Sector.actualMinusSource c:BurnolL2) (actualMinusCorrected c)=actualMinusCorrectedInputPrice c :=by
 have fields:=actual_source_two_corrected_fields c
 have plus:=actual_seed_right_input (Sector.actualPlusSource c)
 have minus:=actual_seed_right_input (Sector.actualMinusSource c)
 rw [fields.1,fields.2,inner_sub_right,inner_smul_right,inner_add_right,
  inner_sub_right,inner_smul_right,inner_sub_right,plus.1,plus.2,minus.1,minus.2]
 unfold actualPlusCorrectedInputPrice actualMinusCorrectedInputPrice
 constructor <;> ring

def actualMixedLeftPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 ((c.value-1/2)*Sector.actualPlusPrice c+
 actualPlusRightForcingPrice c (Sector.actualPlusSource c)+2*actualPlusCorrectedInputPrice c)/(star c.value-1/2)
def actualMixedRightPrice (c : BurnolCompletedMellinCoordinate) : ℂ:=
 ((c.value-1/2)*Sector.actualMinusPrice c+
 actualMinusRightForcingPrice c (Sector.actualMinusSource c)+2*actualMinusCorrectedInputPrice c)/(star c.value-1/2)

/-- The original actual mixed responses consume the generated coupled source equations, complete source forcing and contact input. -/
theorem actual_two_mixed_R_source_prices (c : BurnolCompletedMellinCoordinate) :
 Sector.actualMixedLeft c=actualMixedLeftPrice c ∧ Sector.actualMixedRight c=actualMixedRightPrice c :=by
 have fields:=actual_source_coupled_R_fields c
 have plus:=congrArg (inner ℂ (Sector.actualPlusSource c:BurnolL2)) fields.1
 have minus:=congrArg (inner ℂ (Sector.actualMinusSource c:BurnolL2)) fields.2
 simp only [inner_smul_right,inner_add_right] at plus minus
 have actualPlus:=(OriginalKFourierSectorRGramSource.actual_two_sector_R_prices c).1
 have actualMinus:=(OriginalKFourierSectorRGramSource.actual_two_sector_R_prices c).2
 rw [actualPlus,(actual_two_forcing_R_right_prices c (Sector.actualPlusSource c)).1,
  (actual_two_corrected_input_prices c).1] at plus
 rw [actualMinus,(actual_two_forcing_R_right_prices c (Sector.actualMinusSource c)).2,
  (actual_two_corrected_input_prices c).2] at minus
 have unit:star c.value-1/2≠0 :=by
  intro zero
  have real:=congrArg Complex.re zero
  simp only [Complex.sub_re,Complex.star_def,Complex.conj_re,Complex.div_re] at real
  norm_num at real
  linarith [c.rightHalf]
 unfold actualMixedLeftPrice actualMixedRightPrice
 constructor
 · apply (eq_div_iff unit).mpr
   change Sector.actualMixedLeft c*(star c.value-1/2)=_
   change (star c.value-1/2)*Sector.actualMixedLeft c=_ at plus
   linear_combination plus
 · apply (eq_div_iff unit).mpr
   change Sector.actualMixedRight c*(star c.value-1/2)=_
   change (star c.value-1/2)*Sector.actualMixedRight c=_ at minus
   linear_combination minus

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSectorEulerMixedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
