import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.KernelGram

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.AmbientBPriceSource
open Complex BurnolPhysicalState OriginalRieszSourceGreen OriginalRieszSource
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKCrossParameterRAdjointSource
open OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local notation "q"=>(1/4:ℝ)
local notation "Hq"=>BurnolQuarterIntervalL2
local notation "M"=>BurnolQuarterMeanZeroCarrier
local notation "E"=>burnolQuarterZeroExtension
local notation "S"=>burnolMeanZeroTruncatedFourier
local notation "K"=>burnolCompletedMellinRieszVector
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem evenPart_right (left right:BurnolL2) (even:reflectL2 left=left):
    inner ℂ left (burnolAmbientEvenPart right)=inner ℂ left right:=by
  have reflected:=reflectL2.inner_map_map left right
  rw [even] at reflected
  unfold burnolAmbientEvenPart
  rw [inner_smul_right,inner_add_right,reflected]
  norm_num
  ring

private theorem evenPart_left (left right:BurnolL2) (even:reflectL2 right=right):
    inner ℂ (burnolAmbientEvenPart left) right=inner ℂ left right:=by
  have reflected:=reflectL2.inner_map_map left right
  rw [even] at reflected
  unfold burnolAmbientEvenPart
  rw [inner_smul_left,inner_add_left,reflected]
  simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
  norm_num
  ring

private theorem source_even (c:BurnolCompletedMellinCoordinate):
    reflectL2 (sourceCorrection c)=sourceCorrection c:=by
  have source:sourceCorrection c=gapState c-(K c:BurnolL2):=by
    rw [gapState_eq_kernel_add_correction]
    module
  have gapEven:reflectL2 (gapState c)=gapState c:=burnolAmbientEvenPart_even _
  rw [source,map_sub,gapEven,
    mem_evenL2ClosedFace_iff.mp (K c).property.2]

private theorem ambient_outside (c:BurnolCompletedMellinCoordinate) (v:BurnolL2)
    (even:reflectL2 v=v) (outside:v∈(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ):
    burnolAmbientCompletedMellinEvaluator c v=inner ℂ (sourceCorrection c) v:=by
  have read:burnolAmbientCompletedMellinEvaluator c v=inner ℂ (gapState c) v:=by
    rw [←burnolAmbientCompletedMellinRieszVector_readback,
      burnolAmbientCompletedMellinRieszVector_eq_kernelFormula]
    exact (evenPart_left _ _ even).symm
  rw [read,gapState_eq_kernel_add_correction,inner_add_left,outside (K c) (K c).property,zero_add]

private theorem S_left (c:BurnolCompletedMellinCoordinate) (v:M):
    inner ℂ (S (burnolRieszSingleFourierSource c)) v=
      inner ℂ (burnolRieszSingleFourierSource c) (S v):=by
  have paid:=meanZero_fourier_pairing_of_reflection v (burnolRieszSingleFourierSource c)
    (burnolRieszSingleFourierSource_reflection_fixed c)
  calc
    _=star (inner ℂ v (S (burnolRieszSingleFourierSource c))):=(inner_conj_symm _ _).symm
    _=star (inner ℂ (S v) (burnolRieszSingleFourierSource c)):=congrArg star paid.symm
    _=_:=inner_conj_symm _ _

private theorem crossed (left right:M)
    (even:reflectRestricted q (left:Hq)=left):
    inner ℂ (fourierL2 (E (left:Hq))) (E (right:Hq))=inner ℂ left (S right):=by
  have extEven:reflectL2 (E (left:Hq))=E (left:Hq):=by
    change reflectL2 (burnolRadiusZeroExtension q (left:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,even]
    rfl
  have moved:=fourierL2.inner_map_map (fourierL2 (E (left:Hq))) (E (right:Hq))
  rw [fourierL2_fourierL2,extEven] at moved
  exact moved.symm.trans (extension_fourier_pairing left right)

theorem actual_ambient_first_B_price (c:BurnolCompletedMellinCoordinate):
    burnolAmbientCompletedMellinEvaluator c (physicalOutsideColumn c)=
      inner ℂ (burnolRieszSingleFourierSource c) (SingularCounting.centeredPower (barC c)):=by
  let b:=burnolRieszSingleFourierSource c
  let first:=hPowerBColumn (barC c)
  let second:=hPowerBSecond (barC c)
  have corrEven:=source_even c
  have fcorrEven:reflectL2 (fourierL2 (sourceCorrection c))=fourierL2 (sourceCorrection c):=by
    rw [←fourierL2_reflectL2_commute,corrEven]
  have powerEven:reflectL2 (hPowerPhysicalCorrection (barC c))=hPowerPhysicalCorrection (barC c):=
    burnolAmbientEvenPart_even _
  have vEven:reflectL2 (physicalOutsideColumn c)=physicalOutsideColumn c:=by
    apply fourierL2.injective
    rw [fourierL2_reflectL2_commute,physicalOutsideColumn,fourierL2.apply_symm_apply,powerEven]
  rw [ambient_outside c _ vEven (outsideColumn_orthogonal c)]
  have moved:=fourierL2.inner_map_map (sourceCorrection c) (physicalOutsideColumn c)
  have fullFourier:fourierL2 (physicalOutsideColumn c)=hPowerPhysicalCorrection (barC c):=
    fourierL2.apply_symm_apply _
  rw [fullFourier] at moved
  rw [←moved]
  change inner ℂ (fourierL2 (sourceCorrection c)) (burnolAmbientEvenPart
    (E (first:Hq)+fourierL2 (E (second:Hq))))=_
  rw [evenPart_right _ _ fcorrEven]
  have eb:reflectL2 (E (b:Hq))=E (b:Hq):=by
    change reflectL2 (burnolRadiusZeroExtension q (b:Hq))=_
    rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  unfold sourceCorrection
  rw [map_sub,fourierL2_fourierL2,eb,inner_sub_left,inner_add_right,inner_add_right,
    quarter_extension_inner,extension_fourier_pairing,
    crossed (S b) first (burnolRieszSingleFourierReturn_reflection_fixed c),
    fourierL2.inner_map_map,quarter_extension_inner,←S_left c second,S_left c (S first)]
  have equation: first-S (S first)=SingularCounting.centeredPower (barC c):=by
    have paid:=(h_power_B_source (barC c)).1
    change first+S second=_ at paid
    change first+S (-S first)=_ at paid
    simpa only [map_neg,sub_eq_add_neg] using paid
  rw [←equation,inner_sub_right]
  change (inner ℂ b first+inner ℂ (S b) second)-
    (inner ℂ b (S (S first))+inner ℂ (S b) second)=
      inner ℂ b first-inner ℂ b (S (S first))
  ring

theorem actual_ambient_second_B_price (c:BurnolCompletedMellinCoordinate):
    burnolAmbientCompletedMellinEvaluator c (hPowerPhysicalCorrection (barC c))=
      -inner ℂ (S (burnolRieszSingleFourierSource c)) (SingularCounting.centeredPower (barC c)):=by
  let b:=burnolRieszSingleFourierSource c
  let first:=hPowerBColumn (barC c)
  let second:=hPowerBSecond (barC c)
  have powerEven:reflectL2 (hPowerPhysicalCorrection (barC c))=hPowerPhysicalCorrection (barC c):=
    burnolAmbientEvenPart_even _
  rw [ambient_outside c _ powerEven (powerCorrection_orthogonal (barC c))]
  change inner ℂ (sourceCorrection c) (burnolAmbientEvenPart
    (E (first:Hq)+fourierL2 (E (second:Hq))))=_
  rw [evenPart_right _ _ (source_even c)]
  unfold sourceCorrection
  rw [inner_sub_left,inner_add_right,inner_add_right,
    crossed b first (burnolRieszSingleFourierSource_reflection_fixed c),
    fourierL2.inner_map_map,quarter_extension_inner,quarter_extension_inner,
    extension_fourier_pairing,←S_left c first,S_left c (S second)]
  have equation:second-S (S second)=-S (SingularCounting.centeredPower (barC c)):=by
    have paid:=congrArg S (h_power_B_source (barC c)).1
    rw [map_add] at paid
    change S first+S (S second)=_ at paid
    change second-S (S second)=-S (SingularCounting.centeredPower (barC c))
    change -S first-S (S second)=-S (SingularCounting.centeredPower (barC c))
    linear_combination (norm:=module) -paid
  have price:=congrArg (inner ℂ b) equation
  rw [inner_sub_right,inner_neg_right,←S_left c (SingularCounting.centeredPower (barC c))] at price
  change inner ℂ (S b) first+inner ℂ b second-(inner ℂ (S b) first+
    inner ℂ b (S (S second)))= -inner ℂ (S b) (SingularCounting.centeredPower (barC c))
  linear_combination price

end OriginalKCrossParameterRAdjointSource.AmbientBPriceSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
