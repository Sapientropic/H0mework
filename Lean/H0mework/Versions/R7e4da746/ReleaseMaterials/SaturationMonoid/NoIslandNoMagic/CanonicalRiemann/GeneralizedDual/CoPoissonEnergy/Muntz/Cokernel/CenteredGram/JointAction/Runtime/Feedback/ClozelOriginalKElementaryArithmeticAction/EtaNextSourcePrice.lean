import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CountedUnitRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CoreUnitProgramme
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FourierUnitPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalEtaNextSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction OriginalKExteriorCoPoissonAction OriginalKFiniteOrderRelease
open OriginalFullLossRAction OriginalReverseCoreJumpMean
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "L" => OriginalRieszSourceGreen.sourceCorrection
local instance : CompleteSpace M :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
open private gamma conjugate_zero unitCurrent FT boxProgram unitTailProgram
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitRProgram
open private SBWeight SBSlope SB_regular
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FullLossRAction
open private pair_raw box_price tail_price dilation_raw unitCurrent_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseCoreJumpMean
open private column_raw
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Source
open private original_B_pair extension_price fourier_extension_price
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPrice
open private core_reverse_even coefficient
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CurrentRegularPriceConsumer
open private extension_even
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

def correctionRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
  Constructor.fourierRaw (sourceProfile c 0) x-(symmetricInterval q).indicator (sourceProfile c 1) x

def reciprocalCorrectionRaw (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
  burnolTateReciprocalRaw (fun x=>(symmetricInterval q).indicator (sourceProfile c 0) x-
    Constructor.fourierRaw (sourceProfile c 1) x)

private theorem profile_read (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    ((sourceColumn c i:Hq):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] sourceProfile c i := by
  fin_cases i
  · exact burnolRieszSingleFourierSource_ae_raw c
  · exact Constructor.returnState_read c

private theorem fourier_column_raw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) :
    (F (E (sourceColumn c i:Hq)):ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (sourceProfile c i) := by
  have raw:=burnolRadiusFourierL2_zeroExtension_ae_eq_raw (sourceColumn c i:Hq)
  change (F (E (sourceColumn c i:Hq)):ℝ→ℂ)=ᵐ[volume] Constructor.fourierRaw (sourceColumn c i:Hq) at raw
  rw [Constructor.fourierRaw_congr _ _ (profile_read c i)] at raw
  exact raw

private theorem correction_raw (c:BurnolCompletedMellinCoordinate) :
    (L c:ℝ→ℂ)=ᵐ[volume] correctionRaw c := by
  change ((F (E (sourceColumn c 0:Hq))-E (sourceColumn c 1:Hq):BurnolL2):ℝ→ℂ)=ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (F (E (sourceColumn c 0:Hq))) (E (sourceColumn c 1:Hq)),
    fourier_column_raw c 0,column_raw c 1] with x difference left right
  rw [difference,Pi.sub_apply,left,right]
  rfl

private theorem B_extension_even (c:BurnolCompletedMellinCoordinate) :
    reflectL2 (E (sourceB c:Hq))=E (sourceB c:Hq) :=
  extension_even _ (burnolRieszSingleFourierSource_reflection_fixed c)

private theorem SB_extension_even (c:BurnolCompletedMellinCoordinate) :
    reflectL2 (E (sourceSB c:Hq))=E (sourceSB c:Hq) :=
  extension_even _ (burnolRieszSingleFourierReturn_reflection_fixed c)

private theorem correction_even (c:BurnolCompletedMellinCoordinate) : reflectL2 (L c)=L c := by
  change reflectL2 (F (E (sourceB c:Hq))-E (sourceSB c:Hq))=_
  rw [map_sub,←fourierL2_reflectL2_commute,B_extension_even,SB_extension_even]
  rfl

private theorem reciprocal_correction_raw (c:BurnolCompletedMellinCoordinate) :
    (T (F (L c)):ℝ→ℂ)=ᵐ[volume] reciprocalCorrectionRaw c := by
  have raw:(F (L c):ℝ→ℂ)=ᵐ[volume] fun x=>(symmetricInterval q).indicator (sourceProfile c 0) x-
      Constructor.fourierRaw (sourceProfile c 1) x := by
    change (F (F (E (sourceB c:Hq))-E (sourceSB c:Hq)):ℝ→ℂ)=ᵐ[volume] _
    rw [map_sub,fourierL2_fourierL2,B_extension_even]
    change ((E (sourceColumn c 0:Hq)-F (E (sourceColumn c 1:Hq)):BurnolL2):ℝ→ℂ)=ᵐ[volume] _
    filter_upwards [Lp.coeFn_sub (E (sourceColumn c 0:Hq)) (F (E (sourceColumn c 1:Hq))),
      column_raw c 0,fourier_column_raw c 1] with x difference left right
    rw [difference,Pi.sub_apply,left,right]
  have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp (F (L c)))
    ((Lp.memLp (F (L c))).ae_eq raw) raw
  exact (burnolTateReciprocalL2_coeFn (F (L c))).trans pulled

private theorem FT_price (c:BurnolCompletedMellinCoordinate) (v:BurnolL2) :
    inner ℂ (L c) (FT v)=inner ℂ (T (F (L c))) v := by
  have twice:F (F (L c))=L c := by rw [fourierL2_fourierL2,correction_even]
  have actual:=fourierL2.inner_map_map (F (L c)) (T v)
  rw [twice] at actual
  exact actual.trans (OriginalRieszFiniteSynthesis.tate_pairing _ _).symm

def correctionBoundaryPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (profile:ℝ→ℂ) : ℂ :=
  pairedMellinTranslationCharacter c.value h*rawPair (correctionRaw c) profile-
    (1/2:ℂ)*(rawPair (correctionRaw c) (dilationProfile h profile)+
      rawPair (correctionRaw c) (dilationProfile (-h) profile))

def correctionLossPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (profile:ℝ→ℂ) : ℂ :=
  boxPrice (correctionRaw c) q (q*Real.exp h) (SBWeight c h) (SBSlope c h) profile+
    centeringMean c h 1*rawPair (correctionRaw c) profile-
    (boxPrice (reciprocalCorrectionRaw c) (bandLower h) 4 (positiveWeight c h 0)
        (deriv (positiveWeight c h 0)) profile+
      centeringMean c h 0*tailPrice (reciprocalCorrectionRaw c) profile)

def correctionCurrentPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (2*gamma c)*correctionBoundaryPrice c h (elementaryReverseRaw (barC c))-
    (2*gamma (barC c))*correctionBoundaryPrice c h (elementaryReverseRaw c)-
    (((c.value-star c.value)*gamma (barC c))*(1/2:ℂ))*correctionLossPrice c h (unitCurrentProfile c)

private theorem boundary_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2)
    (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (L c) (OriginalKFixedBoundarySourceFibre.finiteBoundaryAction c h value)=
      correctionBoundaryPrice c h raw := by
  unfold OriginalKFixedBoundarySourceFibre.finiteBoundaryAction correctionBoundaryPrice
  rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right]
  rw [pair_raw _ _ _ _ (correction_raw c) actual,
    pair_raw _ _ _ _ (correction_raw c) (dilation_raw h value raw actual),
    pair_raw _ _ _ _ (correction_raw c) (dilation_raw (-h) value raw actual)]

private theorem loss_price (c:BurnolCompletedMellinCoordinate) (h:ℝ) (value:BurnolL2)
    (raw:ℝ→ℂ) (actual:(value:ℝ→ℂ)=ᵐ[volume] raw) :
    inner ℂ (L c) (boxProgram q (q*Real.exp h) (SBWeight c h) (SBSlope c h) value+
        centeringMean c h 1 • value-
      FT (boxProgram (bandLower h) 4 (positiveWeight c h 0) (deriv (positiveWeight c h 0)) value+
        centeringMean c h 0 • unitTailProgram value))=correctionLossPrice c h raw := by
  have regular:ContinuousOn (deriv (positiveWeight c h 0)) (Icc (bandLower h) 4) :=
    (positiveWeight_deriv_continuousOn c h 0).mono (fun _ inside=>(bandLower_pos h).trans_le inside.1)
  unfold correctionLossPrice
  rw [inner_sub_right,inner_add_right,inner_smul_right,FT_price,inner_add_right,inner_smul_right]
  rw [box_price _ value _ raw (correction_raw c) actual _ _ _ _ (by norm_num) (SB_regular c h).continuousOn,
    pair_raw _ value _ raw (correction_raw c) actual,
    box_price _ value _ raw (reciprocal_correction_raw c) actual _ _ _ _ (bandLower_pos h) regular,
    tail_price _ value _ raw (reciprocal_correction_raw c) actual]

/-- Complete original B correction is priced by the actual finite and infinite source programme. -/
theorem correction_current_source (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (h:ℝ) :
    inner ℂ (L c) (completeCoreRCurrent c zero h)=correctionCurrentPrice c h := by
  unfold completeCoreRCurrent correctionCurrentPrice
  rw [inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,inner_smul_right,
    boundary_price c h _ _ (elementary_reverse_raw (barC c) (conjugate_zero c zero)),
    boundary_price c h _ _ (elementary_reverse_raw c zero),loss_price c h _ _ (unitCurrent_raw c zero)]

private theorem eta_B_price (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) :
    inner ℂ (sourceEta c) (burnolAmbientMeanZeroSecondCorrection value)=inner ℂ (L c) value := by
  have law:=original_B_pair c value
  change _=inner ℂ (F (E (sourceB c:Hq))-E (sourceSB c:Hq)) value
  have BParity:reflectRestricted q (sourceB c:Hq)=sourceB c:=burnolRieszSingleFourierSource_reflection_fixed c
  have SBParity:reflectRestricted q (sourceSB c:Hq)=sourceSB c:=burnolRieszSingleFourierReturn_reflection_fixed c
  rw [inner_sub_left,fourier_extension_price (sourceB c) BParity value,
    extension_price (sourceSB c) SBParity value]
  linear_combination law

/-- The original primitive programme after its actual Fourier-unit source is consumed. -/
def primitiveInputPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  OriginalCurrentRegularPrice.elementaryBoundarySourcePrice c h-(1/2:ℂ)*
    (rawPair (burnolEvenRaw (burnolAmbientMellinKernelRaw c))
      (dilationProfile (-h) ((symmetricInterval q).indicator (sourceProfile c 1)))+
      (Real.sqrt 2:ℂ)*star (GapEuler.gapMean q c)*
        inner ℂ SmallScaleLog.logL2 (lossFirstBandColumn c h:Hq))

private theorem primitive_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
    OriginalCurrentRegularPrice.elementaryCoreSourcePrice c h=primitiveInputPrice c h := by
  unfold OriginalCurrentRegularPrice.elementaryCoreSourcePrice primitiveInputPrice
  rw [OriginalFourierUnitPrice.elementary_fourier_unit c zero,mul_zero,sub_zero]

/-- Both original unit source calculations are consumed inside the complete counted difference. -/
def countedDifferencePrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  coreCharacterDefect c h*((star c.value*GapEuler.gapMean q c/(1-star c.value))*
      ((1/2:ℂ)*star (OriginalRieszFinitePairing.positionMean c))-OriginalRieszFinitePairing.kernelSelfSource c)+
    positionLogPrice c h+(1/2:ℂ)*
      (centeringMean c h 0*(-inner ℂ (sourceB c:Hq) SmallScaleLog.logL2)-
        (OriginalKExteriorBCotest.sourcePrice c h+
          centeringMean c h 0*((1/2:ℂ)*star (OriginalRieszFinitePairing.fourierMean c))))

private theorem counted_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) :
    OriginalCompleteCountedSource.calculatedDifference c h=countedDifferencePrice c h := by
  have read:=OriginalCountedUnitRead.calculated_units c zero h
  unfold countedDifferencePrice
  linear_combination read

/-- Fixed c/h source calculation: all current, core and next-eta inner prices have been executed. -/
def sourcePrice (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0) (h:ℝ) : ℂ :=
  let a:=coefficient c
  let input:=coreReverseSource c zero h
  let first:=GenericSourceStepBAction.firstNext (barC c) (F input)
  let second:=GenericSourceStepBAction.secondNext (barC c) (F input)
  let mean0:=OriginalCoreUnitProgramme.currentUnitPrice c h 0
  let mean1:=OriginalCoreUnitProgramme.currentUnitPrice c h 1
  let meanCore:=OriginalCoreUnitProgramme.coreUnitPrice c h 0
  (-star (Kernel.A c)*(a*(q:ℂ)*(burnolMeanZeroFourierRaw first q+burnolMeanZeroFourierRaw first (-q))+
        (1-c.value)*mean0)-
    star (Kernel.beta c)*(a*(q:ℂ)*(burnolMeanZeroFourierRaw second q+burnolMeanZeroFourierRaw second (-q))+
        c.value*mean1)+
    (c.value*star (gamma c)*mean0+2*a*star (gamma c)*meanCore-2*a*primitiveInputPrice c h-
      (2*c.value-1)*correctionCurrentPrice c h)-
    2*a*coreJumpPrice c h-(2*c.value-1)*currentJumpPrice c h+2*a*countedDifferencePrice c h)/(2*a)


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h0" => Real.log stageZeroSonineQ
local notation "a" => coefficient c
local notation "v" => coreReverseSource c observation.mathlibZero h0
local notation "current" => completeCoreRCurrent c observation.mathlibZero h0
local notation "nextFirst" => GenericSourceStepBAction.firstNext (barC c) (F v)
local notation "nextSecond" => GenericSourceStepBAction.secondNext (barC c) (F v)

/-- The actual next B pairing is paid from the original source programme without dividing its coefficient. -/
theorem original_eta_next_source :
    a*inner ℂ (sourceEta c) nextFirst=correctionCurrentPrice c h0 := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have even:=core_reverse_even c observation.mathlibZero h0 nn
  have update:=GenericSourceStepBAction.actual_forward_R_B c v even
  have source:=OriginalFullLossRAction.original_core_R_update observation nontrivial half
  change a • burnolDirectRightResolventCLM c v=current at source
  have pair:=eta_B_price c (burnolDirectRightResolventCLM c v)
  rw [update.2] at pair
  rw [←correction_current_source c observation.mathlibZero h0,←source,inner_smul_right,←pair]

/-- The same original fixed residual reads the complete source-only price. -/
theorem original_fixedResidual_source_price :
    burnolPaFixedShiftResidual c observation.mathlibZero=sourcePrice c observation.mathlibZero h0 := by
  have nn:0≤h0:=Real.log_nonneg (by norm_num [stageZeroSonineQ])
  have read:=OriginalCurrentRegularPrice.original_fixedResidual_source_prices observation nontrivial half
  have paid:=original_eta_next_source observation nontrivial half
  have effect:(2*(c).value-1)*a*inner ℂ (sourceEta c) nextFirst=
      (2*(c).value-1)*correctionCurrentPrice c h0 := by rw [mul_assoc,paid]
  rw [effect,primitive_source c observation.mathlibZero h0,counted_source c observation.mathlibZero h0] at read
  have mean0:=OriginalCoreUnitProgramme.current_unit_source c observation.mathlibZero h0 0
  have mean1:=OriginalCoreUnitProgramme.current_unit_source c observation.mathlibZero h0 1
  have meanCore:=OriginalCoreUnitProgramme.core_unit_source c observation.mathlibZero h0 nn 0
  change inner ℂ ConstantDual.seed current=OriginalCoreUnitProgramme.currentUnitPrice c h0 0 at mean0
  change inner ℂ (F ConstantDual.seed) current=OriginalCoreUnitProgramme.currentUnitPrice c h0 1 at mean1
  change inner ℂ ConstantDual.seed v=OriginalCoreUnitProgramme.coreUnitPrice c h0 0 at meanCore
  rw [mean0,mean1,meanCore] at read
  exact read

end OriginalEtaNextSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
