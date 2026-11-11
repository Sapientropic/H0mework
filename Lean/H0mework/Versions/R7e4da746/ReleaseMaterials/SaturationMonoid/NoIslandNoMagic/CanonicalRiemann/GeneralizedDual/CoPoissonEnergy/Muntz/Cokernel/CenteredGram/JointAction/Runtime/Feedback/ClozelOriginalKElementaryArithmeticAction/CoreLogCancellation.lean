import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.CoreComparison
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing BurnolPhysicalState.OriginalRieszFiniteColumns
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction OriginalKSourceFiniteUpdate.OriginalBFiniteAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction

/-- A genuine B-source column; no full-loss membership is supplied by the caller. -/
def lossFirstBandColumn (c:BurnolCompletedMellinCoordinate) (h:ℝ) : M :=
  meanZeroDilation (Real.log 2-h) (sourceSB c-meanZeroDilation h (meanZeroDilation (-h) (sourceSB c)))

/-- The remaining column is generated only from the original elementary gap at both finite scales. -/
def gapFirstBandColumn (c:BurnolCompletedMellinCoordinate) (h:ℝ) : M :=
  Constructor.zeroMean (R (burnolMultiplicativeDilation (Real.log 2)
    (gapDilationDifference c h+gapDilationDifference c (-h))))

def lossLogContact (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (lossFirstBandColumn c h:Hq)

def gapLogContact (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
  (Real.sqrt 2:ℂ)*star (positionMean c)*inner ℂ SmallScaleLog.logL2 (gapFirstBandColumn c h:Hq)

theorem loss_firstBand_expanded (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    burnolMultiplicativeDilation (-Real.log 2) (E (lossFirstBandColumn c h:Hq))=FullUnit.fullSource c h 1 := by
  let d:=sourceSB c-meanZeroDilation h (meanZeroDilation (-h) (sourceSB c))
  have extension:E (d:Hq)=E (sourceSB c:Hq)-
      burnolMultiplicativeDilation h (E (meanZeroDilation (-h) (sourceSB c):Hq)) := by
    change E ((sourceSB c:Hq)-(meanZeroDilation h (meanZeroDilation (-h) (sourceSB c)):Hq))=_
    rw [map_sub,inward_extension h nn]
  change burnolMultiplicativeDilation (-Real.log 2) (E (meanZeroDilation (Real.log 2-h) d:Hq))=_
  rw [inward_extension (Real.log 2-h) (by linarith),burnolMultiplicativeDilation_add]
  rw [show -Real.log 2+(Real.log 2-h)=-h by ring,extension,map_sub,
    burnolMultiplicativeDilation_add,neg_add_cancel,burnolMultiplicativeDilation_zero]
  have actual:=outward_full_source_inventory h (sourceSB c)
  change _=fullWindowLoss h (sourceSB c)
  linear_combination (norm:=module) actual

theorem loss_firstBand_whole (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    E (lossFirstBandColumn c h:Hq)=burnolMultiplicativeDilation (Real.log 2) (FullUnit.fullSource c h 1) := by
  have actual:=congrArg (burnolMultiplicativeDilation (Real.log 2)) (loss_firstBand_expanded c h nn bound)
  rw [burnolMultiplicativeDilation_add,add_neg_cancel,burnolMultiplicativeDilation_zero] at actual
  exact actual

private theorem gap_difference_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    reflectL2 (gapDilationDifference c h)=gapDilationDifference c h := by
  unfold gapDilationDifference
  rw [map_sub,map_smul,reflectL2_burnolMultiplicativeDilation,
    show reflectL2 (gapState c)=gapState c from burnolAmbientEvenPart_even _]

private theorem loss_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) :
    reflectL2 (FullUnit.fullSource c h 1)=FullUnit.fullSource c h 1 := by
  have actual:=position_core_even c h
  unfold positionCoreSource at actual
  rw [map_smul,map_add,map_add,gap_difference_even,gap_difference_even] at actual
  linear_combination (norm:=module) (-2:ℂ) • actual

theorem loss_firstBand_even (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    reflectRestricted q (lossFirstBandColumn c h:Hq)=lossFirstBandColumn c h := by
  have parity:reflectL2 (E (lossFirstBandColumn c h:Hq))=E (lossFirstBandColumn c h:Hq) := by
    rw [loss_firstBand_whole c h nn bound,reflectL2_burnolMultiplicativeDilation,loss_even]
  have actual:=congrArg R parity
  change R (reflectL2 (burnolRadiusZeroExtension q (lossFirstBandColumn c h:Hq)))=_ at actual
  rw [burnolRadiusZeroExtension_reflect] at actual
  change R (E (reflectRestricted q (lossFirstBandColumn c h:Hq)))=R (E (lossFirstBandColumn c h:Hq)) at actual
  rw [burnolQuarterRestriction_zeroExtension,burnolQuarterRestriction_zeroExtension] at actual
  exact actual

private theorem zeroMean_fixed (v:M) : Constructor.zeroMean (v:Hq)=v := by
  apply Subtype.ext
  rw [Constructor.zeroMean_read,Constructor.mean_zero,zero_smul,sub_zero]

theorem source_log_columns (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    compressedCoreSource c h=-(1/2:ℂ) • (gapFirstBandColumn c h+lossFirstBandColumn c h) := by
  have lossRead:Constructor.zeroMean (R (burnolMultiplicativeDilation (Real.log 2) (FullUnit.fullSource c h 1)))=
      lossFirstBandColumn c h := by
    rw [←loss_firstBand_whole c h nn bound,burnolQuarterRestriction_zeroExtension,zeroMean_fixed]
  unfold compressedCoreSource positionCoreSource
  rw [map_smul,map_add,map_smul,map_add,map_smul,map_add,lossRead]
  rfl

/-- The same actual SB column appears twice, so its entire log contact cancels. -/
theorem source_log_contact_cancellation (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    -positionLogPrice c h-(1/2:ℂ)*lossLogContact c h=(1/2:ℂ)*gapLogContact c h := by
  unfold positionLogPrice lossLogContact gapLogContact
  rw [source_log_columns c h nn bound]
  change -(_*inner ℂ SmallScaleLog.logL2 (-(1/2:ℂ) • ((gapFirstBandColumn c h:Hq)+(lossFirstBandColumn c h:Hq))))-_=_
  rw [inner_smul_right,inner_add_right]
  ring

/-- The reverse programme reads precisely the same generated B column used by the generic first band. -/
theorem full_reverse_SB_price (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) :
    inner ℂ (sourceKernel c) (FullUnit.fullReverse c h 1)=
      inner ℂ (sourceKernel c) (FullUnit.fullSource c h 1)+lossLogContact c h := by
  have first:=meanZero_firstBand_counted_read c zero (lossFirstBandColumn c h) (loss_firstBand_even c h nn bound)
  rw [loss_firstBand_expanded c h nn bound] at first
  have left:=(KCountingGram.forward_tendsto c zero).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=FullUnit.fullSource c h 1))
  have right:=(tendsto_const_nhds (x:=(burnolCompletedMellinRieszVector c:BurnolL2))).inner (𝕜:=ℂ)
    (FullUnit.full_reverse_tendsto c h nn 1)
  have same:=left.congr' (Eventually.of_forall (fun N=>CountingDual.source_pairing N
    (burnolCompletedMellinRieszVector c:BurnolL2) (FullUnit.fullSource c h 1)))
  have actual:=tendsto_nhds_unique same right
  rw [←sourceKernel_original c,first] at actual
  exact actual.symm

/-- After the literal SB cancellation, only the elementary gap log and the original loss cross-price remain. -/
theorem original_fixedResidual_gap_log_source (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0)
    (h:ℝ) (nn:0≤h) (bound:h≤Real.log 2) (fixed:h=Real.log stageZeroSonineQ) :
    -burnolPaFixedShiftResidual c zero=
      ((pairedMellinTranslationCharacter c.value h-((Real.exp (h/2):ℂ)+(Real.exp (-h/2):ℂ))/2)*reverseMean c zero+
        (2*q:ℝ)*GapEuler.gapMean q c*(Complex.exp (OriginalKSourceResolventReconstruction.sourceRate c*(h:ℂ))-(Real.exp (-h/2):ℂ)))*
        inner ℂ (sourceKernel c) ConstantDual.seed-(1/2:ℂ)*inner ℂ (sourceKernel c) (collarSource c h)-
      coreCharacterDefect c h*(reverseMean c zero*inner ℂ (sourceKernel c) ConstantDual.seed-kernelSelfSource c)+
      (1/2:ℂ)*gapLogContact c h-
      (1/2:ℂ)*(inner ℂ (sourceKernel c) (FullUnit.fullSource c h 1)-
        inner ℂ (sourceKernel c) (fourierL2 (FullUnit.fullSource c h 0))) := by
  have price:=original_fixedResidual_firstBand_source c zero h nn bound fixed
  rw [full_reverse_SB_price c zero h nn bound] at price
  have self:inner ℂ (sourceKernel c) (elementarySource c)=kernelSelfSource c := by
    rw [sourceKernel_original]
    change inner ℂ (burnolCompletedMellinRieszVector c:BurnolL2) (gapState c)=_
    rw [gapState_eq_kernel_add_correction,inner_add_right,kernel_inner_sourceCorrection_zero,add_zero]
    exact original_kernel_self_source c
  rw [self] at price
  have cancel:=source_log_contact_cancellation c h nn bound
  linear_combination price+cancel

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
