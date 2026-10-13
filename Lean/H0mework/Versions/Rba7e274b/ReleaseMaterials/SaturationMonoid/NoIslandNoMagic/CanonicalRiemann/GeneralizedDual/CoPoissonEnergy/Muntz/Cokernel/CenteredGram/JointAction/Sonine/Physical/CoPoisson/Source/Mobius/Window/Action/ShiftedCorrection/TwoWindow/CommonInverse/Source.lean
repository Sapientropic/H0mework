import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Reaction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource FixedWindowFourierReaction
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)
local notation "Sq" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "S" => centeredOperator

def driveInventory (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier :=
  (cotestColumn (-h/2) (bForcingBand coordinate h (h/2))-
      Sq (cotestColumn (-h/2) (pGapBand coordinate h (h/2))),
   cotestColumn (h/2) (bForcingBand coordinate h (-h/2))-
      Sq (cotestColumn (h/2) (pGapBand coordinate h (-h/2))))

theorem actual_joint_inverse_window (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    L (inverseCotest coordinate h).1=((Real.exp (-h/4):ℂ)/2)•
      (windowKernelColumn (Constructor.returnState coordinate) h (-h/2) (h/2)+
       Sq (windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (-h/2) (h/2)))+
      (driveInventory coordinate h).1 ∧
    L (inverseCotest coordinate h).2=((Real.exp (h/4):ℂ)/2)•
      (windowKernelColumn (Constructor.returnState coordinate) h (h/2) (-h/2)+
       Sq (windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (h/2) (-h/2)))+
      (driveInventory coordinate h).2 := by
  have returnEven : reflectRestricted q (Constructor.returnState coordinate:BurnolQuarterIntervalL2)=
      Constructor.returnState coordinate := burnolRieszSingleFourierReturn_reflection_fixed coordinate
  have sourceEven:=burnolRieszSingleFourierSource_reflection_fixed coordinate
  obtain ⟨lower,upper⟩:=actual_joint_band_drive coordinate h
  rw [jointBandDrive,source_cotest_window_sandwich _ returnEven _ _ _ nonnegative,
    source_cotest_window_sandwich _ sourceEven _ _ _ nonnegative] at lower upper
  rw [show -(h/2)/2=-h/4 by ring,map_smul] at lower
  rw [show -(-h/2)/2=h/4 by ring,map_smul] at upper
  unfold driveInventory
  constructor
  · rw [lower]
    module
  · rw [upper]
    module

def lowerKernelField (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) : H :=
  S q (S (upperRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))-
    S (lowerRadius h) (S q (quarterChart (state:BurnolQuarterIntervalL2)))+lowerWindowMean state h
def upperKernelField (state : BurnolQuarterMeanZeroCarrier) (h : ℝ) : H :=
  S (upperRadius h) (S q (quarterChart (state:BurnolQuarterIntervalL2)))-
    S q (S (lowerRadius h) (quarterChart (state:BurnolQuarterIntervalL2)))+upperWindowMean state h

def jointForcingRead (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (inverse partner : BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier) : ℂ :=
  (Real.exp (h/4):ℂ)*(star (Kernel.A coordinate)*inner ℂ Response.eta partner.1-
    star (Kernel.beta coordinate)*inner ℂ Response.eta inverse.1)+
  (Real.exp (-h/4):ℂ)*(Kernel.A coordinate*star (inner ℂ Response.eta partner.2)-
    Kernel.beta coordinate*star (inner ℂ Response.eta inverse.2))

structure JointSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) where
  inverse : BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier
  partner : BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier
  lowerKernel : BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier
  upperKernel : BurnolQuarterMeanZeroCarrier×BurnolQuarterMeanZeroCarrier
  inverseSource : inverse=inverseCotest coordinate h
  partnerSource : partner=inversePartner coordinate h
  lowerSource : lowerKernel=(windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (-h/2) (h/2),
    windowKernelColumn (Constructor.returnState coordinate) h (-h/2) (h/2))
  upperSource : upperKernel=(windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (h/2) (-h/2),
    windowKernelColumn (Constructor.returnState coordinate) h (h/2) (-h/2))
  lowerAction : L inverse.1=((Real.exp (-h/4):ℂ)/2)•(lowerKernel.2+Sq lowerKernel.1)+(driveInventory coordinate h).1
  upperAction : L inverse.2=((Real.exp (h/4):ℂ)/2)•(upperKernel.2+Sq upperKernel.1)+(driveInventory coordinate h).2
  lowerPhysical : quarterChart (lowerKernel.1:BurnolQuarterIntervalL2)=lowerKernelField (burnolRieszSingleFourierSource coordinate) h ∧
    quarterChart (lowerKernel.2:BurnolQuarterIntervalL2)=lowerKernelField (Constructor.returnState coordinate) h
  upperPhysical : quarterChart (upperKernel.1:BurnolQuarterIntervalL2)=upperKernelField (burnolRieszSingleFourierSource coordinate) h ∧
    quarterChart (upperKernel.2:BurnolQuarterIntervalL2)=upperKernelField (Constructor.returnState coordinate) h
  jointPrice : inner ℂ (originalB coordinate)
    (quarterChart (lowerKernel.1:BurnolQuarterIntervalL2)+quarterChart (upperKernel.1:BurnolQuarterIntervalL2))=
    mixedReactionPrice coordinate (upperRadius h)-mixedReactionPrice coordinate (lowerRadius h)+
      originalJointWindowMeanPrice coordinate h
  forcingAction : (∫ x:ℝ in (lowerRadius h)..(upperRadius h),forcingCross coordinate h x)=
    jointForcingRead coordinate h inverse partner+forcingInventory coordinate h

def generatedJointSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) : JointSource coordinate h where
  inverse:=inverseCotest coordinate h
  partner:=inversePartner coordinate h
  lowerKernel:=(windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (-h/2) (h/2),
    windowKernelColumn (Constructor.returnState coordinate) h (-h/2) (h/2))
  upperKernel:=(windowKernelColumn (burnolRieszSingleFourierSource coordinate) h (h/2) (-h/2),
    windowKernelColumn (Constructor.returnState coordinate) h (h/2) (-h/2))
  inverseSource:=rfl
  partnerSource:=rfl
  lowerSource:=rfl
  upperSource:=rfl
  lowerAction:=(actual_joint_inverse_window coordinate h nonnegative).1
  upperAction:=(actual_joint_inverse_window coordinate h nonnegative).2
  lowerPhysical:=⟨source_lower_window_complete _ h,source_lower_window_complete _ h⟩
  upperPhysical:=⟨source_upper_window_complete _ h,source_upper_window_complete _ h⟩
  jointPrice:=original_joint_window_reaction_price coordinate h
  forcingAction:=forcingCross_common_inverse coordinate h nonnegative

def JointSource.price {coordinate : BurnolCompletedMellinCoordinate} {h : ℝ}
    (source : JointSource coordinate h) : ℂ :=
  2*(sourceAction coordinate h (upperRadius h)-sourceAction coordinate h (lowerRadius h)-
      jointForcingRead coordinate h source.inverse source.partner-forcingInventory coordinate h)/coupling coordinate

theorem generated_joint_source_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    (generatedJointSource coordinate h nonnegative).price=forcingPrice coordinate h := by
  unfold JointSource.price forcingPrice
  rw [(generatedJointSource coordinate h nonnegative).forcingAction]
  ring

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
