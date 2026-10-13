import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.Forcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace ENNReal
open OriginalTwoWindowInverseForcing
local notation "q" => (1/4:ℝ)
local notation "S" => burnolMeanZeroTruncatedFourier

private def bandCut (h : ℝ) (field : BurnolL2) : BurnolL2 :=
  ((Lp.memLp field).indicator (show MeasurableSet (sourceBand h) from measurableSet_uIcc)).toLp
    ((sourceBand h).indicator (field:ℝ→ℂ))
private theorem bandCut_raw (h : ℝ) (field : BurnolL2) :
    (bandCut h field:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator (field:ℝ→ℂ) := MemLp.coeFn_toLp _

def sourceFourierBand (state : BurnolQuarterMeanZeroCarrier) (h scale : ℝ) : BurnolL2 :=
  (Real.exp (-scale/2):ℂ)•bandCut h (burnolMultiplicativeDilation scale (fourierL2 (whole state)))

theorem sourceFourierBand_raw (state : BurnolQuarterMeanZeroCarrier) (h scale : ℝ) :
    (sourceFourierBand state h scale:ℝ→ℂ)=ᵐ[volume]
      (sourceBand h).indicator (fun x:ℝ=>rawFourier state (Real.exp scale*x)) := by
  have normalization : (Real.exp (-scale/2):ℂ)*(Real.exp (scale/2):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show -scale/2+scale/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  filter_upwards [Lp.coeFn_smul (Real.exp (-scale/2):ℂ)
    (bandCut h (burnolMultiplicativeDilation scale (fourierL2 (whole state)))),
    bandCut_raw h (burnolMultiplicativeDilation scale (fourierL2 (whole state))),
    whole_fourier_dilation_raw state scale] with x scalar band fourier
  unfold sourceFourierBand
  rw [scalar]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [band]
  by_cases inside : x∈sourceBand h
  · rw [indicator_of_mem inside,indicator_of_mem inside,fourier,← mul_assoc,normalization,one_mul]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside,mul_zero]

def bForcingBand (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) : BurnolL2 :=
  bBand coordinate h scale-sourceFourierBand (Constructor.returnState coordinate) h scale
def pGapBand (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) : BurnolL2 :=
  pBand coordinate h scale+sourceFourierBand (burnolRieszSingleFourierSource coordinate) h scale

theorem actual_b_forcing_band (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    (bForcingBand coordinate h scale:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator
      (fun x:ℝ=>Translator.ForcingWhole.raw coordinate (Real.exp scale*x)-
        Translator.ForcingMeanZero.mean coordinate-OriginalInverseReturnActionSource.returnMean coordinate) := by
  filter_upwards [Lp.coeFn_sub (bBand coordinate h scale)
    (sourceFourierBand (Constructor.returnState coordinate) h scale),bBand_raw coordinate h scale,
    sourceFourierBand_raw (Constructor.returnState coordinate) h scale] with x subtraction bRead returnRead
  unfold bForcingBand
  rw [subtraction]
  simp only [Pi.sub_apply]
  rw [bRead,returnRead]
  by_cases inside : x∈sourceBand h
  · rw [indicator_of_mem inside,indicator_of_mem inside,indicator_of_mem inside,
      return_full_fourier]
    unfold bLeg b OriginalInverseReturnActionSource.fullInverseReturnProfile
    ring
  · rw [indicator_of_notMem inside,indicator_of_notMem inside,indicator_of_notMem inside,sub_self]

theorem actual_p_gap_band (coordinate : BurnolCompletedMellinCoordinate) (h scale : ℝ) :
    (pGapBand coordinate h scale:ℝ→ℂ)=ᵐ[volume] (sourceBand h).indicator
      (fun x:ℝ=>(1/2:ℂ)*(Real.exp scale*x:ℂ)^(-star coordinate.value)-
        GapEuler.gapMean q coordinate+sourceMean coordinate) := by
  filter_upwards [Lp.coeFn_add (pBand coordinate h scale)
    (sourceFourierBand (burnolRieszSingleFourierSource coordinate) h scale),pBand_raw coordinate h scale,
    sourceFourierBand_raw (burnolRieszSingleFourierSource coordinate) h scale] with x addition pRead sourceRead
  unfold pGapBand
  rw [addition]
  simp only [Pi.add_apply]
  rw [pRead,sourceRead]
  by_cases inside : x∈sourceBand h
  · rw [indicator_of_mem inside,indicator_of_mem inside,indicator_of_mem inside,source_full_fourier]
    unfold pLeg p OriginalRieszFinitePairing.positionSource
    rw [Complex.ofReal_mul]
    ring
  · rw [indicator_of_notMem inside,indicator_of_notMem inside,indicator_of_notMem inside,add_zero]

theorem cotestColumn_add (scale : ℝ) (left right : BurnolL2) :
    cotestColumn scale (left+right)=cotestColumn scale left+cotestColumn scale right := by
  unfold cotestColumn Constructor.zeroMean burnolAmbientEvenPart
  simp only [map_add,smul_add]
  module
theorem cotestColumn_sub (scale : ℝ) (left right : BurnolL2) :
    cotestColumn scale (left-right)=cotestColumn scale left-cotestColumn scale right := by
  apply eq_sub_iff_add_eq.mpr
  have additive:=cotestColumn_add scale (left-right) right
  simpa only [sub_add_cancel] using additive.symm


def jointBandDrive (coordinate : BurnolCompletedMellinCoordinate) (h testScale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier :=
  cotestColumn testScale (sourceFourierBand (Constructor.returnState coordinate) h leg)+
    S (cotestColumn testScale (sourceFourierBand (burnolRieszSingleFourierSource coordinate) h leg))+
    cotestColumn testScale (bForcingBand coordinate h leg)-
    S (cotestColumn testScale (pGapBand coordinate h leg))

theorem actual_joint_band_drive (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).1=jointBandDrive coordinate h (-h/2) (h/2) ∧
    burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).2=jointBandDrive coordinate h (h/2) (-h/2) := by
  have expand (testScale leg : ℝ) :
      cotestColumn testScale (bBand coordinate h leg)-S (cotestColumn testScale (pBand coordinate h leg))=
        jointBandDrive coordinate h testScale leg := by
    have bSplit : bBand coordinate h leg=
        sourceFourierBand (Constructor.returnState coordinate) h leg+bForcingBand coordinate h leg := by
      unfold bForcingBand
      abel
    have pSplit : pBand coordinate h leg=
        pGapBand coordinate h leg-sourceFourierBand (burnolRieszSingleFourierSource coordinate) h leg := by
      unfold pGapBand
      abel
    rw [bSplit,pSplit,cotestColumn_add,cotestColumn_sub,map_sub]
    unfold jointBandDrive
    abel
  obtain ⟨lower,upper⟩:=actual_inverse_cotest coordinate h
  change burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).1=
    cotestColumn (-h/2) (bBand coordinate h (h/2))-S (cotestColumn (-h/2) (pBand coordinate h (h/2))) at lower
  change burnolMeanZeroOneMinusSquare (inverseCotest coordinate h).2=
    cotestColumn (h/2) (bBand coordinate h (-h/2))-S (cotestColumn (h/2) (pBand coordinate h (-h/2))) at upper
  rw [expand] at lower upper
  exact ⟨lower,upper⟩

end OriginalCommonInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
