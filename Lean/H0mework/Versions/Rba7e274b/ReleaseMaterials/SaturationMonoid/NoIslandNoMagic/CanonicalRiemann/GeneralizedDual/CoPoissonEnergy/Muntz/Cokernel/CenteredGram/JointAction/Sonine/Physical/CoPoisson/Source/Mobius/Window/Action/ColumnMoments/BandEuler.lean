import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Contact
import H0mework.Versions.V2.Arithmetic.RieszGreen.SourceDerivative
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open OriginalRieszSource

 theorem source_weighted_continuous (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ} (nonzero : x≠0) :
    ContinuousAt (OriginalRieszSourceGreen.weightedRaw coordinate) x := by
  rw [show OriginalRieszSourceGreen.weightedRaw coordinate=(fun x=>(star coordinate.value-1/2)*Translator.ForcingWhole.raw coordinate x+
    (star coordinate.value*GapEuler.gapMean (1/4:ℝ) coordinate)*Edge.raw (1/4:ℝ) x+
    Constructor.secondEulerRaw coordinate x-(1/2:ℂ)*Translator.ForcingMeanZero.mean coordinate) by
      funext y;exact OriginalRieszSourceGreen.weightedRaw_eq coordinate y]
  exact ((continuousAt_const.mul (Translator.ForcingWhole.raw_continuousAt coordinate nonzero)).add
    (continuousAt_const.mul (Edge.raw_continuous (1/4:ℝ)).continuousAt)).add
      (Constructor.secondEulerRaw_continuous coordinate).continuousAt |>.sub continuousAt_const

def contactResponse (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  Kernel.A coordinate • (Response.u:BurnolQuarterIntervalL2)-Kernel.beta coordinate • (Response.v:BurnolQuarterIntervalL2)

theorem original_contact_response_read (coordinate : BurnolCompletedMellinCoordinate) :
    (contactResponse coordinate : ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval (1/4:ℝ))]
      fun x=>OriginalRieszSourceGreen.weightedRaw coordinate x-Kernel.beta coordinate-
        (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x := by
  have source := congrArg (fun value : BurnolQuarterMeanZeroCarrier=>(value:BurnolQuarterIntervalL2))
    (Euler.sourceEuler_eq coordinate)
  have sourceField : contactResponse coordinate=(Euler.sourceEuler coordinate:BurnolQuarterIntervalL2)-
      (star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2) := by
    change (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2)=
      (star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)+
        Kernel.A coordinate • (Response.u:BurnolQuarterIntervalL2)-Kernel.beta coordinate • (Response.v:BurnolQuarterIntervalL2) at source
    rw [source]
    unfold contactResponse
    module
  rw [sourceField]
  filter_upwards [Lp.coeFn_sub (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2)
      ((star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2)),
    Lp.coeFn_smul (star coordinate.value-1/2) (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2),
    burnolRieszSingleFourierSource_ae_raw coordinate,Euler.sourceEuler_read coordinate] with x difference scalar actual euler
  rw [difference]
  change (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2) x-
    ((star coordinate.value-1/2) • (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2):BurnolQuarterIntervalL2) x=_
  rw [scalar]
  change (Euler.sourceEuler coordinate:BurnolQuarterIntervalL2) x-(star coordinate.value-1/2)*(burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2) x=_
  rw [actual,euler]
  unfold OriginalRieszSourceGreen.weightedRaw OriginalRieszSourceGreen.centeredRaw
  ring

 theorem original_band_euler_flux (coordinate : BurnolCompletedMellinCoordinate) (lower upper : ℝ)
    (lowerPositive : 0<lower) (ordered : lower≤upper) :
    (∫ x : ℝ in lower..upper,
      OriginalRieszSourceGreen.weightedRaw coordinate x+(1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x)=
    (upper:ℂ)*burnolRieszSingleFourierSourceRaw coordinate upper-
      (lower:ℂ)*burnolRieszSingleFourierSourceRaw coordinate lower := by
  have derivative (x : ℝ) (inside : x∈Icc lower upper) :
      HasDerivAt (fun y : ℝ=>(y:ℂ)*burnolRieszSingleFourierSourceRaw coordinate y)
        (OriginalRieszSourceGreen.weightedRaw coordinate x+(1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x) x := by
    have positive := lowerPositive.trans_le inside.1
    have actual := (Complex.ofRealCLM.hasDerivAt (x:=x)).mul
      (OriginalRieszSourceGreen.sourceRaw_hasDerivAt coordinate x positive.ne')
    convert! actual using 1
    change _=1*burnolRieszSingleFourierSourceRaw coordinate x+(x:ℂ)*OriginalRieszSourceGreen.sourceRawDerivative coordinate x
    rw [show (x:ℂ)*OriginalRieszSourceGreen.sourceRawDerivative coordinate x=
        OriginalRieszSourceGreen.weightedRaw coordinate x-(1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x by
          linear_combination OriginalRieszSourceGreen.sourceRaw_weighted_eq coordinate x positive.ne']
    ring
  have continuous : ContinuousOn (fun x : ℝ=>OriginalRieszSourceGreen.weightedRaw coordinate x+
      (1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x) (Icc lower upper) := by
    intro x inside
    exact ((source_weighted_continuous coordinate (lowerPositive.trans_le inside.1).ne').add
      (continuousAt_const.mul (burnolRieszSingleFourierSourceRaw_continuousAt coordinate
        (lowerPositive.trans_le inside.1).ne'))).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x inside=>derivative x (by simpa only [uIcc_of_le ordered] using inside))
    (continuous.intervalIntegrable_of_Icc ordered)

theorem original_response_band_action (coordinate : BurnolCompletedMellinCoordinate) (lower upper : ℝ)
    (lowerPositive : 0<lower) (ordered : lower≤upper) (upperQuarter : upper≤(1/4:ℝ)) :
    (∫ x : ℝ in lower..upper,contactResponse coordinate x)=
      (upper:ℂ)*burnolRieszSingleFourierSourceRaw coordinate upper-
      (lower:ℂ)*burnolRieszSingleFourierSourceRaw coordinate lower-
      star coordinate.value*(∫ x : ℝ in lower..upper,burnolRieszSingleFourierSourceRaw coordinate x)-
      Kernel.beta coordinate*(upper-lower:ℝ) := by
  have onQuarter : Icc lower upper⊆symmetricInterval (1/4:ℝ) := by
    intro x inside
    exact ⟨by linarith [inside.1],inside.2.trans upperQuarter⟩
  have raw (x : ℝ) (inside : x∈Icc lower upper) :=
    burnolRieszSingleFourierSourceRaw_continuousAt coordinate (lowerPositive.trans_le inside.1).ne'
  have rawContinuous : ContinuousOn (burnolRieszSingleFourierSourceRaw coordinate) (Icc lower upper) :=
    fun x inside=>(raw x inside).continuousWithinAt
  have weightedContinuous : ContinuousOn (OriginalRieszSourceGreen.weightedRaw coordinate) (Icc lower upper) :=
    fun x inside=>(source_weighted_continuous coordinate (lowerPositive.trans_le inside.1).ne').continuousWithinAt
  have rawIntegral := rawContinuous.intervalIntegrable_of_Icc ordered (μ:=volume)
  have weightedIntegral := weightedContinuous.intervalIntegrable_of_Icc ordered (μ:=volume)
  have source : (∫ x : ℝ in lower..upper,contactResponse coordinate x)=
      (∫ x : ℝ in lower..upper,OriginalRieszSourceGreen.weightedRaw coordinate x-Kernel.beta coordinate-
        (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp
      (original_contact_response_read coordinate)
    filter_upwards [ae_restrict_of_ae read,ae_restrict_mem measurableSet_uIoc] with x actual inside
    have bandInside : x∈Ioc lower upper := by simpa only [uIoc_of_le ordered] using inside
    exact actual (onQuarter ⟨bandInside.1.le,bandInside.2⟩)
  have flux := original_band_euler_flux coordinate lower upper lowerPositive ordered
  rw [intervalIntegral.integral_add weightedIntegral (rawIntegral.const_mul (1/2:ℂ)),intervalIntegral.integral_const_mul] at flux
  rw [source,intervalIntegral.integral_sub (weightedIntegral.sub intervalIntegrable_const)
      (rawIntegral.const_mul _),intervalIntegral.integral_sub weightedIntegral intervalIntegrable_const,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  linear_combination flux

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
