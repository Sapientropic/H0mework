import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.PairPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalTwoWindowInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)

def lambda (coordinate : BurnolCompletedMellinCoordinate) : ℂ := star coordinate.value-1/2
def sourceMean (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolTruncatedFourier
    (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))
def rawFourier (state : BurnolQuarterMeanZeroCarrier) (x : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw q (state:BurnolQuarterIntervalL2) x
def responseU (x : ℝ) : ℂ := rawFourier Response.u x
def responseV (x : ℝ) : ℂ := rawFourier Response.v x+Edge.raw q x
def forceB (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.A coordinate*responseV x-Kernel.beta coordinate*responseU x+
    (star coordinate.value-1)*(Translator.ForcingMeanZero.mean coordinate+
      OriginalInverseReturnActionSource.returnMean coordinate)
def forceP (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.A coordinate*responseU x-Kernel.beta coordinate*responseV x+
    star coordinate.value*(sourceMean coordinate-GapEuler.gapMean q coordinate)

theorem rawFourier_add (left right : BurnolQuarterMeanZeroCarrier) (x : ℝ) :
    rawFourier (left+right) x=rawFourier left x+rawFourier right x := by
  exact congrFun (burnolRadiusTruncatedFourierRaw_add (left:BurnolQuarterIntervalL2)
    (right:BurnolQuarterIntervalL2)) x
theorem rawFourier_smul (scalar : ℂ) (state : BurnolQuarterMeanZeroCarrier) (x : ℝ) :
    rawFourier (scalar•state) x=scalar*rawFourier state x := by
  exact congrFun (burnolRadiusTruncatedFourierRaw_smul scalar (state:BurnolQuarterIntervalL2)) x
theorem rawFourier_sub (left right : BurnolQuarterMeanZeroCarrier) (x : ℝ) :
    rawFourier (left-right) x=rawFourier left x-rawFourier right x := by
  rw [sub_eq_add_neg,rawFourier_add,← neg_one_smul ℂ right,rawFourier_smul]
  ring

theorem source_full_fourier (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    rawFourier (burnolRieszSingleFourierSource coordinate) x=
      burnolRieszReturnRaw coordinate x+sourceMean coordinate := by
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw sourceMean rawFourier
  ring
theorem return_full_fourier (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    rawFourier (Constructor.returnState coordinate) x=
      OriginalInverseReturnActionSource.fullInverseReturnProfile coordinate x := by
  have same:=congrFun (Constructor.fourierRaw_congr _ _ (Constructor.returnState_read coordinate)) x
  rw [Constructor.fourierRaw_state] at same
  exact same.trans (OriginalInverseReturnActionSource.original_inverse_return_profile coordinate x)

theorem source_euler_full_fourier (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    rawFourier (Euler.sourceEuler coordinate) x=
      lambda coordinate*rawFourier (burnolRieszSingleFourierSource coordinate) x+
      Kernel.A coordinate*responseU x-Kernel.beta coordinate*rawFourier Response.v x := by
  rw [Euler.sourceEuler_eq,rawFourier_sub,rawFourier_add,rawFourier_smul,rawFourier_smul,rawFourier_smul]
  rfl
theorem return_euler_full_fourier (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    rawFourier (Constructor.returnEuler coordinate) x=
      -lambda coordinate*rawFourier (Constructor.returnState coordinate) x-
      Kernel.A coordinate*rawFourier Response.v x+Kernel.beta coordinate*responseU x := by
  rw [Euler.returnEuler_eq,rawFourier_add,rawFourier_sub,rawFourier_smul,rawFourier_smul,rawFourier_smul]
  rfl

theorem return_raw_euler_fourier (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Constructor.fourierRaw (Constructor.returnEulerRaw coordinate) x=
      rawFourier (Constructor.returnEuler coordinate) x+
      burnolRieszReturnRaw coordinate q*burnolRadiusTruncatedFourierRaw q (intervalConstant q) x := by
  have mean:=Constructor.returnEulerAmbient_mean coordinate
  have endpoints : burnolRieszReturnRaw coordinate (-q)=burnolRieszReturnRaw coordinate q :=
    burnolRieszSingleFourierReturnRaw_endpoints coordinate
  rw [endpoints] at mean
  have meanValue : burnolQuarterMeanCoefficient (Constructor.returnEulerAmbient coordinate)=
      burnolRieszReturnRaw coordinate q := mean.trans (by ring)
  have original:=Constructor.zeroMean_read (Constructor.returnEulerAmbient coordinate)
  change (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)=_ at original
  rw [meanValue] at original
  have split : Constructor.returnEulerAmbient coordinate=
      (Constructor.returnEuler coordinate:BurnolQuarterIntervalL2)+
        burnolRieszReturnRaw coordinate q•intervalConstant q := by
    rw [original]
    module
  have same:=congrFun (Constructor.fourierRaw_congr _ _
    (Constructor.compact_read _ (Constructor.returnEulerRaw_continuous coordinate))) x
  rw [Constructor.fourierRaw_state] at same
  rw [← same]
  change burnolRadiusTruncatedFourierRaw q (Constructor.returnEulerAmbient coordinate) x=_
  rw [split,burnolRadiusTruncatedFourierRaw_add,burnolRadiusTruncatedFourierRaw_smul]
  rfl

-- The Fourier kernel laws hold at every frequency, including the exterior moving leg.
theorem original_return_euler (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    Constructor.returnEulerRaw coordinate x=
      -lambda coordinate*burnolRieszReturnRaw coordinate x-
        Kernel.A coordinate*responseU x+Kernel.beta coordinate*responseV x-
        star coordinate.value*sourceMean coordinate := by
  have source:=Euler.source_kernel_ward coordinate (Euler.sourceEuler coordinate)
    (Euler.source_euler coordinate) x
  change (x:ℂ)*burnolRieszReturnRawDerivative coordinate x+
    (1/2:ℂ)*rawFourier (burnolRieszSingleFourierSource coordinate) x+
    rawFourier (Euler.sourceEuler coordinate) x=Kernel.beta coordinate*Edge.raw q x at source
  rw [source_euler_full_fourier,source_full_fourier] at source
  unfold Constructor.returnEulerRaw responseV lambda at *
  linear_combination source

theorem original_source_euler (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    OriginalRieszSourceGreen.weightedRaw coordinate x=
      lambda coordinate*burnolRieszSingleFourierSourceRaw coordinate x+forceB coordinate x := by
  have source:=Constructor.return_ward_fourier_source coordinate x
  rw [return_raw_euler_fourier,return_euler_full_fourier,return_full_fourier] at source
  have inverse:=OriginalInverseReturnActionSource.original_inverse_return_profile coordinate x
  have second:=congrFun (Constructor.secondReturnRaw_eq_fourier coordinate) x
  rw [inverse] at source second
  rw [OriginalRieszSourceGreen.weightedRaw_eq]
  unfold Constructor.secondEulerRaw
  rw [second]
  unfold forceB lambda responseV Kernel.A OriginalInverseReturnActionSource.fullInverseReturnProfile
    OriginalInverseReturnActionSource.returnMean at *
  have endpoints : burnolRieszReturnRaw coordinate (-q)=burnolRieszReturnRaw coordinate q :=
    burnolRieszSingleFourierReturnRaw_endpoints coordinate
  rw [endpoints] at source
  rw [Edge.raw_apply]
  linear_combination source

end OriginalTwoWindowInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
