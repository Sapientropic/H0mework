import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.BandEuler
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Eta
import Mathlib.Analysis.Calculus.Deriv.Star
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

def sourceCotest (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (x : ℝ) : ℂ :=
  star (burnolRieszSingleFourierSourceRaw coordinate (scale*x))
def sourceCotestDerivative (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (x : ℝ) : ℂ :=
  (scale:ℂ)*star (OriginalRieszSourceGreen.sourceRawDerivative coordinate (scale*x))

theorem actual_cotest_derivative (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (scalePositive : 0<scale)
    (x : ℝ) (xPositive : 0<x) :
    HasDerivAt (sourceCotest coordinate scale) (sourceCotestDerivative coordinate scale x) x := by
  have scaling : HasDerivAt (fun y : ℝ=>scale*y) scale x := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul scale
  have generated := ((OriginalRieszSourceGreen.sourceRaw_hasDerivAt coordinate (scale*x)
    (mul_pos scalePositive xPositive).ne').scomp x scaling).star
  change HasDerivAt (sourceCotest coordinate scale)
    (star (scale • OriginalRieszSourceGreen.sourceRawDerivative coordinate (scale*x))) x at generated
  simpa only [sourceCotestDerivative,Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal,mul_comm] using generated

 theorem actual_cotest_band_response (coordinate : BurnolCompletedMellinCoordinate) (scale : ℝ) (scalePositive : 0<scale)
    (lower upper : ℝ) (lowerPositive : 0<lower) (ordered : lower≤upper) (upperQuarter : upper≤(1/4:ℝ)) :
    (∫ x : ℝ in lower..upper,sourceCotest coordinate scale x*contactResponse coordinate x)=
      sourceCotest coordinate scale upper*(upper:ℂ)*burnolRieszSingleFourierSourceRaw coordinate upper-
      sourceCotest coordinate scale lower*(lower:ℂ)*burnolRieszSingleFourierSourceRaw coordinate lower-
      (∫ x : ℝ in lower..upper,
        ((x:ℂ)*sourceCotestDerivative coordinate scale x+star coordinate.value*sourceCotest coordinate scale x)*
          burnolRieszSingleFourierSourceRaw coordinate x)-
      Kernel.beta coordinate*(∫ x : ℝ in lower..upper,sourceCotest coordinate scale x) := by
  have pointDerivative (x : ℝ) (inside : x∈Icc lower upper) :
      HasDerivAt (fun y : ℝ=>sourceCotest coordinate scale y*(y:ℂ)*burnolRieszSingleFourierSourceRaw coordinate y)
        (sourceCotest coordinate scale x*(OriginalRieszSourceGreen.weightedRaw coordinate x+
          (1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x)+
          (x:ℂ)*sourceCotestDerivative coordinate scale x*burnolRieszSingleFourierSourceRaw coordinate x) x := by
    have positive := lowerPositive.trans_le inside.1
    have actual := ((actual_cotest_derivative coordinate scale scalePositive x positive).mul
      (Complex.ofRealCLM.hasDerivAt (x:=x))).mul
      (OriginalRieszSourceGreen.sourceRaw_hasDerivAt coordinate x positive.ne')
    convert! actual using 1
    change _=(sourceCotestDerivative coordinate scale x*(x:ℂ)+sourceCotest coordinate scale x*1)*
      burnolRieszSingleFourierSourceRaw coordinate x+
      (sourceCotest coordinate scale x*(x:ℂ))*OriginalRieszSourceGreen.sourceRawDerivative coordinate x
    have euler := OriginalRieszSourceGreen.sourceRaw_weighted_eq coordinate x positive.ne'
    linear_combination -(sourceCotest coordinate scale x)*euler
  have rawContinuous : ContinuousOn (burnolRieszSingleFourierSourceRaw coordinate) (Icc lower upper) :=
    fun x inside=>(burnolRieszSingleFourierSourceRaw_continuousAt coordinate
      (lowerPositive.trans_le inside.1).ne').continuousWithinAt
  have cotestContinuous : ContinuousOn (sourceCotest coordinate scale) (Icc lower upper) :=
    fun x inside=>(actual_cotest_derivative coordinate scale scalePositive x
      (lowerPositive.trans_le inside.1)).continuousAt.continuousWithinAt
  have weightedContinuous : ContinuousOn (OriginalRieszSourceGreen.weightedRaw coordinate) (Icc lower upper) :=
    fun x inside=>(source_weighted_continuous coordinate (lowerPositive.trans_le inside.1).ne').continuousWithinAt
  have derivativeContinuous : ContinuousOn (sourceCotestDerivative coordinate scale) (Icc lower upper) := by
    intro x inside
    have positive := lowerPositive.trans_le inside.1
    unfold sourceCotestDerivative OriginalRieszSourceGreen.sourceRawDerivative
    have scaling : ContinuousAt (fun y : ℝ=>scale*y) x := (continuous_const.mul continuous_id).continuousAt
    have actual := Translator.ForcingWhole.raw_continuousAt coordinate (mul_pos scalePositive positive).ne'
    have moved := actual.comp scaling
    have edge := (Edge.raw_continuous (1/4:ℝ)).continuousAt.comp scaling
    have returned := (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate)).continuousAt.comp scaling
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul
      (((((continuousAt_const.mul moved).add (continuousAt_const.mul edge)).div
        (Complex.continuous_ofReal.continuousAt.comp scaling)
        (Complex.ofReal_ne_zero.mpr (mul_pos scalePositive positive).ne')).add returned).star)
  have sourceRaw (x : ℝ) (inside : x∈Icc lower upper) := pointDerivative x inside
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x inside=>sourceRaw x (by simpa only [uIcc_of_le ordered] using inside))
    (((cotestContinuous.mul (weightedContinuous.add (continuousOn_const.mul rawContinuous))).add
      ((Complex.continuous_ofReal.continuousOn.mul derivativeContinuous).mul rawContinuous)).intervalIntegrable_of_Icc ordered)
  have onQuarter : Icc lower upper⊆symmetricInterval (1/4:ℝ) := by
    intro x inside
    exact ⟨by linarith [inside.1],inside.2.trans upperQuarter⟩
  have source : (∫ x : ℝ in lower..upper,sourceCotest coordinate scale x*contactResponse coordinate x)=
      (∫ x : ℝ in lower..upper,sourceCotest coordinate scale x*(OriginalRieszSourceGreen.weightedRaw coordinate x-
        Kernel.beta coordinate-(star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (original_contact_response_read coordinate)
    filter_upwards [ae_restrict_of_ae read,ae_restrict_mem measurableSet_uIoc] with x actual inside
    have bandInside : x∈Ioc lower upper := by simpa only [uIoc_of_le ordered] using inside
    rw [actual (onQuarter ⟨bandInside.1.le,bandInside.2⟩)]
  have pointSplit : (fun x : ℝ=>sourceCotest coordinate scale x*(OriginalRieszSourceGreen.weightedRaw coordinate x-
      Kernel.beta coordinate-(star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x))=
    fun x =>(sourceCotest coordinate scale x*(OriginalRieszSourceGreen.weightedRaw coordinate x+
        (1/2:ℂ)*burnolRieszSingleFourierSourceRaw coordinate x)+
        (x:ℂ)*sourceCotestDerivative coordinate scale x*burnolRieszSingleFourierSourceRaw coordinate x)-
      (((x:ℂ)*sourceCotestDerivative coordinate scale x+star coordinate.value*sourceCotest coordinate scale x)*
        burnolRieszSingleFourierSourceRaw coordinate x)-Kernel.beta coordinate*sourceCotest coordinate scale x := by
    funext x
    ring
  rw [source,pointSplit,intervalIntegral.integral_sub,intervalIntegral.integral_sub,integrated,
    intervalIntegral.integral_const_mul]
  all_goals first | rfl | exact ContinuousOn.intervalIntegrable_of_Icc ordered (by fun_prop)

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
