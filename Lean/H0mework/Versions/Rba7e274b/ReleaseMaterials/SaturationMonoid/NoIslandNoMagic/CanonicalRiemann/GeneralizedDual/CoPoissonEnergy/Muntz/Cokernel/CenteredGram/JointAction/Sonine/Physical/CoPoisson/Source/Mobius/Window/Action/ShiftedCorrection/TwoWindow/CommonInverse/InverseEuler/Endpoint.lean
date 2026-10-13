import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Action
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.Band
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.InverseEuler
open Complex Filter FourierTransform MeasureTheory Set OriginalRieszSource
open scoped ENNReal InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
local notation "q" => (1/4:ℝ)
local notation "μq" => volume.restrict (symmetricInterval q)
local notation "S" => burnolMeanZeroTruncatedFourier

def projectedRaw (raw : ℝ→ℂ) (continuous : Continuous raw) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (Constructor.compact raw continuous)
private theorem projectedRaw_add (f g : ℝ→ℂ) (hf : Continuous f) (hg : Continuous g) :
    projectedRaw (f+g) (hf.add hg)=projectedRaw f hf+projectedRaw g hg := by
  unfold projectedRaw
  rw [Constructor.compact_add f g hf hg,map_add]
private theorem projectedRaw_sub (f g : ℝ→ℂ) (hf : Continuous f) (hg : Continuous g) :
    projectedRaw (f-g) (hf.sub hg)=projectedRaw f hf-projectedRaw g hg := by
  unfold projectedRaw
  rw [Constructor.compact_sub f g hf hg,map_sub]
private theorem projectedRaw_smul (a : ℂ) (f : ℝ→ℂ) (hf : Continuous f) :
    projectedRaw (a • f) (hf.const_smul a)=a • projectedRaw f hf := by
  unfold projectedRaw
  rw [Constructor.compact_smul a f hf,map_smul]
private theorem projectedRaw_const (a : ℂ) :
    projectedRaw (fun _:ℝ=>a) continuous_const=0 := by
  have scalar:=projectedRaw_smul a (fun _:ℝ=>(1:ℂ)) continuous_const
  have one : projectedRaw (fun _:ℝ=>(1:ℂ)) continuous_const=0 := by
    unfold projectedRaw
    rw [Constructor.compact_one,Constructor.zeroMean_constant]
  rw [one,smul_zero] at scalar
  have same : Constructor.compact (fun _:ℝ=>a) continuous_const=
      Constructor.compact (a • (fun _:ℝ=>(1:ℂ))) (continuous_const.const_smul a) := by
    apply Lp.ext
    filter_upwards [Constructor.compact_read (fun _:ℝ=>a) continuous_const,
      Constructor.compact_read (a • (fun _:ℝ=>(1:ℂ))) (continuous_const.const_smul a)]
      with x left right
    rw [left,right]
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
  unfold projectedRaw at scalar ⊢
  rw [same]
  exact scalar

private theorem projectedRaw_congr (f g : ℝ→ℂ) (hf : Continuous f) (hg : Continuous g)
    (same : f=g) : projectedRaw f hf=projectedRaw g hg := by subst g; rfl
private theorem projectedRaw_state (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ→ℂ)
    (continuous : Continuous raw) (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) :
    projectedRaw raw continuous=state := by
  have actual : Constructor.compact raw continuous=(state:BurnolQuarterIntervalL2) := by
    apply Lp.ext
    exact (Constructor.compact_read raw continuous).trans read.symm
  unfold projectedRaw
  rw [actual]
  apply Subtype.ext
  rw [Constructor.zeroMean_read,Constructor.mean_zero,zero_smul,sub_zero]

def bandEndpointRaw (h scale : ℝ) (raw : ℝ→ℂ) (x : ℝ) : ℂ :=
  (Real.exp (scale/2):ℂ)/2*
    ((upperRadius h:ℂ)*raw (upperRadius h)*
      (Constructor.phase (upperRadius h) (Real.exp scale*x)+
        Constructor.phase (upperRadius h) (-(Real.exp scale*x)))-
     (lowerRadius h:ℂ)*raw (lowerRadius h)*
      (Constructor.phase (lowerRadius h) (Real.exp scale*x)+
        Constructor.phase (lowerRadius h) (-(Real.exp scale*x))))
theorem bandEndpointRaw_continuous (h scale : ℝ) (raw : ℝ→ℂ) :
    Continuous (bandEndpointRaw h scale raw) := by
  have plus:=Constructor.phaseContinuous (upperRadius h)
  have minus:=Constructor.phaseContinuous (lowerRadius h)
  unfold bandEndpointRaw
  fun_prop
theorem evenBandFourier_continuous (h scale : ℝ) (raw : ℝ→ℂ)
    (continuous : ContinuousOn raw (sourceBand h)) : Continuous (evenBandFourier h scale raw) :=
  continuous_iff_continuousAt.mpr fun x=>(evenBandFourier_hasDerivAt h scale raw continuous x).continuousAt

def bandEndpoint (h scale : ℝ) (raw : ℝ→ℂ) : BurnolQuarterMeanZeroCarrier :=
  projectedRaw (bandEndpointRaw h scale raw) (bandEndpointRaw_continuous h scale raw)
def forceBColumn (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier := projectedRaw (evenBandFourier h scale (forceBLeg coordinate leg))
      (evenBandFourier_continuous h scale _ (forceBLeg_continuous coordinate leg).continuousOn)
def forcePColumn (coordinate : BurnolCompletedMellinCoordinate) (h scale leg : ℝ) :
    BurnolQuarterMeanZeroCarrier := projectedRaw (evenBandFourier h scale (forcePLeg coordinate leg))
      (evenBandFourier_continuous h scale _ (forcePLeg_continuous coordinate leg).continuousOn)

theorem evenBand_source_euler (h scale : ℝ) (raw force : ℝ→ℂ) (weight : ℂ)
    (source : ∀ frequency:ℝ,
      (frequency:ℂ)*bandDerivative h raw frequency+(weight+1/2)*bandFourier h raw frequency+
        bandFourier h force frequency=
        (upperRadius h:ℂ)*Constructor.phase frequency (upperRadius h)*raw (upperRadius h)-
        (lowerRadius h:ℂ)*Constructor.phase frequency (lowerRadius h)*raw (lowerRadius h)) (x : ℝ) :
    (x:ℂ)*evenBandDerivative h scale raw x+(weight+1/2)*evenBandFourier h scale raw x+
      evenBandFourier h scale force x=bandEndpointRaw h scale raw x := by
  have plus:=source (Real.exp scale*x)
  have minus:=source (-(Real.exp scale*x))
  rw [Constructor.phase_symm (Real.exp scale*x) (upperRadius h),
    Constructor.phase_symm (Real.exp scale*x) (lowerRadius h)] at plus
  rw [Constructor.phase_symm (-(Real.exp scale*x)) (upperRadius h),
    Constructor.phase_symm (-(Real.exp scale*x)) (lowerRadius h)] at minus
  simp only [Complex.ofReal_mul,Complex.ofReal_neg] at plus minus
  unfold evenBandDerivative evenBandFourier bandEndpointRaw
  linear_combination ((Real.exp (scale/2):ℂ)/2)*plus+((Real.exp (scale/2):ℂ)/2)*minus

private theorem projected_cotest_action (state : BurnolQuarterMeanZeroCarrier) (raw derivative forcing boundary : ℝ→ℂ)
    (rawContinuous : Continuous raw) (derivativeContinuous : Continuous derivative)
    (forcingContinuous : Continuous forcing) (boundaryContinuous : Continuous boundary)
    (read : (state:BurnolQuarterIntervalL2)=ᵐ[μq] raw) (weight constant : ℂ)
    (action : ∀ x:ℝ,eulerRaw raw derivative x+weight*raw x=boundary x-forcing x-constant) :
    eulerState raw derivative rawContinuous derivativeContinuous+weight • state=
      projectedRaw boundary boundaryContinuous-projectedRaw forcing forcingContinuous := by
  let left:=eulerRaw raw derivative+weight • raw
  let right:=boundary-forcing-(fun _:ℝ=>constant)
  have leftContinuous : Continuous left := (eulerRaw_continuous _ _ rawContinuous derivativeContinuous).add
    (rawContinuous.const_smul weight)
  have rightContinuous : Continuous right := (boundaryContinuous.sub forcingContinuous).sub continuous_const
  have same : left=right := by funext x; exact action x
  have fields:=projectedRaw_congr left right leftContinuous rightContinuous same
  change projectedRaw (eulerRaw raw derivative+weight • raw) leftContinuous=
    projectedRaw (boundary-forcing-(fun _:ℝ=>constant)) rightContinuous at fields
  rw [projectedRaw_add _ _ (eulerRaw_continuous _ _ rawContinuous derivativeContinuous)
      (rawContinuous.const_smul weight),projectedRaw_smul weight raw rawContinuous,
    projectedRaw_sub _ _ (boundaryContinuous.sub forcingContinuous) continuous_const,
    projectedRaw_sub _ _ boundaryContinuous forcingContinuous,projectedRaw_const,sub_zero] at fields
  rw [projectedRaw_state state raw rawContinuous read] at fields
  exact fields

theorem source_b_cotest_action (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    bCotestEuler coordinate h scale leg+lambda coordinate • cotestColumn scale (bBand coordinate h leg)=
      bandEndpoint h scale (bLeg coordinate leg)-forceBColumn coordinate h scale leg := by
  apply projected_cotest_action _ _ _ _ _ (bCotestRaw_continuous coordinate h scale leg)
    (evenBandDerivative_continuous h scale _ (bLeg_continuousOn coordinate h leg))
    (evenBandFourier_continuous h scale _ (forceBLeg_continuous coordinate leg).continuousOn)
    (bandEndpointRaw_continuous h scale _) (bCotestRaw_read coordinate h scale leg nonnegative)
    (lambda coordinate) ((lambda coordinate+1/2)*cotestMean scale (bBand coordinate h leg))
  intro x
  have actual:=evenBand_source_euler h scale (bLeg coordinate leg) (forceBLeg coordinate leg)
    (lambda coordinate) (fun frequency=>b_band_source_euler coordinate h leg frequency nonnegative) x
  unfold eulerRaw bCotestRaw
  linear_combination actual

theorem source_p_cotest_action (coordinate : BurnolCompletedMellinCoordinate)
    (h scale leg : ℝ) (nonnegative : 0≤h) :
    pCotestEuler coordinate h scale leg+(-lambda coordinate) • cotestColumn scale (pBand coordinate h leg)=
      bandEndpoint h scale (pLeg coordinate leg)-forcePColumn coordinate h scale leg := by
  apply projected_cotest_action _ _ _ _ _ (pCotestRaw_continuous coordinate h scale leg)
    (evenBandDerivative_continuous h scale _ (pLeg_continuousOn coordinate h leg))
    (evenBandFourier_continuous h scale _ (forcePLeg_continuous coordinate leg).continuousOn)
    (bandEndpointRaw_continuous h scale _) (pCotestRaw_read coordinate h scale leg nonnegative)
    (-lambda coordinate) ((-lambda coordinate+1/2)*cotestMean scale (pBand coordinate h leg))
  intro x
  have actual:=evenBand_source_euler h scale (pLeg coordinate leg) (forcePLeg coordinate leg)
    (-lambda coordinate) (fun frequency=>p_band_source_euler coordinate h leg frequency nonnegative) x
  unfold eulerRaw pCotestRaw
  linear_combination actual

end OriginalCommonInverseForcing.InverseEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
