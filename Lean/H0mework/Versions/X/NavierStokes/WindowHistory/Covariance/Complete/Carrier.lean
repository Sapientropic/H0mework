import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Limit
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Budget
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCompleteCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}
def density (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp ℝ 1 (volume : Measure Torus) :=
  NativeWindowHistoryCovarianceLimit.value seed time

def weightedMeasure (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Measure Torus :=
  volume.withDensity (fun x => ENNReal.ofReal (density seed time x))

instance weightedFinite (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    IsFiniteMeasure (weightedMeasure seed time) :=
  isFiniteMeasure_withDensity_ofReal ((Lp.memLp (density seed time)).integrable le_rfl).2

abbrev Weighted (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :=
  Lp ℝ 2 (weightedMeasure seed time)

abbrev TestIndex := IntegerWavevector × Bool
abbrev Test := TestIndex →₀ ℝ

def component (imaginary : Bool) : ℂ →L[ℝ] ℝ := if imaginary then Complex.imCLM else Complex.reCLM

def character (index : TestIndex) : C(Torus,ℝ) :=
  (component index.2).compLeftContinuous ℝ Torus (UnitAddTorus.mFourier (-index.1))

def polynomial : Test →ₗ[ℝ] C(Torus,ℝ) := Finsupp.linearCombination ℝ character

def testMap (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Test →ₗ[ℝ] Weighted seed time :=
  (ContinuousMap.toLp 2 (weightedMeasure seed time) ℝ).toLinearMap.comp polynomial

def residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeCompleteStressCarrier.Space :=
  (NativeForwardWindowSource.source seed time).snd-
    NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst

def action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i : Coordinate) : Test →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun index => component index.2
    (NativeWindowHistoryCovarianceMetric.divergenceRead index.1 i (residual seed time)))


private def integrateAgainst (g : C(Torus,ℝ)) : Lp ℝ 1 (volume : Measure Torus) →L[ℝ] ℝ :=
  (L1.integralCLM' ℝ).comp ((innerSL ℝ (E := ℝ)).holderL volume ∞ 1 1
    ((ContinuousMap.toLp ∞ volume ℝ) g))

private theorem integrateAgainst_apply (g : C(Torus,ℝ)) (f : Lp ℝ 1 (volume : Measure Torus)) :
    integrateAgainst g f=∫x : Torus,g x*f x := by
  simp only [integrateAgainst,ContinuousLinearMap.comp_apply,ContinuousLinearMap.holderL_apply_apply,
    ← L1.integral_eq',L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [(innerSL ℝ (E := ℝ)).coeFn_holder (r := 1) ((ContinuousMap.toLp ∞ volume ℝ) g) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) (volume : Measure Torus) g] with x actual original
  rw [actual,original]
  change f x*g x=g x*f x
  ring

private theorem integrateAgainst_continuous (g f : C(Torus,ℝ)) :
    integrateAgainst g ((ContinuousMap.toLp 1 volume ℝ) f)=∫x : Torus,g x*f x := by
  rw [integrateAgainst_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus) f] with x same
  rw [same]

private theorem character_pair (f : C(Torus,ℝ)) (index : TestIndex) :
    (∫x : Torus,character index x*f x)=
      component index.2 (NativeWindowFiniteGramFourier.fourierRead index.1 f) := by
  have regular : Integrable (fun x : Torus => UnitAddTorus.mFourier (-index.1) x*(f x : ℂ)) :=
    ((UnitAddTorus.mFourier (-index.1)).continuous.mul
      (Complex.continuous_ofReal.comp f.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [NativeWindowFiniteGramFourier.fourierRead_apply,UnitAddTorus.mFourierCoeff]
  change (∫x : Torus,character index x*f x)=component index.2
    (∫x : Torus,UnitAddTorus.mFourier (-index.1) x*(f x : ℂ))
  rw [← (component index.2).integral_comp_comm regular]
  apply integral_congr_ae
  filter_upwards with x
  change component index.2 (UnitAddTorus.mFourier (-index.1) x)*f x=_
  rw [mul_comm (UnitAddTorus.mFourier (-index.1) x),← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

private theorem polynomial_pair (f : C(Torus,ℝ)) (c : Test) :
    (∫x : Torus,polynomial c x*f x)=c.sum (fun index a => a*component index.2
      (NativeWindowFiniteGramFourier.fourierRead index.1 f)) := by
  have regular (index : TestIndex) : Integrable (fun x : Torus => character index x*f x) :=
    ((character index).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [polynomial,Finsupp.linearCombination_apply,Finsupp.sum,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum c.support (fun index _ => (regular index).const_mul (c index))]
  simp_rw [integral_const_mul,character_pair]

theorem finite_action_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (i : Coordinate) (c : Test) :
    Tendsto (fun M => ∫x : Torus,polynomial c x*NativeWindowHistoryCovarianceMetric.momentum seed M time i x)
      atTop (𝓝 (action seed time i c)) := by
  simp only [polynomial_pair,action,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul]
  apply tendsto_finsetSum
  intro index _
  have original:=NativeWindowHistoryCovarianceMetric.momentum_tendsto seed time index.1 i
  rw [← NativeWindowHistoryCovarianceMetric.divergenceRead_apply] at original
  exact ((component index.2).continuous.tendsto _ |>.comp original).const_mul (c index)

theorem density_square_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (g : C(Torus,ℝ)) :
    Tendsto (fun M => ∫x : Torus,NativeWindowHistoryCovarianceCurrent.value seed M time x*(g x)^2)
      atTop (𝓝 (∫x : Torus,density seed time x*(g x)^2)) := by
  have original:=(integrateAgainst (g*g)).continuous.tendsto _ |>.comp
    (NativeWindowHistoryCovarianceLimit.source_tendsto seed time)
  have finite (M : ℕ) : integrateAgainst (g*g) ((ContinuousMap.toLp 1 volume ℝ)
      (NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0))=
      ∫x : Torus,NativeWindowHistoryCovarianceCurrent.value seed M time x*(g x)^2 := by
    rw [integrateAgainst_continuous]
    apply integral_congr_ae
    filter_upwards with x
    have read:=NativeWindowAbsoluteTimePhysicalCurrent.current_read seed M time 0 x
    have real:=congrArg Complex.re read
    change NativeWindowHistoryCovarianceCurrent.value seed M time x=
      NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0 x at real
    rw [real]
    change (g x*g x)*_= _*(g x)^2
    ring
  have complete : integrateAgainst (g*g) (density seed time)=∫x : Torus,density seed time x*(g x)^2 := by
    rw [integrateAgainst_apply]
    apply integral_congr_ae
    filter_upwards with x
    change (g x*g x)*_=_*(g x)^2
    ring
  change Tendsto _ atTop (𝓝 (integrateAgainst (g*g) (density seed time))) at original
  simpa only [Function.comp_def,finite,complete] using original

theorem weighted_square (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (c : Test) :
    ‖testMap seed time c‖^2=∫x : Torus,density seed time x*(polynomial c x)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have actual : (fun x => (testMap seed time c x)^2)=ᵐ[weightedMeasure seed time]
      (fun x => (polynomial c x)^2) := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (weightedMeasure seed time) (polynomial c)] with x same
    exact congrArg (fun a : ℝ => a^2) same
  rw [integral_congr_ae actual]
  rw [weightedMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (Lp.memLp (density seed time)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryCovarianceLimit.source_lower seed time] with x lower
  change 2 ≤ density seed time x at lower
  rw [ENNReal.toReal_ofReal (show 0 ≤ density seed time x by linarith only [lower]),smul_eq_mul]

end
end SaturationMonoid.NavierStokes.NativeCompleteCovariance
