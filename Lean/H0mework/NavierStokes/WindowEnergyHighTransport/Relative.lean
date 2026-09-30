import H0mework.NavierStokes.WindowEnergyHighTransport.Resolvent
import H0mework.NavierStokes.WindowEnergyHighTransport.Work

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportRelative
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalGradient NativeWindowHighTransportResolvent
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def fieldCLM : ScalarSequence →L[ℝ] ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

def primitiveField (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField := fieldCLM (primitive seed F radius order time output input)

theorem primitiveField_norm (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : ‖primitiveField seed F radius order time output input‖=
      ‖primitive seed F radius order time output input‖ := (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.norm_map _

theorem primitiveField_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (output input : Coordinate) : HasDerivAt (fun t => primitiveField seed F radius order t output input)
      (primitiveField seed F radius (order+1) time output input) time :=
  fieldCLM.hasFDerivAt.comp_hasDerivAt time (primitive_hasDerivAt seed F radius order time output input)

theorem primitive_viscous_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) (k : IntegerWavevector) :
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • UnitAddTorus.mFourierCoeff
      (primitiveField seed F radius 0 time output input) k =
    ∑ j : Coordinate,multiplier k j*NativeWindowFiniteGramFourier.fourierRead k
      (NativeWindowHighTransportWork.physicalCurrent seed time F
        (F∩ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes radius) j output input) := by
  have original := viscous_row nu (NativeWindowHighTransportSource.window seed F radius 0 time) output input k
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) • UnitAddTorus.mFourierCoeff
    (NativeWindowStressHeatEnergy.field (primitive seed F radius 0 time output input)) k=_
  rw [NativeWindowStressHeatEnergy.field_fourier]
  change (nu.coeff*integerWaveViscousMultiplier k : ℝ) • resolve nu output input
    (NativeWindowHighTransportSource.window seed F radius 0 time) k=_
  rw [original]
  apply Finset.sum_congr rfl
  intro j _
  rw [← NativeWindowHighTransportWork.physicalCurrent_fourier seed time nonnegative F radius closed j output input k]
  have inverse : ((NativeUnheatedSexticLatticePower.radical k^2 : ℝ) : ℂ)*
      (NativeUnheatedSexticLatticePower.density 2 k : ℂ)=1 := by
    rw [← Complex.ofReal_mul]
    norm_cast
    exact mul_inv_cancel₀ (pow_ne_zero 2 (NativeUnheatedSexticLatticePower.radical_positive k).ne')
  rw [mul_assoc (multiplier k j),← mul_assoc (((NativeUnheatedSexticLatticePower.radical k^2 : ℝ) : ℂ)),inverse,one_mul]

def relative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatBalance.sigma seed F output input time-primitiveField seed F radius 0 time output input

def rate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  NativeWindowStressHeatSource.physical (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input)+
  NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input)-
  primitiveField seed F radius 1 time output input

theorem relative_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (fun t => relative seed F radius t output input) (rate seed F radius time output input) time :=
  (NativeWindowStressHeatBalance.sigma_hasDerivAt seed time nonnegative F closed output input).sub
    (primitiveField_hasDerivAt seed F radius 0 time output input)

def energy (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,(1/2 : ℝ)*‖relative seed F radius time output input‖^2

def timeWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (primitiveField seed F radius 1 time output input)

def forcingWork (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ (relative seed F radius time output input)
    (NativeWindowStressHeatSource.physical (NativeWindowStressHeatBalance.nonlinearWindow seed time F output input)+
      NativeWindowStressHeatSource.physical (NativeWindowStressHeatSource.heat seed time F output input))

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) :
    HasDerivAt (energy seed F radius) (forcingWork seed F radius time-timeWork seed F radius time) time := by
  have row (output input : Coordinate) := ((relative_hasDerivAt seed F radius time nonnegative closed output input).norm_sq).const_mul (1/2 : ℝ)
  have actual := HasDerivAt.sum (u := Finset.univ) fun output _ => HasDerivAt.sum (u := Finset.univ) fun input _ => row output input
  convert! actual using 1
  simp only [rate,forcingWork,timeWork,inner_sub_right]
  simp_rw [show ∀ x : ℝ,(1/2 : ℝ)*(2*x)=x from fun x => by ring]
  simp only [Finset.sum_sub_distrib]

theorem timeWork_bound (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    |timeWork seed F radius time|≤energy seed F radius time+
      ∑ output : Coordinate,∑ input : Coordinate,(1/2 : ℝ)*‖primitiveField seed F radius 1 time output input‖^2 := by
  unfold timeWork energy
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun output _ => Finset.abs_sum_le_sum_abs _ _)).trans
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro input _
  have cauchy := abs_real_inner_le_norm (relative seed F radius time output input) (primitiveField seed F radius 1 time output input)
  nlinarith only [cauchy,sq_nonneg (‖relative seed F radius time output input‖-‖primitiveField seed F radius 1 time output input‖)]

theorem timeWork_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      |timeWork seed F radius time|≤energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := primitive_small seed 1 horizon nonnegative (Real.sqrt (2*epsilon/9)) (by positivity)
  refine ⟨low,fun radius above F time inside => (timeWork_bound seed F radius time).trans ?_⟩
  apply add_le_add_right
  have row (output input : Coordinate) : (1/2 : ℝ)*‖primitiveField seed F radius 1 time output input‖^2≤epsilon/9 := by
    rw [primitiveField_norm]
    have paid := pow_le_pow_left₀ (norm_nonneg _) (small radius above F time inside output input).le 2
    rw [Real.sq_sqrt (by positivity : 0≤2*epsilon/9)] at paid
    linarith
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)


def rawRate (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  -NativeWindowStressHeatSource.physical (NativeWindowStressHeatTime.jet seed F output input 1 time)-
    primitiveField seed F radius 1 time output input

theorem rate_original (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (closed : ∀ k,k∈F →waveNeg k∈F) (output input : Coordinate) :
    rate seed F radius time output input=rawRate seed F radius time output input := by
  have same := congrArg NativeWindowStressHeatSource.physical
    (NativeWindowStressHeatBalance.jet_generator seed time nonnegative F closed output input)
  simp only [map_neg,map_add] at same
  exact congrArg (fun value => value-primitiveField seed F radius 1 time output input) same.symm

theorem relative_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) :
    HasDerivAt (fun t => relative seed F radius t output input) (rawRate seed F radius time output input) time := by
  have actual := ((NativeWindowStressHeatSource.physical.hasFDerivAt.comp_hasDerivAt time
    (NativeWindowStressHeatTime.jet_hasDerivAt seed F output input 0 time)).neg).sub
      (primitiveField_hasDerivAt seed F radius 0 time output input)
  simpa only [relative,rawRate,NativeWindowStressHeatBalance.sigma,NativeWindowStressHeatTime.jet_zero,
    Function.comp_def,Pi.sub_apply,Pi.neg_apply] using! actual

theorem rawRate_continuous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (output input : Coordinate) : Continuous (fun t => rawRate seed F radius t output input) := by
  have first := (NativeWindowStressHeatSource.physical.continuous.comp (continuous_iff_continuousAt.mpr
    (fun time => (NativeWindowStressHeatTime.jet_hasDerivAt seed F output input 1 time).continuousAt))).neg
  have last := continuous_iff_continuousAt.mpr (fun time => (primitiveField_hasDerivAt seed F radius 1 time output input).continuousAt)
  exact first.sub last

theorem relative_write (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (closed : ∀ k,k∈F →waveNeg k∈F) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) (output input : Coordinate) :
    relative seed F radius b output input-relative seed F radius a output input=
      ∫ time in a..b,rate seed F radius time output input := by
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ => relative_derivative seed F radius time output input)
    ((rawRate_continuous seed F radius output input).intervalIntegrable a b)
  refine actual.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro time inside
  exact (rate_original seed F radius time ((le_min a0 b0).trans inside.1) closed output input).symm

theorem original_energy_le (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    NativeWindowStressHeatBalance.energy seed F time≤2*energy seed F radius time+
      ∑ output : Coordinate,∑ input : Coordinate,‖primitiveField seed F radius 0 time output input‖^2 := by
  simp only [NativeWindowStressHeatBalance.energy,energy,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  apply Finset.sum_le_sum
  intro input _
  have source : NativeWindowStressHeatBalance.sigma seed F output input time=
      relative seed F radius time output input+primitiveField seed F radius 0 time output input := by unfold relative; abel
  rw [source]
  have triangle := norm_add_le (relative seed F radius time output input) (primitiveField seed F radius 0 time output input)
  have paid := pow_le_pow_left₀ (norm_nonneg _) triangle 2
  nlinarith only [paid,sq_nonneg (‖relative seed F radius time output input‖-‖primitiveField seed F radius 0 time output input‖)]

theorem original_energy_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F time,time∈Icc 0 horizon →
      NativeWindowStressHeatBalance.energy seed F time≤2*energy seed F radius time+epsilon := by
  obtain ⟨low,small⟩ := primitive_small seed 0 horizon nonnegative (Real.sqrt (epsilon/9)) (by positivity)
  refine ⟨low,fun radius above F time inside => (original_energy_le seed F radius time).trans ?_⟩
  apply add_le_add_right
  have row (output input : Coordinate) : ‖primitiveField seed F radius 0 time output input‖^2≤epsilon/9 := by
    rw [primitiveField_norm]
    have paid := pow_le_pow_left₀ (norm_nonneg _) (small radius above F time inside output input).le 2
    simpa only [Real.sq_sqrt (by positivity : 0≤epsilon/9)] using paid
  exact (Finset.sum_le_sum (fun output _ => Finset.sum_le_sum (fun input _ => row output input))).trans_eq (by simp; ring)


def primitiveViscous (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : ScalarField :=
  fieldCLM (NativeWindowStressHeatEnergy.finiteSequence (F+(F+F)) (fun k =>
    (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F radius 0 time output input k))

theorem primitiveViscous_fourier (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) (k : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (primitiveViscous seed F radius time output input) k=
      (nu.coeff*integerWaveViscousMultiplier k : ℝ) • primitive seed F radius 0 time output input k := by
  change UnitAddTorus.mFourierCoeff (NativeWindowStressHeatEnergy.field _) k=_
  rw [NativeWindowStressHeatEnergy.field_fourier,NativeWindowStressHeatEnergy.finiteSequence_apply]
  split_ifs with inside
  · rfl
  · rw [primitive_supported seed F radius 0 time output input k inside,smul_zero]


theorem relative_mean (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (output input : Coordinate) : UnitAddTorus.mFourierCoeff (relative seed F radius time output input) 0=
      UnitAddTorus.mFourierCoeff (NativeWindowStressHeatBalance.sigma seed F output input time) 0 := by
  simp only [← UnitAddTorus.mFourierBasis_repr,relative,map_sub,lp.coeFn_sub,Pi.sub_apply]
  change _-((UnitAddTorus.mFourierBasis (d := Coordinate)).repr
    (NativeWindowStressHeatEnergy.field (primitive seed F radius 0 time output input))) 0=_
  have inverse : (UnitAddTorus.mFourierBasis (d := Coordinate)).repr
      (NativeWindowStressHeatEnergy.field (primitive seed F radius 0 time output input))=
        primitive seed F radius 0 time output input := (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.apply_symm_apply _
  rw [inverse,primitive_zero,sub_zero]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportRelative
