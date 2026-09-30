import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.PhysicalCompletion

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalStress
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_closed)
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (Fiber Space physical field)
open NativeWindowAbsoluteTimeSource (history)
open NativeWindowAbsoluteTimePhysicalCompletion (synthesis)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance fiberSeminormed : SeminormedAddCommGroup Fiber :=
  (inferInstance : NormedAddCommGroup Fiber).toSeminormedAddCommGroup
local instance spaceSeminormed : SeminormedAddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toSeminormedAddCommGroup
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {nu : Viscosity}

abbrev Density := Lp ℝ 1 (volume : Measure Torus)

def pair : Space →L[ℝ] Space →L[ℝ] Density := (innerSL ℝ (E := Fiber)).holderL volume 2 2 1

theorem pair_ae (u v : Space) : pair u v=ᵐ[volume] fun x => inner ℝ (u x) (v x) :=
  (innerSL ℝ (E := Fiber)).coeFn_holder u v

theorem real_pair (u v : Fiber) : inner ℝ u v=(inner ℂ u v).re := by
  have first:=norm_add_sq_real u v
  have last:=norm_add_sq (𝕜 := ℂ) u v
  change ‖u+v‖^2=‖u‖^2+2*(inner ℂ u v).re+‖v‖^2 at last
  linarith only [first,last]

def stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) : Density :=
  -pair (synthesis i (history seed time)) (synthesis j (history seed time))

theorem stress_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) :
    stress seed time i j=ᵐ[volume] fun x =>
      -inner ℝ (synthesis i (history seed time) x) (synthesis j (history seed time) x) := by
  filter_upwards [Lp.coeFn_neg (pair (synthesis i (history seed time)) (synthesis j (history seed time))),
    pair_ae (synthesis i (history seed time)) (synthesis j (history seed time))] with x neg same
  exact neg.trans (congrArg Neg.neg same)

theorem finite_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i j : Coordinate) :
    pair (physical (modes M) i (history seed time)) (physical (modes M) j (history seed time))=
      (ContinuousMap.toLp 1 volume ℝ) (NativeWindowFiniteGramFourier.stress seed time (modes M) i j) := by
  apply Lp.ext
  filter_upwards [pair_ae (physical (modes M) i (history seed time)) (physical (modes M) j (history seed time)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (field (modes M) i (history seed time)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus) (field (modes M) j (history seed time)),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus)
      (NativeWindowFiniteGramFourier.stress seed time (modes M) i j)] with x actual first last target
  rw [actual,show physical (modes M) i (history seed time) x=_ from first,
    show physical (modes M) j (history seed time) x=_ from last,target]
  have original:=congrArg Complex.re
    (NativeWindowAbsoluteTimePhysicalRead.source_pair seed (modes M) (modes_closed M) time i j x)
  simpa only [real_pair,Complex.ofReal_re] using original

theorem stress_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) :
    Tendsto (fun M => -(ContinuousMap.toLp 1 volume ℝ)
      (NativeWindowFiniteGramFourier.stress seed time (modes M) i j)) atTop (𝓝 (stress seed time i j)) := by
  have continuity : Continuous (fun p : Space × Space => pair p.1 p.2) :=
    (pair.continuous.comp continuous_fst).clm_apply continuous_snd
  have both:=continuity.tendsto (synthesis i (history seed time),synthesis j (history seed time)) |>.comp
    ((NativeWindowAbsoluteTimePhysicalCompletion.source_tendsto seed time i).prodMk_nhds
      (NativeWindowAbsoluteTimePhysicalCompletion.source_tendsto seed time j))
  simpa only [Function.comp_def,finite_pair,stress] using! both.neg

def phase (k : IntegerWavevector) : Lp ℂ ∞ (volume : Measure Torus) :=
  (ContinuousMap.toLp ∞ volume ℂ) (UnitAddTorus.mFourier (-k))

def scalar : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).flip

def fourier (k : IntegerWavevector) : Density →L[ℝ] ℂ :=
  (L1.integralCLM' ℝ).comp (scalar.holderL volume ∞ 1 1 (phase k))

theorem fourier_integral (k : IntegerWavevector) (v : Density) :
    fourier k v=UnitAddTorus.mFourierCoeff (fun x => (v x : ℂ)) k := by
  simp only [fourier,ContinuousLinearMap.comp_apply,ContinuousLinearMap.holderL_apply_apply,
    ← L1.integral_eq',L1.integral_eq_integral]
  rw [UnitAddTorus.mFourierCoeff]
  apply integral_congr_ae
  filter_upwards [scalar.coeFn_holder (r := 1) (phase k) v,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (volume : Measure Torus) (UnitAddTorus.mFourier (-k))]
    with x actual original
  change phase k x=_ at original
  rw [actual,original]
  change v x • UnitAddTorus.mFourier (-k) x=UnitAddTorus.mFourier (-k) x • (v x : ℂ)
  simp only [Complex.real_smul,smul_eq_mul]
  ring

theorem fourier_continuous (k : IntegerWavevector) (f : C(Torus,ℝ)) :
    fourier k ((ContinuousMap.toLp 1 volume ℝ) f)=
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k := by
  rw [fourier_integral,UnitAddTorus.mFourierCoeff,UnitAddTorus.mFourierCoeff]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus) f] with x actual
  rw [actual]

theorem finite_fourier (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : IntegerWavevector) (i j : Coordinate) :
    fourier k (-(ContinuousMap.toLp 1 volume ℝ)
      (NativeWindowFiniteGramFourier.stress seed time (modes M) i j))=
        NativeWindowAbsoluteTimePhysicalCurrent.stressCoefficient seed M time k i j := by
  rw [map_neg,fourier_continuous,
    NativeWindowFiniteGramFourier.stress_fourier seed time (modes M) (modes_closed M) i j k]
  exact neg_neg _

theorem stress_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (k : IntegerWavevector) (i j : Coordinate) :
    fourier k (stress seed time i j)=NativeCompleteStressCarrier.read
      (NativeForwardWindowSource.source seed time).snd k i j := by
  have physical:=(fourier k).continuous.tendsto (stress seed time i j) |>.comp
    (stress_tendsto seed time i j)
  simp only [Function.comp_def,finite_fourier] at physical
  exact tendsto_nhds_unique physical (NativeWindowAbsoluteTimePhysicalLimit.stress_tendsto seed time k i j)

theorem stress_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) :
    ‖stress seed time i j‖≤NativeUnifiedCompleteSource.budget seed^2 := by
  have op:‖pair‖≤1 := (ContinuousLinearMap.norm_holderL_le (B := innerSL ℝ (E := Fiber))).trans (norm_innerSL_le ℝ)
  have paid:=pair.le_opNorm₂ (synthesis i (history seed time)) (synthesis j (history seed time))
  have first:=NativeWindowAbsoluteTimePhysicalCompletion.source_bound seed time i
  have last:=NativeWindowAbsoluteTimePhysicalCompletion.source_bound seed time j
  have budget:0≤NativeUnifiedCompleteSource.budget seed := (norm_nonneg _).trans first
  rw [stress,norm_neg]
  calc
    _≤‖pair‖*‖synthesis i (history seed time)‖*‖synthesis j (history seed time)‖ := paid
    _≤1*‖synthesis i (history seed time)‖*‖synthesis j (history seed time)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right op (norm_nonneg _)) (norm_nonneg _)
    _≤1*NativeUnifiedCompleteSource.budget seed*NativeUnifiedCompleteSource.budget seed := by
      simpa only [one_mul] using mul_le_mul first last (norm_nonneg _) budget
    _=_ := by ring

def stressRate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) : Density :=
  -(pair (synthesis i (NativeWindowAbsoluteTimeSource.rate seed time)) (synthesis j (history seed time))+
    pair (synthesis i (history seed time)) (synthesis j (NativeWindowAbsoluteTimeSource.rate seed time)))

theorem stress_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (i j : Coordinate) :
    HasDerivAt (fun t => stress seed t i j) (stressRate seed time i j) time := by
  have first:=(pair.hasFDerivAt.comp_hasDerivAt time
    (NativeWindowAbsoluteTimePhysicalCompletion.source_hasDerivAt seed time i)).clm_apply
      (NativeWindowAbsoluteTimePhysicalCompletion.source_hasDerivAt seed time j)
  simpa only [stress,stressRate] using! first.neg

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem stress_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (i j : Coordinate) : stress seed (step.2.clockAdvance+time) i j=stress step.1 time i j := by
  have original:=stress_tendsto seed (step.2.clockAdvance+time) i j
  simp only [NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative] at original
  exact tendsto_nhds_unique original (stress_tendsto step.1 time i j)

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimePhysicalStress
