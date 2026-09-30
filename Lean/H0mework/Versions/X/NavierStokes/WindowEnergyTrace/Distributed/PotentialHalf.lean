import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CoveredBand
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Cubic
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Operator
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.HilbertHalfProduct

set_option autoImplicit false
open scoped Topology BigOperators ComplexConjugate
namespace SaturationMonoid.NavierStokes.NativeTracePotentialHalf
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceTerminalCubic (halfTrace halfTrace_read halfTrace_bound halfBudget)
open NativeWindowTraceGradient (traceStress)
open NativeWindowStressHeatSource (physical)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowHistoryAdjointSpatialHalf (moment cap)
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativeUnheatedSexticLatticePower (radical radical_positive)
open NativePhysicalFourier (Torus)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem halfTrace_spectrum (seed : GeneratedWholeRestartCurrent nu) (outerRadius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) (k : IntegerWavevector) :
    halfTrace seed outerRadius time k=(radical k:ℂ)*UnitAddTorus.mFourierCoeff
      (physical (traceStress seed time (integerWaveFrequencyCube outerRadius))) k := by
  rw [NativeWindowTraceTerminalCubic.physical_fourier,halfTrace_read seed outerRadius time nonnegative,
    NativeWindowTraceTerminalCubic.decode,NativeUnheatedSexticLatticePower.density,pow_one]
  simp only [Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (radical_positive k).ne'),one_mul]

private theorem evaluated_complex (M F : Finset IntegerWavevector)
    (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (v : physicalSpace M) (i : Coordinate) (x : Torus) :
    polynomial F (fun k => v.1 k i) x=(evaluate M F i v x:ℂ) := by
  have reality (k : IntegerWavevector) : v.1 (waveNeg k) i=conj (v.1 k i) :=
    congrFun (physical_reality (fun {_} inside => closedM _ inside) v k) i
  have source := congrArg (fun f : C(Torus,ℂ) => f x)
    (NativeWindowHighPressurePhysical.realSynthesis_complex F closedF (fun k => v.1 k i) reality)
  change (NativeWindowHighPressurePhysical.realSynthesis F (fun k => v.1 k i) x:ℂ)=
    NativeWindowStressHeatSource.polynomial F (fun k => v.1 k i) 0 0 x at source
  have same : evaluate M F i v=NativeWindowHighPressurePhysical.realSynthesis F (fun k => v.1 k i) := by
    rw [NativeWindowStressOseenTest.evaluate_apply]
    rfl
  rw [same]
  simpa only [polynomial,ContinuousMap.coe_mk,NativeWindowStressHeatSource.polynomial,
    pow_zero,one_mul,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_comm] using source.symm

private theorem component_energy (M F : Finset IntegerWavevector) (v : physicalSpace M) (i : Coordinate) :
    (∑ k∈F,radical k^4*‖v.1 k i‖^2) ≤ moment M 2 v := by
  have outside (k : IntegerWavevector) (absent : k∉M) : radical k^4*‖v.1 k i‖^2=0 := by
    rw [physical_supported v k absent,Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
  have finite : Summable (fun k => radical k^4*‖v.1 k i‖^2) :=
    summable_of_ne_finset_zero outside
  have first := finite.sum_le_tsum F (fun _ _ => mul_nonneg (pow_nonneg (radical_positive _).le _) (sq_nonneg _))
  rw [tsum_eq_sum outside] at first
  apply first.trans
  rw [NativeWindowHistoryAdjointSpatialHalf.moment_original]
  norm_num only
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => sq_nonneg ‖v.1 k j‖) (Finset.mem_univ i))
    (pow_nonneg (radical_positive k).le _)

theorem trace_product_square (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : Finset IntegerWavevector) (closed : FiniteModeNegClosed M) (outerRadius : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace M) (i : Coordinate) :
    ‖physical (traceStress seed time (integerWaveFrequencyCube outerRadius)*
      evaluate M (integerWaveFrequencyCube outerRadius) i v)‖^2 ≤
      cap^2*moment M 2 v*(halfBudget seed horizon)^2 := by
  let F := integerWaveFrequencyCube outerRadius
  let S := traceStress seed time F
  have paid := NativeWindowHilbertHalfProduct.scalar_product_of_spectrum (E := ℂ)
    (physical S) (halfTrace seed outerRadius time)
    (halfTrace_spectrum seed outerRadius time inside.1) F (fun k => v.1 k i)
  have represented := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure Torus)
    ((Complex.ofRealCLM.compLeftContinuous ℝ Torus) S)
  have same : (∫x : Torus,‖physical S x • polynomial F (fun k => v.1 k i) x‖^2)=
      ‖physical (S*evaluate M F i v)‖^2 := by
    rw [NativeWindowTraceTerminalSynthesis.physical_square]
    apply integral_congr_ae
    filter_upwards [represented] with x actual
    change physical S x=(S x:ℂ) at actual
    rw [actual,evaluated_complex M F closed (NativeWindowFiniteGramFourier.cube_closed outerRadius),
      norm_smul,mul_pow,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs]
    simp only [ContinuousMap.mul_apply,mul_pow]
  rw [same] at paid
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left (component_energy M F v i) (sq_nonneg cap))
    (pow_le_pow_left₀ (norm_nonneg _) (halfTrace_bound seed outerRadius time horizon inside) 2)
    (sq_nonneg _) (mul_nonneg (sq_nonneg cap) (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative M 2 v))
  exact paid.trans bound

private theorem physical_potential_bound (M F : Finset IntegerWavevector)
    (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (S : C(Torus,ℝ)) (v : physicalSpace M) :
    ‖coefficients M (NativeWindowMetricGraphPotential.potential M F (physical S) v)‖ ≤
      ∑ i : Coordinate,‖physical (S*evaluate M F i v)‖ := by
  let r := NativeWindowMetricGraphPotential.potential M F (physical S) v
  have row (i : Coordinate) : inner ℝ (physical S)
      (physical (evaluate M F i r*evaluate M F i v)) ≤
        ‖coefficients M r‖*‖physical (S*evaluate M F i v)‖ := by
    rw [NativeWindowTraceTerminalOperator.physical_exchange]
    exact ((le_abs_self _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul_of_nonneg_right
        (NativeWindowTraceTerminalSynthesis.evaluate_physical_bound M F closedM closedF r i)
        (norm_nonneg _))
  have square : ‖coefficients M r‖^2 ≤
      ‖coefficients M r‖*(∑ i : Coordinate,‖physical (S*evaluate M F i v)‖) := by
    rw [← real_inner_self_eq_norm_sq]
    change pairing M r (NativeWindowMetricGraphPotential.potential M F (physical S) v) ≤ _
    rw [NativeWindowMetricGraphPotential.potential_pairing,Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => row i
  by_cases zero : ‖coefficients M r‖=0
  · change ‖coefficients M r‖≤_
    rw [zero]
    positivity
  · have positive := (norm_nonneg (coefficients M r)).lt_of_ne (Ne.symm zero)
    change ‖coefficients M r‖≤_
    nlinarith only [square,positive]

theorem covered_potential_square (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M outerRadius radius : ℕ) (covered : integerWaveFrequencyCube outerRadius⊆integerWaveFrequencyCube radius)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖coefficients (modes M) (NativeDistributedLyapunov.potential seed M
      (integerWaveFrequencyCube outerRadius) radius time v)‖^2 ≤
      (9*cap^2*(halfBudget seed horizon)^2)*moment (modes M) 2 v := by
  let F := integerWaveFrequencyCube outerRadius
  let S := traceStress seed time F
  have normed := physical_potential_bound (modes M) F (modes_closed M)
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) S v
  have sumSquare := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate)
    (fun _ => (1:ℝ)) (fun i => ‖physical (S*evaluate (modes M) F i v)‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at sumSquare
  have rows := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
    trace_product_square seed horizon (modes M) (modes_closed M) outerRadius time inside v i
  have squared := pow_le_pow_left₀ (norm_nonneg _) normed 2
  unfold NativeDistributedLyapunov.potential
  rw [NativeTraceCoveredBand.trace_original seed F radius covered time]
  have summed : (∑ i : Coordinate,‖physical (S*evaluate (modes M) F i v)‖)^2 ≤
      (9*cap^2*(halfBudget seed horizon)^2)*moment (modes M) 2 v := by
    calc
      _ ≤ 3*(∑ i : Coordinate,‖physical (S*evaluate (modes M) F i v)‖^2) := by
        simpa only [mul_one] using sumSquare
      _ ≤ 3*(∑ _ : Coordinate,cap^2*moment (modes M) 2 v*(halfBudget seed horizon)^2) :=
        mul_le_mul_of_nonneg_left rows (by norm_num : (0:ℝ)≤3)
      _ = _ := by simp; ring
  exact squared.trans summed

theorem source_potential_square (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ radius≥low,∀ outerRadius≤radius,∀ M,
      ∀ time∈Icc 0 horizon,∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := NativeWindowTraceDualEvolution.lifted seed M F radius time w
      ‖coefficients (modes M) (NativeDistributedLyapunov.potential seed M F radius time z)‖^2 ≤
        C*NativeWindowTraceDualEvolution.energy seed M F radius time w := by
  obtain ⟨low,D,D0,source⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  let K := 9*cap^2*(halfBudget seed horizon)^2
  have K0 : 0≤K := by dsimp only [K]; positivity
  let A := NativeWindowHistoryAdjointSpatialHalf.energyCap nu
  have A0 : 0≤A := (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le
  refine ⟨low,2*K*A,by positivity,fun radius above outerRadius within M time inside w => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let z := NativeWindowTraceDualEvolution.lifted seed M F radius time w
  let E := NativeWindowTraceDualEvolution.energy seed M F radius time w
  have covered : F⊆integerWaveFrequencyCube radius := by
    intro k member
    dsimp only [F] at member
    rw [integerWaveFrequencyCube,Fintype.mem_piFinset] at member
    rw [integerWaveFrequencyCube,Fintype.mem_piFinset]
    intro i
    have point := member i
    rw [Finset.mem_Icc] at point ⊢
    have cast : (outerRadius:ℤ)≤radius := by exact_mod_cast within
    constructor <;> omega
  have raw := covered_potential_square seed horizon M outerRadius radius covered time inside z
  have control := (source radius above outerRadius M time inside).2 w |>.2.1
  have zero : 0 ≤ pairing (modes M) z z := by
    change 0 ≤ inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)
    exact real_inner_self_nonneg
  have normed : pairing (modes M) z z=‖coefficients (modes M) z‖^2 := by
    change inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)=_
    exact real_inner_self_eq_norm_sq _
  have doubled : NativeWindowHistoryHeatDual.energy nu M z≤2*E := by
    change ‖coefficients (modes M) z‖^2+
      nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) z.1 z.1≤_
    rw [normed] at control zero
    dsimp only [E,z,F] at control ⊢
    nlinarith only [control,zero]
  have momentPaid := (NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M z).trans
    (mul_le_mul_of_nonneg_left doubled A0)
  exact raw.trans ((mul_le_mul_of_nonneg_left momentPaid K0).trans_eq (by dsimp only [K,A,E,F,z]; ring))

end
end SaturationMonoid.NavierStokes.NativeTracePotentialHalf
