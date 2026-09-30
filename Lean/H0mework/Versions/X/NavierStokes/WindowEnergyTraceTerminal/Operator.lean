import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Synthesis
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffOperatorKernel

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalOperator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWindowOperatorGreen NativeCommonAdvectorAction
open NativePhysicalFourier NativeWindowStressOseenTest
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceTerminalSynthesis (cap evaluate_bound evaluate_physical_bound product_bound)
open NativeWindowTraceGradient (traceStress)
open NativeWindowConvectionCutoffTrace (relative correction)
open NativeWindowTraceCutOperator (jointTest)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem trace_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    relative seed F radius time= -physical (traceStress seed time F)-correction seed F radius time := by
  simp only [relative,NativeWindowConvectionCutoffNormalForm.relative_original,NativeWindowStressHeatBalance.sigma,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,correction,traceStress,map_sum]

theorem physical_exchange (S f g : C(Torus,ℝ)) : inner ℝ (physical S) (physical (f*g))=
    inner ℝ (physical f) (physical (S*g)) := by
  rw [NativeWindowStressHeatSource.physical_inner,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

def stressNorm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (v : physicalSpace M) : ℝ :=
  ∑ i : Coordinate,‖physical (traceStress seed observation F*evaluate M F i v)‖

def remainder (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0∉M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) : physicalSpace M :=
  jointTest seed observation M F radius v+nu.coeff • laplacian M zero closed nu v

theorem remainder_pairing (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0∉M) (closed : FiniteModeNegClosed M) (x v : physicalSpace M) :
    pairing M x (remainder seed observation M F radius zero closed v)=
      ∑ i : Coordinate,inner ℝ (relative seed F radius observation) (physical (evaluate M F i x*evaluate M F i v)) := by
  rw [remainder,map_add,map_smul,NativeWindowTraceCutOperator.jointTest_physical seed observation M F radius zero closed]
  simp only [smul_eq_mul]
  ring

theorem remainder_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0∉M) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F) (v : physicalSpace M) :
    ‖coefficients M (remainder seed observation M F radius zero closedM v)‖ ≤ stressNorm seed observation M F v+
      3*cap*‖correction seed F radius observation‖*‖coefficients M (laplacian M zero closedM nu v)‖ := by
  let r:=remainder seed observation M F radius zero closedM v
  let D:=‖coefficients M (laplacian M zero closedM nu v)‖
  have stress (i : Coordinate) : |inner ℝ (physical (traceStress seed observation F)) (physical (evaluate M F i r*evaluate M F i v))|≤
      ‖coefficients M r‖*‖physical (traceStress seed observation F*evaluate M F i v)‖ := by
    rw [physical_exchange]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (evaluate_physical_bound M F closedM closedF r i) (norm_nonneg _))
  have corr (i : Coordinate) : |inner ℝ (correction seed F radius observation) (physical (evaluate M F i r*evaluate M F i v))|≤
      ‖coefficients M r‖*(cap*‖correction seed F radius observation‖*D) := by
    have product : ‖physical (evaluate M F i r*evaluate M F i v)‖≤cap*D*‖coefficients M r‖ := by
      rw [mul_comm (evaluate M F i r)]
      exact (product_bound _ _).trans (mul_le_mul (evaluate_bound nu M F zero closedM v i)
        (evaluate_physical_bound M F closedM closedF r i) (norm_nonneg _) (by positivity [NativeWindowTraceTerminalSynthesis.cap_positive]))
    exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left product (norm_nonneg _)).trans_eq (by ring))
  have point (i : Coordinate) : inner ℝ (relative seed F radius observation) (physical (evaluate M F i r*evaluate M F i v))≤
      ‖coefficients M r‖*(‖physical (traceStress seed observation F*evaluate M F i v)‖+cap*‖correction seed F radius observation‖*D) := by
    rw [trace_split,inner_sub_left,inner_neg_left]
    have first := (neg_le_abs _).trans (stress i)
    have last := (neg_le_abs _).trans (corr i)
    linarith only [first,last]
  have bound : ‖coefficients M r‖^2≤‖coefficients M r‖*(stressNorm seed observation M F v+3*cap*‖correction seed F radius observation‖*D) := by
    rw [← real_inner_self_eq_norm_sq]
    change pairing M r r≤_
    rw [remainder_pairing]
    exact (Finset.sum_le_sum fun i _ => point i).trans_eq (by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,stressNorm]
      ring)
  by_cases zeroNorm : ‖coefficients M r‖=0
  · change ‖coefficients M r‖≤_
    rw [zeroNorm]
    unfold stressNorm
    positivity [NativeWindowTraceTerminalSynthesis.cap_positive]
  · have positive := (norm_nonneg (coefficients M r)).lt_of_ne (Ne.symm zeroNorm)
    change ‖coefficients M r‖≤_
    nlinarith only [bound,positive]

theorem joint_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0∉M) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F) (v : physicalSpace M) :
    ‖coefficients M (jointTest seed observation M F radius v)‖≤
      (nu.coeff+3*cap*‖correction seed F radius observation‖)*‖coefficients M (laplacian M zero closedM nu v)‖+
        stressNorm seed observation M F v := by
  have same : jointTest seed observation M F radius v=remainder seed observation M F radius zero closedM v-
      nu.coeff • laplacian M zero closedM nu v := by unfold remainder; abel
  rw [same,map_sub,map_smul]
  apply (norm_sub_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le]
  exact (add_le_add (remainder_bound seed observation M F radius zero closedM closedF v) le_rfl).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalOperator
