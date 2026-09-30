import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedMatrixHistory

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWindowStressOseenTest NativeWindowAugmentedFixedOperator
open NativeWindowOperatorGreen
open NativeWindowStressHeatSource (physical)
open NativeWindowStressOseenTest (evaluate)
noncomputable section
variable {nu : Viscosity}

def transposePotential (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) : Module.End ℝ (physicalSpace M) :=
  (duality M).symm.toLinearMap.comp (matrixPhysicalForm seed time M F radius)

theorem transposePotential_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace M) :
    pairing M x (transposePotential seed time M F radius y)=
      matrixPhysicalForm seed time M F radius y x := by
  have generated := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply (matrixPhysicalForm seed time M F radius y))
  change pairing M (transposePotential seed time M F radius y) x=_ at generated
  rw [NativeResolventAdjoint.pairing_symmetric] at generated
  exact generated

theorem transposePotential_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ)
    (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (v : physicalSpace M) :
    ‖coefficients M (transposePotential seed time M F radius v)‖ ≤
      ∑ output : Coordinate,∑ input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F output v‖ := by
  let r:=transposePotential seed time M F radius v
  have row (output input : Coordinate) :
      NativeWindowAugmentedSourceForm.matrixRead seed time F radius output input
        (evaluate M F output v*evaluate M F input r) ≤
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F output v‖*‖coefficients M r‖ := by
    have product : ‖physical (evaluate M F output v*evaluate M F input r)‖≤
        ‖evaluate M F output v‖*‖coefficients M r‖ :=
      (NativeWindowTraceTerminalSynthesis.product_bound _ _).trans
        (mul_le_mul_of_nonneg_left
          (NativeWindowTraceTerminalSynthesis.evaluate_physical_bound M F closedM closedF r input)
          (norm_nonneg _))
    change inner ℝ (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input)
      (physical (evaluate M F output v*evaluate M F input r)) ≤ _
    have pair := (le_abs_self _).trans (abs_real_inner_le_norm
      (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input)
      (physical (evaluate M F output v*evaluate M F input r)))
    have scaled := mul_le_mul_of_nonneg_left product
      (norm_nonneg (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input))
    exact (pair.trans scaled).trans_eq (by ring)
  have squared : ‖coefficients M r‖^2 ≤
      (∑ output : Coordinate,∑ input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F output v‖)*‖coefficients M r‖ := by
    have normed : ‖coefficients M r‖^2=pairing M r r :=
      (real_inner_self_eq_norm_sq _).symm
    rw [normed]
    change pairing M r (transposePotential seed time M F radius v)≤_
    rw [transposePotential_pairing]
    simp only [matrixPhysicalForm,LinearMap.mk₂_apply,Finset.sum_mul]
    exact Finset.sum_le_sum fun output _ => Finset.sum_le_sum fun input _ => row output input
  by_cases zero : ‖coefficients M r‖=0
  · rw [zero]
    exact Finset.sum_nonneg fun output _ => Finset.sum_nonneg fun input _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have positive : 0<‖coefficients M r‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    nlinarith only [squared,positive]

theorem transposePotential_relative_of_field (seed : GeneratedWholeRestartCurrent nu)
    (S : Set ℝ) (low : ℕ) (B : ℝ) (B0 : 0≤B)
    (field : ∀radius≥low,∀outerRadius (time : ℝ),time∈S →
      ∀output input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius output input‖≤B)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈S,∀v : physicalSpace M,
          ‖coefficients M (transposePotential seed time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)‖≤
            epsilon*‖coefficients M (laplacian M zero closed nu v)‖+
              C*‖coefficients M v‖ := by
  let delta:=epsilon/(9*(B+1))
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  obtain ⟨D,D0,evaluateBound⟩ :=
    NativeWindowMetricGraphSynthesis.exists_evaluate_bound nu delta delta0
  let C:=9*B*D
  refine ⟨C,by dsimp only [C]; positivity,fun radius above outerRadius M zero closed time inside v => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let d:=‖coefficients M (laplacian M zero closed nu v)‖
  let m:=‖coefficients M v‖
  have source:=transposePotential_bound seed time M F radius closed
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) v
  have sumBound :
      (∑output : Coordinate,∑input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F output v‖)≤9*B*(delta*d+D*m) := by
    have rows:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
        mul_le_mul (field radius above outerRadius time inside output input)
          (evaluateBound M F zero closed v output) (norm_nonneg _) B0
    exact rows.trans_eq (by simp; ring)
  have frac : 9*B*delta≤epsilon := by
    have denominator : 0<9*(B+1) := by positivity
    have identity : delta*(9*(B+1))=epsilon := by
      dsimp only [delta]
      exact div_mul_cancel₀ _ denominator.ne'
    nlinarith only [identity,delta0]
  have scaled:=mul_le_mul_of_nonneg_right frac (norm_nonneg (coefficients M (laplacian M zero closed nu v)))
  dsimp only [d,m,C] at sumBound scaled ⊢
  nlinarith only [source,sumBound,scaled]

def transposeTest (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) :
    Module.End ℝ (physicalSpace M) :=
  (duality M).symm.toLinearMap.comp
    (spectral nu M L+(matrixPhysicalForm seed time M F radius).flip).flip

theorem transposeTest_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace M) :
    pairing M x (transposeTest seed time M L F radius y)=
      spectral nu M L x y+matrixPhysicalForm seed time M F radius y x := by
  have generated:=congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply
      ((spectral nu M L+(matrixPhysicalForm seed time M F radius).flip).flip y))
  change pairing M (transposeTest seed time M L F radius y) x=_ at generated
  rw [NativeResolventAdjoint.pairing_symmetric] at generated
  change pairing M x (transposeTest seed time M L F radius y)=
    spectral nu M L x y+matrixPhysicalForm seed time M F radius y x at generated
  exact generated

theorem transposeTest_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    transposeTest seed time M M F radius v=
      v+nu.coeff • laplacian M zero closed nu v+
        transposePotential seed time M F radius v := by
  apply (duality M).injective
  apply LinearMap.ext
  intro x
  change pairing M (transposeTest seed time M M F radius v) x=pairing M
    (v+nu.coeff • laplacian M zero closed nu v+
      transposePotential seed time M F radius v) x
  rw [NativeResolventAdjoint.pairing_symmetric M
      (transposeTest seed time M M F radius v) x,
    NativeResolventAdjoint.pairing_symmetric M
      (v+nu.coeff • laplacian M zero closed nu v+
        transposePotential seed time M F radius v) x]
  rw [transposeTest_pairing,
    NativeWindowTraceOperatorAction.spectral_laplacian M zero closed]
  simp only [map_add,map_smul,smul_eq_mul,transposePotential_pairing]

theorem spectral_symmetric (M L : Finset IntegerWavevector)
    (x y : physicalSpace M) :
    spectral nu M L x y=spectral nu M L y x := by
  simp only [spectral,LinearMap.mk₂_apply]
  apply Finset.sum_congr rfl
  intro wave _
  apply Finset.sum_congr rfl
  intro coordinate _
  exact congrArg (fun z : ℝ => (1+nu.coeff*integerWaveViscousMultiplier wave)*z)
    (real_inner_comm _ _)

theorem transposeTest_dual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M L F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) :
    pairing M x (transposeTest seed time M L F radius y)=
      pairing M y (test seed time M L F radius x) := by
  rw [transposeTest_pairing,test_pairing,physicalForm,
    LinearMap.add_apply,LinearMap.add_apply,spectral_symmetric M L x y]
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
