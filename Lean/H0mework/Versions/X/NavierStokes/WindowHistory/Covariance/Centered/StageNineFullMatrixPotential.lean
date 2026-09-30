import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineActionBlocks
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Potential

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWindowStressOseenTest NativeWindowAugmentedFixedOperator
open NativeWindowOperatorGreen
open NativeWindowStressHeatSource (physical)
open NativeWindowStressOseenTest (evaluate)
open Set
noncomputable section
variable {nu : Viscosity}

def potential (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) : Module.End ℝ (physicalSpace M) :=
  (duality M).symm.toLinearMap.comp
    (matrixPhysicalForm seed time M F radius).flip

theorem potential_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) (x y : physicalSpace M) :
    pairing M x (potential seed time M F radius y)=
      matrixPhysicalForm seed time M F radius x y := by
  have generated := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply
      ((matrixPhysicalForm seed time M F radius).flip y))
  change pairing M (potential seed time M F radius y) x=_ at generated
  rw [NativeResolventAdjoint.pairing_symmetric] at generated
  exact generated

theorem test_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    test seed time M M F radius v=
      v+nu.coeff • laplacian M zero closed nu v+
        potential seed time M F radius v := by
  apply (duality M).injective
  apply LinearMap.ext
  intro x
  change pairing M (test seed time M M F radius v) x=pairing M
    (v+nu.coeff • laplacian M zero closed nu v+potential seed time M F radius v) x
  rw [NativeResolventAdjoint.pairing_symmetric M (test seed time M M F radius v) x,
    NativeResolventAdjoint.pairing_symmetric M
      (v+nu.coeff • laplacian M zero closed nu v+potential seed time M F radius v) x]
  rw [test_pairing,physicalForm,LinearMap.add_apply,LinearMap.add_apply,
    NativeWindowTraceOperatorAction.spectral_laplacian M zero closed]
  simp only [map_add,map_smul,smul_eq_mul,potential_pairing]

theorem potential_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ)
    (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F)
    (v : physicalSpace M) :
    ‖coefficients M (potential seed time M F radius v)‖ ≤
      ∑ output : Coordinate,∑ input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F input v‖ := by
  let r:=potential seed time M F radius v
  have row (output input : Coordinate) :
      NativeWindowAugmentedSourceForm.matrixRead seed time F radius output input
        (evaluate M F output r*evaluate M F input v) ≤
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F input v‖*‖coefficients M r‖ := by
    have product : ‖physical (evaluate M F output r*evaluate M F input v)‖≤
        ‖evaluate M F input v‖*‖coefficients M r‖ := by
      rw [mul_comm]
      exact (NativeWindowTraceTerminalSynthesis.product_bound _ _).trans
        (mul_le_mul_of_nonneg_left
          (NativeWindowTraceTerminalSynthesis.evaluate_physical_bound M F closedM closedF r output)
          (norm_nonneg _))
    change inner ℝ (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input)
      (physical (evaluate M F output r*evaluate M F input v)) ≤ _
    have pair := (le_abs_self _).trans (abs_real_inner_le_norm
      (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input)
      (physical (evaluate M F output r*evaluate M F input v)))
    have scaled := mul_le_mul_of_nonneg_left product
      (norm_nonneg (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input))
    exact (pair.trans scaled).trans_eq (by ring)
  have squared : ‖coefficients M r‖^2 ≤
      (∑ output : Coordinate,∑ input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F input v‖)*‖coefficients M r‖ := by
    have normed : ‖coefficients M r‖^2=pairing M r r :=
      (real_inner_self_eq_norm_sq _).symm
    rw [normed]
    change pairing M r (potential seed time M F radius v)≤_
    rw [potential_pairing]
    simp only [matrixPhysicalForm,LinearMap.mk₂_apply,Finset.sum_mul]
    exact Finset.sum_le_sum fun output _ => Finset.sum_le_sum fun input _ => row output input
  by_cases zero : ‖coefficients M r‖=0
  · rw [zero]
    exact Finset.sum_nonneg fun output _ => Finset.sum_nonneg fun input _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have positive : 0<‖coefficients M r‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    nlinarith only [squared,positive]

theorem source_field_bound (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃B : ℝ,0≤B ∧
      ∀radius≥low,∀outerRadius (time : ℝ),time∈Icc 0 horizon →
        ∀output input : Coordinate,
          ‖NativeWindowAugmentedSourceForm.matrixField seed time
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius output input‖≤B := by
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.correctionJet_small
    seed 0 horizon nonnegative 1 (by norm_num)
  let S:=NativeWindowAugmentedPayment.stressBudget seed 0 horizon
  let B:=S+1
  have S0 : 0≤S := by
    have inside : (0 : ℝ)∈Icc 0 horizon := ⟨le_rfl,nonnegative⟩
    have source := NativeWindowAugmentedPayment.stressJet_bound seed 0 0 0 horizon inside 0 0
    exact (norm_nonneg _).trans source
  refine ⟨low,B,by dsimp only [B]; linarith,fun radius above outerRadius time inside output input => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  have correction : ‖NativeWindowPressureStrainHistory.correction seed F radius time output input‖≤1 := by
    simpa only [NativeWindowJointNormalForm.correctionJet_zero] using
      (paid radius above F time inside output input).le
  have stress : ‖NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress seed time F output input)‖≤S := by
    have original := NativeWindowAugmentedPayment.stressJet_bound
      seed outerRadius 0 time horizon inside output input
    rw [NativeWindowAugmentedPayment.stressJet_original seed outerRadius 0 time inside.1,
      NativeWindowStressHeatTime.jet_zero] at original
    exact original
  change ‖NativeWindowStressHeatSource.physical
      (NativeWindowFiniteGramFourier.stress seed time F output input)+
        NativeWindowPressureStrainHistory.correction seed F radius time output input‖≤B
  exact (norm_add_le _ _).trans (add_le_add stress correction)

theorem potential_relative_of_field (seed : GeneratedWholeRestartCurrent nu)
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
          ‖coefficients M (potential seed time M
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
  have source:=potential_bound seed time M F radius closed
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) v
  have sumBound :
      (∑output : Coordinate,∑input : Coordinate,
        ‖NativeWindowAugmentedSourceForm.matrixField seed time F radius output input‖*
          ‖evaluate M F input v‖)≤9*B*(delta*d+D*m) := by
    have rows:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
        mul_le_mul (field radius above outerRadius time inside output input)
          (evaluateBound M F zero closed v input) (norm_nonneg _) B0
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

theorem source_potential_relative (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈Icc 0 horizon,∀v : physicalSpace M,
          ‖coefficients M (potential seed time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)‖≤
            epsilon*‖coefficients M (laplacian M zero closed nu v)‖+
              C*‖coefficients M v‖ := by
  obtain ⟨low,B,B0,field⟩ := source_field_bound seed horizon nonnegative
  obtain ⟨C,C0,paid⟩ := potential_relative_of_field seed (Icc 0 horizon)
    low B B0 field epsilon positive
  exact ⟨low,C,C0,paid⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
