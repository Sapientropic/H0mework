import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Synthesis
import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffOperatorTime

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphPotential
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWindowOperatorGreen
open NativePhysicalFourier
open NativeWindowStressOseenTest (evaluate duality)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def form (M F : Finset IntegerWavevector) (a : ScalarField) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : Coordinate,inner ℝ a (physical (evaluate M F i x*evaluate M F i y)))
    (fun _ _ _ => by simp only [map_add,add_mul,inner_add_right,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,smul_mul_assoc,real_inner_smul_right,Finset.mul_sum,smul_eq_mul])
    (fun _ _ _ => by simp only [map_add,mul_add,inner_add_right,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,real_inner_smul_right,Finset.mul_sum,smul_eq_mul])

def potential (M F : Finset IntegerWavevector) (a : ScalarField) : Module.End ℝ (physicalSpace M) :=
  (duality M).symm.toLinearMap.comp (form M F a).flip

theorem potential_pairing (M F : Finset IntegerWavevector) (a : ScalarField) (x y : physicalSpace M) :
    pairing M x (potential M F a y)=∑ i : Coordinate,inner ℝ a (physical (evaluate M F i x*evaluate M F i y)) := by
  have source := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply ((form M F a).flip y))
  change pairing M (potential M F a y) x=_ at source
  rw [pairing_symmetric] at source
  exact source

theorem potential_bound (M F : Finset IntegerWavevector) (closedM : FiniteModeNegClosed M)
    (closedF : FiniteModeNegClosed F) (a : ScalarField) (v : physicalSpace M) :
    ‖coefficients M (potential M F a v)‖ ≤ ‖a‖*(∑ i : Coordinate,‖evaluate M F i v‖) := by
  let r := potential M F a v
  have row (i : Coordinate) : inner ℝ a (physical (evaluate M F i r*evaluate M F i v)) ≤
      ‖a‖*(‖evaluate M F i v‖*‖coefficients M r‖) := by
    have product := (NativeWindowTraceTerminalSynthesis.product_bound (evaluate M F i v) (evaluate M F i r)).trans
      (mul_le_mul_of_nonneg_left (NativeWindowTraceTerminalSynthesis.evaluate_physical_bound M F closedM closedF r i) (norm_nonneg _))
    rw [mul_comm (evaluate M F i v)] at product
    exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left product (norm_nonneg _)))
  have squared : ‖coefficients M r‖^2 ≤ (‖a‖*(∑ i : Coordinate,‖evaluate M F i v‖))*‖coefficients M r‖ := by
    have normed : ‖coefficients M r‖^2=pairing M r r := (real_inner_self_eq_norm_sq _).symm
    rw [normed]
    change pairing M r (potential M F a v) ≤ _
    rw [potential_pairing]
    exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by rw [← Finset.mul_sum,← Finset.sum_mul]; ring)
  by_cases zero : ‖coefficients M r‖=0
  · rw [zero]
    positivity
  · have positive : 0 < ‖coefficients M r‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    nlinarith only [squared,positive]

theorem exists_potential_bound (nu : Viscosity) (B : ℝ) (B0 : 0 ≤ B) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M F : Finset IntegerWavevector,∀ zero : 0 ∉ M,
      ∀ closedM : FiniteModeNegClosed M,FiniteModeNegClosed F → ∀ a : ScalarField,‖a‖ ≤ B →
      ∀ v : physicalSpace M,‖coefficients M (potential M F a v)‖ ≤
        epsilon*‖coefficients M (laplacian M zero closedM nu v)‖+C*‖coefficients M v‖ := by
  let delta := epsilon/(3*(B+1))
  have delta0 : 0 < delta := div_pos positive (by positivity)
  obtain ⟨C,C0,source⟩ := NativeWindowMetricGraphSynthesis.exists_evaluate_bound nu delta delta0
  refine ⟨3*B*C,by positivity,fun M F zero closedM closedF a bound v => ?_⟩
  have sum : (∑ i : Coordinate,‖evaluate M F i v‖) ≤
      3*(delta*‖coefficients M (laplacian M zero closedM nu v)‖+C*‖coefficients M v‖) :=
    (Finset.sum_le_sum fun i _ => source M F zero closedM v i).trans_eq (by simp; ring)
  have base := (potential_bound M F closedM closedF a v).trans
    (mul_le_mul bound sum (Finset.sum_nonneg fun _ _ => norm_nonneg _) B0)
  have fraction : 3*B*delta ≤ epsilon := by
    dsimp only [delta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 3*(B+1))).mpr
    nlinarith
  have scaled := mul_le_mul_of_nonneg_right fraction (norm_nonneg (coefficients M (laplacian M zero closedM nu v)))
  nlinarith only [base,scaled]

theorem test_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    NativeWindowTraceCutOperator.test seed frame M M F radius v=
      v+nu.coeff • laplacian M zero closed nu v+potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v := by
  apply (duality M).injective
  apply LinearMap.ext
  intro x
  change pairing M (NativeWindowTraceCutOperator.test seed frame M M F radius v) x=pairing M
    (v+nu.coeff • laplacian M zero closed nu v+potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v) x
  rw [pairing_symmetric M (NativeWindowTraceCutOperator.test seed frame M M F radius v) x,
    pairing_symmetric M (v+nu.coeff • laplacian M zero closed nu v+potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v) x]
  rw [NativeWindowTraceCutOperator.test_pairing,NativeWindowTraceOperatorAction.spectral_laplacian M zero closed]
  simp only [map_add,map_smul,smul_eq_mul,potential_pairing,NativeWindowTraceCutTime.fieldJet_zero,inner_neg_left,Finset.sum_neg_distrib]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphPotential
