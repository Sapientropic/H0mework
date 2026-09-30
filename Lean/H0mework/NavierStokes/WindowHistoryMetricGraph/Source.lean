import H0mework.NavierStokes.WindowHistoryMetricGraph.Potential

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWindowOperatorGreen
open NativeWindowMetricGraphPotential (potential test_split)
open NativePhysicalFourier
noncomputable section
variable {nu : Viscosity}

private theorem paired_norm (M : Finset IntegerWavevector) (v : physicalSpace M) :
    pairing M v v=‖coefficients M v‖^2 := real_inner_self_eq_norm_sq (coefficients M v)

private theorem pair_bound (M : Finset IntegerWavevector) (u v : physicalSpace M) :
    |pairing M u v| ≤ ‖coefficients M u‖*‖coefficients M v‖ := abs_real_inner_le_norm (coefficients M u) (coefficients M v)

private theorem curl_nonnegative (M : Finset IntegerWavevector) (v : physicalSpace M) : 0 ≤ curlPair M v.1 v.1 := by
  unfold curlPair
  simp only [complexCoordinateRealInner_self]
  exact Finset.sum_nonneg fun _ _ => complexCoordinateVectorNormSq_nonneg _

private theorem square_bound (x y z A B : ℝ) (x0 : 0 ≤ x) (bound : x ≤ A*y+B*z) :
    x^2 ≤ (2*A^2+2*B^2)*(y^2+z^2) := by
  have squared := pow_le_pow_left₀ x0 bound 2
  nlinarith only [squared,sq_nonneg (A*y-B*z),mul_nonneg (sq_nonneg A) (sq_nonneg z),
    mul_nonneg (sq_nonneg B) (sq_nonneg y)]

private theorem heat_bound (nu C d m h : ℝ) (positive : 0 < nu)
    (lower : nu*d^2-(nu/4*d+C*m)*d ≤ h) :
    -2*nu*h ≤ -nu^2*d^2+2*C^2*m^2 := by
  have paid := mul_le_mul_of_nonneg_left lower positive.le
  nlinarith only [paid,sq_nonneg (nu*d-2*C*m)]

def cap (nu : Viscosity) (C : ℝ) : ℝ := 2*(5*nu.coeff/4)^2+2*(C+1)^2+2*C^2

theorem cap_nonnegative (nu : Viscosity) (C : ℝ) : 0 ≤ cap nu C := by unfold cap; positivity

private theorem upper (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) (C : ℝ)
    (paid : ‖coefficients M (potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v)‖ ≤
      (nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+C*‖coefficients M v‖) :
    ‖coefficients M (NativeWindowTraceCutOperator.test seed frame M M F radius v)‖^2 ≤
      cap nu C*(‖coefficients M (laplacian M zero closed nu v)‖^2+‖coefficients M v‖^2) := by
  have linear : ‖coefficients M (NativeWindowTraceCutOperator.test seed frame M M F radius v)‖ ≤
      (5*nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+(C+1)*‖coefficients M v‖ := by
    rw [test_split seed frame M F radius zero closed v,map_add,map_add,map_smul]
    have first := norm_add_le (coefficients M v) (nu.coeff • coefficients M (laplacian M zero closed nu v))
    have last := norm_add_le (coefficients M v+nu.coeff • coefficients M (laplacian M zero closed nu v))
      (coefficients M (potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v))
    rw [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le] at first
    nlinarith only [first,last,paid]
  have squared := square_bound _ _ _ _ _ (norm_nonneg _) linear
  have extra := mul_nonneg (show 0 ≤ 2*C^2 by positivity)
    (add_nonneg (sq_nonneg ‖coefficients M (laplacian M zero closed nu v)‖) (sq_nonneg ‖coefficients M v‖))
  dsimp only [cap]
  nlinarith only [squared,extra]

private theorem heat (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0 ∉ M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) (C : ℝ)
    (paid : ‖coefficients M (potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v)‖ ≤
      (nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+C*‖coefficients M v‖) :
    -2*nu.coeff*pairing M (NativeWindowTraceCutOperator.test seed frame M M F radius v) (laplacian M zero closed nu v) ≤
      -nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+cap nu C*‖coefficients M v‖^2 := by
  let L := laplacian M zero closed nu v
  let P := potential M F (NativeWindowTraceCutTime.fieldJet seed F radius 0 frame) v
  have source : pairing M (NativeWindowTraceCutOperator.test seed frame M M F radius v) L=
      curlPair M v.1 v.1+nu.coeff*‖coefficients M L‖^2+pairing M P L := by
    rw [test_split seed frame M F radius zero closed v]
    simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [laplacian_pairing M zero closed nu v v,paired_norm]
  have bounded := (pair_bound M P L).trans (mul_le_mul_of_nonneg_right paid (norm_nonneg (coefficients M L)))
  have lower : nu.coeff*‖coefficients M L‖^2-
      ((nu.coeff/4)*‖coefficients M L‖+C*‖coefficients M v‖)*‖coefficients M L‖ ≤
        pairing M (NativeWindowTraceCutOperator.test seed frame M M F radius v) L := by
    have sign := neg_abs_le (pairing M P L)
    have positive := curl_nonnegative M v
    linarith only [source,bounded,sign,positive]
  have final := heat_bound nu.coeff C _ _ _ nu.coeff_pos lower
  have extra := mul_nonneg (show 0 ≤ 2*(5*nu.coeff/4)^2+2*(C+1)^2 by positivity) (sq_nonneg ‖coefficients M v‖)
  dsimp only [cap]
  nlinarith only [final,extra]

theorem source_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : Finset IntegerWavevector,
      ∀ zero : 0 ∉ M,∀ closed : FiniteModeNegClosed M,∀ frame ∈ Icc 0 horizon,∀ v : physicalSpace M,
        ‖coefficients M (NativeWindowTraceCutOperator.test seed frame M M (integerWaveFrequencyCube cutoff) radius v)‖^2 ≤
          C*(‖coefficients M (laplacian M zero closed nu v)‖^2+‖coefficients M v‖^2) ∧
        -2*nu.coeff*pairing M (NativeWindowTraceCutOperator.test seed frame M M (integerWaveFrequencyCube cutoff) radius v)
          (laplacian M zero closed nu v) ≤
            -nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+C*‖coefficients M v‖^2 := by
  obtain ⟨low,B,B0,field⟩ := NativeWindowTraceCutTime.source_field_bound seed horizon nonnegative 0
  obtain ⟨C,C0,source⟩ := NativeWindowMetricGraphPotential.exists_potential_bound nu B B0 (nu.coeff/4) (by positivity [nu.coeff_pos])
  refine ⟨low,cap nu C,cap_nonnegative nu C,fun radius above cutoff covered M zero closed frame inside v => ?_⟩
  have paid := source M (integerWaveFrequencyCube cutoff) zero closed
    (NativeWindowFiniteGramFourier.cube_closed cutoff) _ (field radius above cutoff covered frame inside) v
  exact ⟨upper seed frame M _ radius zero closed v C paid,heat seed frame M _ radius zero closed v C paid⟩

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphSource
