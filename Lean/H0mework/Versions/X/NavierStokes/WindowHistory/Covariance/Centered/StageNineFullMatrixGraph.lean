import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineFullMatrixPotential
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
private theorem square_bound (x y z A B : ℝ) (x0 : 0≤x)
    (bound : x≤A*y+B*z) :
    x^2≤(2*A^2+2*B^2)*(y^2+z^2) := by
  have squared:=pow_le_pow_left₀ x0 bound 2
  nlinarith only [squared,sq_nonneg (A*y-B*z),
    mul_nonneg (sq_nonneg A) (sq_nonneg z),
    mul_nonneg (sq_nonneg B) (sq_nonneg y)]

private theorem heat_bound (nu C d m h : ℝ) (positive : 0<nu)
    (lower : nu*d^2-(nu/4*d+C*m)*d≤h) :
    -2*nu*h≤-nu^2*d^2+2*C^2*m^2 := by
  have paid:=mul_le_mul_of_nonneg_left lower positive.le
  nlinarith only [paid,sq_nonneg (nu*d-2*C*m)]

def graphCap (nu : Viscosity) (C : ℝ) : ℝ :=
  2*(5*nu.coeff/4)^2+2*(C+1)^2+2*C^2

theorem graphCap_nonnegative (nu : Viscosity) (C : ℝ) :
    0≤graphCap nu C := by unfold graphCap; positivity

theorem graph_upper_of_split
    (M : Finset IntegerWavevector)
    (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (T P : Module.End ℝ (physicalSpace M)) (v : physicalSpace M) (C : ℝ)
    (split : T v=v+nu.coeff • laplacian M zero closed nu v+P v)
    (paid : ‖coefficients M (P v)‖≤
      (nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+
        C*‖coefficients M v‖) :
    ‖coefficients M (T v)‖^2≤
      graphCap nu C*(‖coefficients M (laplacian M zero closed nu v)‖^2+
        ‖coefficients M v‖^2) := by
  have linear : ‖coefficients M (T v)‖≤
      (5*nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+
        (C+1)*‖coefficients M v‖ := by
    rw [split,map_add,map_add,map_smul]
    have first:=norm_add_le (coefficients M v)
      (nu.coeff • coefficients M (laplacian M zero closed nu v))
    have last:=norm_add_le
      (coefficients M v+nu.coeff • coefficients M (laplacian M zero closed nu v))
      (coefficients M (P v))
    rw [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le] at first
    nlinarith only [first,last,paid]
  have squared:=square_bound _ _ _ _ _ (norm_nonneg _) linear
  have extra:=mul_nonneg (show 0≤2*C^2 by positivity)
    (add_nonneg (sq_nonneg ‖coefficients M (laplacian M zero closed nu v)‖)
      (sq_nonneg ‖coefficients M v‖))
  dsimp only [graphCap]
  nlinarith only [squared,extra]

theorem graph_heat_of_split
    (M : Finset IntegerWavevector)
    (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (T P : Module.End ℝ (physicalSpace M)) (v : physicalSpace M) (C : ℝ)
    (split : T v=v+nu.coeff • laplacian M zero closed nu v+P v)
    (paid : ‖coefficients M (P v)‖≤
      (nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+
        C*‖coefficients M v‖) :
    -2*nu.coeff*pairing M (T v)
      (laplacian M zero closed nu v)≤
      -nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+
        graphCap nu C*‖coefficients M v‖^2 := by
  let L:=laplacian M zero closed nu v
  let p:=P v
  have source : pairing M (T v) L=
      NativeCommonAdvectorAction.curlPair M v.1 v.1+
        nu.coeff*‖coefficients M L‖^2+pairing M p L := by
    rw [split]
    simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [laplacian_pairing M zero closed nu v v]
    change _+nu.coeff*inner ℝ (coefficients M L) (coefficients M L)+_=_
    rw [real_inner_self_eq_norm_sq]
  have bound: |pairing M p L|≤‖coefficients M p‖*‖coefficients M L‖ :=
    abs_real_inner_le_norm (coefficients M p) (coefficients M L)
  have bounded:=bound.trans (mul_le_mul_of_nonneg_right paid (norm_nonneg (coefficients M L)))
  have lower : nu.coeff*‖coefficients M L‖^2-
      ((nu.coeff/4)*‖coefficients M L‖+C*‖coefficients M v‖)*‖coefficients M L‖ ≤
        pairing M (T v) L := by
    have sign:=neg_abs_le (pairing M p L)
    have positive : 0≤NativeCommonAdvectorAction.curlPair M v.1 v.1 := by
      unfold NativeCommonAdvectorAction.curlPair
      simp only [ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval.complexCoordinateRealInner_self]
      exact Finset.sum_nonneg fun _ _ =>
        ThreeDimensionalVorticityCoefficientStretchingPairTable.complexCoordinateVectorNormSq_nonneg _
    linarith only [source,bounded,sign,positive]
  have final:=heat_bound nu.coeff C _ _ _ nu.coeff_pos lower
  have extra:=mul_nonneg (show 0≤2*(5*nu.coeff/4)^2+2*(C+1)^2 by positivity)
    (sq_nonneg ‖coefficients M v‖)
  dsimp only [graphCap]
  nlinarith only [final,extra]

theorem test_graph_of_relative (seed : GeneratedWholeRestartCurrent nu)
    (S : Set ℝ) (low : ℕ) (C : ℝ)
    (paid : ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
      ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
      ∀time∈S,∀v : physicalSpace M,
        ‖coefficients M (potential seed time M
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius v)‖≤
          (nu.coeff/4)*‖coefficients M (laplacian M zero closed nu v)‖+
            C*‖coefficients M v‖) :
    ∃D : ℝ,0≤D ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈S,∀v : physicalSpace M,
          ‖coefficients M (test seed time M M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)‖^2≤
            D*(‖coefficients M (laplacian M zero closed nu v)‖^2+
              ‖coefficients M v‖^2) ∧
          -2*nu.coeff*pairing M
            (test seed time M M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacian M zero closed nu v)≤
            -nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+
              D*‖coefficients M v‖^2 := by
  refine ⟨graphCap nu C,graphCap_nonnegative nu C,
    fun radius above outerRadius M zero closed time inside v => ?_⟩
  have source:=paid radius above outerRadius M zero closed time inside v
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let T:=test seed time M M F radius
  let P:=potential seed time M F radius
  have split:=test_split seed time M F radius zero closed v
  exact ⟨graph_upper_of_split M zero closed T P v C split source,
    graph_heat_of_split M zero closed T P v C split source⟩

theorem source_full_test_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius (M : Finset IntegerWavevector),
        ∀zero : 0∉M,∀closed : FiniteModeNegClosed M,
        ∀time∈Icc 0 horizon,∀v : physicalSpace M,
          ‖coefficients M (test seed time M M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius v)‖^2≤
            C*(‖coefficients M (laplacian M zero closed nu v)‖^2+
              ‖coefficients M v‖^2) ∧
          -2*nu.coeff*pairing M
            (test seed time M M
              (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
                outerRadius) radius v)
            (laplacian M zero closed nu v)≤
            -nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+
              C*‖coefficients M v‖^2 := by
  obtain ⟨low,C,C0,paid⟩ := source_potential_relative seed horizon nonnegative
    (nu.coeff/4) (by positivity [nu.coeff_pos])
  obtain ⟨D,D0,graph⟩ := test_graph_of_relative seed (Icc 0 horizon) low C paid
  exact ⟨low,D,D0,graph⟩
end
end SaturationMonoid.NavierStokes.NativeStageNineFullMatrixPotential
