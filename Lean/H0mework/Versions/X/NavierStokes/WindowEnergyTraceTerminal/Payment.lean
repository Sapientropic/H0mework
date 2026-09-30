import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Average

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWholeH1Mixed NativeWindowOperatorGreen
open NativeWindowTraceTerminalSynthesis (cap cap_positive)
open NativeWindowTraceTerminalOperator (stressNorm joint_bound)
open NativeWindowTraceTerminalAverage (stressSquare)
open NativeWindowConvectionCutoffTrace (correction)
open NativeWindowTraceCutOperator (jointTest)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowAugmentedGradientSource (palinstrophyWindow)
noncomputable section
variable {nu : Viscosity}

private theorem weighted_square (a b theta : ℝ) (positive : 0<theta) :
    (a+b)^2 ≤ (1+theta)*a^2+(1+theta⁻¹)*b^2 := by
  have same : theta*((1+theta)*a^2+(1+theta⁻¹)*b^2-(a+b)^2)=(theta*a-b)^2 := by
    field_simp
    ring
  have cost := sq_nonneg (theta*a-b)
  rw [← same] at cost
  have nonnegative := (mul_nonneg_iff_of_pos_left positive).mp cost
  linarith only [nonnegative]

def theta (epsilon : ℝ) : ℝ := min 1 (epsilon/8)

theorem theta_positive (epsilon : ℝ) (positive : 0<epsilon) : 0<theta epsilon := by
  unfold theta
  positivity

theorem theta_budget (epsilon : ℝ) (positive : 0<epsilon) : (1+theta epsilon)^3≤1+epsilon := by
  have zero := (theta_positive epsilon positive).le
  have one : theta epsilon≤1 := min_le_left _ _
  have upper : theta epsilon≤epsilon/8 := min_le_right _ _
  have square : (theta epsilon)^2≤theta epsilon := by nlinarith only [mul_nonneg zero (sub_nonneg.mpr one)]
  have cube : (theta epsilon)^3≤theta epsilon := by
    have first := mul_le_mul_of_nonneg_left square zero
    nlinarith only [first,square]
  nlinarith only [square,cube,upper,zero]

theorem source_point (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,
      ∀ M : Finset IntegerWavevector,∀ zero : 0∉M,∀ closed : FiniteModeNegClosed M,
      ∀ time∈Icc 0 horizon,∀ v : physicalSpace M,
        ‖coefficients M (jointTest seed time M (integerWaveFrequencyCube cutoff) radius v)‖^2≤
          (1+epsilon)*nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2+
            (1+(theta epsilon)⁻¹)*stressNorm seed time M (integerWaveFrequencyCube cutoff) v^2 := by
  let t:=theta epsilon
  have tPos : 0<t := theta_positive epsilon positive
  let delta:=nu.coeff*t/(9*(cap+1))
  have denominator : 0<9*(cap+1) := by positivity [cap_positive]
  have deltaPos : 0<delta := by dsimp only [delta]; positivity [nu.coeff_pos]
  obtain ⟨low,small⟩ := NativeWindowConvectionCutoffNormalForm.correctionJet_small seed 0 horizon nonnegative delta deltaPos
  refine ⟨low,fun radius above cutoff covered M zero closed time inside v => ?_⟩
  let F:=integerWaveFrequencyCube cutoff
  let D:=‖coefficients M (laplacian M zero closed nu v)‖
  let A:=stressNorm seed time M F v
  have Csmall : ‖correction seed F radius time‖≤3*delta := by
    apply (norm_sum_le _ _).trans
    have row (i : Coordinate) : ‖NativeWindowConvectionCutoffNormalForm.correction seed F radius time i i‖≤delta := by
      rw [← NativeWindowConvectionCutoffNormalForm.correctionJet_zero]
      exact (small radius above cutoff covered time inside i i).le
    exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by simp)
  have fraction : 3*cap*‖correction seed F radius time‖≤nu.coeff*t := by
    have same : delta*(9*(cap+1))=nu.coeff*t := div_mul_cancel₀ _ denominator.ne'
    have bound := mul_le_mul_of_nonneg_left Csmall (by positivity [cap_positive] : 0≤3*cap)
    nlinarith only [same,bound,deltaPos]
  have base := joint_bound seed time M F radius zero closed (NativeWindowFiniteGramFourier.cube_closed cutoff) v
  have bounded : ‖coefficients M (jointTest seed time M F radius v)‖≤nu.coeff*(1+t)*D+A := by
    have paid := mul_le_mul_of_nonneg_right fraction (norm_nonneg (coefficients M (laplacian M zero closed nu v)))
    dsimp only [D,A]
    nlinarith only [base,paid]
  have squared := pow_le_pow_left₀ (norm_nonneg _) bounded 2
  have young := weighted_square (nu.coeff*(1+t)*D) A t tPos
  have coefficient := mul_le_mul_of_nonneg_right (theta_budget epsilon positive) (by positivity : 0≤nu.coeff^2*D^2)
  change ‖coefficients M (jointTest seed time M F radius v)‖^2≤(1+epsilon)*nu.coeff^2*D^2+(1+t⁻¹)*A^2
  nlinarith only [squared,young,coefficient]


end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalPayment
