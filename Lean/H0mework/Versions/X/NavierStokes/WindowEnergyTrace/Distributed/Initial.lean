import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Response
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedInitialForce

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowDistributedAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward dual)
noncomputable section
variable {nu : Viscosity}

open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeWindowTraceDualEvolution (mass lifted energy)

theorem source_initial_mass_bound (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ‖coefficients (modes M)
        (mass stackedShortCurrent M
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius)
          radius 0 (value stackedShortCurrent M 0))‖ ≤ C := by
  obtain ⟨low,D,D0,potential⟩ := NativeDistributedLyapunov.source_potential_relative
    stackedShortCurrent horizon nonnegative 1 zero_lt_one
  let B := NativeUnifiedCompleteSource.budget stackedShortCurrent
  let A := 3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0]+1
  have B0 : 0 ≤ B := (norm_nonneg _).trans
    (NativeWindowTraceAdjoint.value_mass_bound stackedShortCurrent 0 0 le_rfl)
  have cap0 : 0 ≤ 3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] :=
    (sq_nonneg _).trans (NativeStageNinePreparedInitialForce.initial_physical_laplacian_bound 0)
  have A0 : 0 ≤ A := by dsimp only [A]; linarith
  refine ⟨low,(1+D)*B+(butterflyGainViscosity.coeff+1)*A,
    by positivity [butterflyGainViscosity.coeff_pos],fun radius above outerRadius M => ?_⟩
  let u := value stackedShortCurrent M 0
  let L := testAction (nu := butterflyGainViscosity) M u
  let P := NativeDistributedLyapunov.potential stackedShortCurrent M
    (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius) radius 0 u
  have source := NativeWindowTraceAdjoint.value_mass_bound stackedShortCurrent M 0 le_rfl
  have graph : ‖coefficients (modes M) L‖ ≤ A := by
    have paid := NativeStageNinePreparedInitialForce.initial_physical_laplacian_bound M
    change ‖coefficients (modes M) L‖^2 ≤ _ at paid
    dsimp only [A]
    nlinarith only [paid,sq_nonneg (‖coefficients (modes M) L‖-1),cap0]
  have relative := potential radius above outerRadius M 0 ⟨le_rfl,nonnegative⟩ u
  change ‖coefficients (modes M) P‖ ≤ 1*‖coefficients (modes M) L‖+D*‖coefficients (modes M) u‖ at relative
  change ‖coefficients (modes M) u‖ ≤ B at source
  rw [NativeDistributedLyapunov.mass_split]
  simp only [map_add,map_smul]
  have first := norm_add_le (coefficients (modes M) u)
    (butterflyGainViscosity.coeff • coefficients (modes M) L)
  have last := norm_add_le
    (coefficients (modes M) u+butterflyGainViscosity.coeff • coefficients (modes M) L)
    (coefficients (modes M) P)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos butterflyGainViscosity.coeff_pos] at first
  change ‖coefficients (modes M) u+butterflyGainViscosity.coeff • coefficients (modes M) L+
    coefficients (modes M) P‖ ≤ _
  have scaledSource := mul_le_mul_of_nonneg_left source D0
  have scaledGraph := mul_le_mul_of_nonneg_left graph butterflyGainViscosity.coeff_pos.le
  linarith only [last,first,relative,source,graph,scaledSource,scaledGraph]

theorem source_initial_pair_paid (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M,
      ∀ w : physicalSpace (modes M),
      |pairing (modes M) (value stackedShortCurrent M 0) w| ≤
        epsilon * energy stackedShortCurrent M
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius)
          radius 0 w + C := by
  obtain ⟨first,B,B0,bounded⟩ := source_initial_mass_bound horizon nonnegative
  obtain ⟨last,Ct,Ct0,controlled⟩ := NativeWindowTraceDualEvolution.source_control
    stackedShortCurrent horizon nonnegative
  obtain ⟨liftLow,liftBound⟩ := NativeDistributedLyapunov.source_lifted_control
    stackedShortCurrent horizon nonnegative
  refine ⟨max first (max last liftLow),B^2/(4*epsilon),by positivity,
    fun radius above outerRadius M w => ?_⟩
  let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let u := value stackedShortCurrent M 0
  let z := lifted stackedShortCurrent M F radius 0 w
  have actual := (controlled radius ((le_max_left last liftLow).trans ((le_max_right first _).trans above))
    outerRadius M 0 ⟨le_rfl,nonnegative⟩).1
  have restore : mass stackedShortCurrent M F radius 0 z = w := actual.self_apply_inverse w
  have paired : pairing (modes M) u w =
      pairing (modes M) z (mass stackedShortCurrent M F radius 0 u) := by
    rw [← restore,NativeWindowTraceDualEvolution.mass_symmetric]
  have cap := bounded radius ((le_max_left first _).trans above) outerRadius M
  have cost := liftBound radius ((le_max_right last liftLow).trans ((le_max_right first _).trans above))
    outerRadius M 0 ⟨le_rfl,nonnegative⟩ w
  have estimate := (abs_real_inner_le_norm (coefficients (modes M) z)
    (coefficients (modes M) (mass stackedShortCurrent M F radius 0 u))).trans
      (mul_le_mul_of_nonneg_left cap (norm_nonneg _))
  change |pairing (modes M) z (mass stackedShortCurrent M F radius 0 u)| ≤
    ‖coefficients (modes M) z‖*B at estimate
  change ‖coefficients (modes M) z‖^2 ≤ energy stackedShortCurrent M F radius 0 w at cost
  have square : 0 ≤ epsilon*‖coefficients (modes M) z‖^2 + B^2/(4*epsilon)-‖coefficients (modes M) z‖*B := by
    have identity : epsilon*‖coefficients (modes M) z‖^2+B^2/(4*epsilon)-‖coefficients (modes M) z‖*B =
        (2*epsilon*‖coefficients (modes M) z‖-B)^2/(4*epsilon) := by
      field_simp [positive.ne']
      ring
    rw [identity]
    positivity
  rw [show value stackedShortCurrent M 0=u from rfl,paired]
  have scaled := mul_le_mul_of_nonneg_left cost positive.le
  linarith only [estimate,square,scaled]

end
end SaturationMonoid.NavierStokes.NativeWindowDistributedAdjoint
