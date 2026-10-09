import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Difference

/-! Compact source histories generate a common finite bound for the entire actual parameter family. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section

theorem window_distance (time first second : ℝ) (firstIn : first ∈ uIcc 0 time) (secondIn : second ∈ uIcc 0 time) :
    |second-first|≤|time| := by
  rcases le_total 0 time with forward | backward
  · rw [uIcc_of_le forward] at firstIn secondIn
    rw [abs_of_nonneg forward]
    exact abs_le.mpr ⟨by linarith [firstIn.1,firstIn.2,secondIn.1,secondIn.2],
      by linarith [firstIn.1,firstIn.2,secondIn.1,secondIn.2]⟩
  · rw [uIcc_of_ge backward] at firstIn secondIn
    rw [abs_of_nonpos backward]
    exact abs_le.mpr ⟨by linarith [firstIn.1,firstIn.2,secondIn.1,secondIn.2],
      by linarith [firstIn.1,firstIn.2,secondIn.1,secondIn.2]⟩

theorem window_integral_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (time M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 time, ‖f r‖≤M) (first second : ℝ)
    (firstIn : first ∈ uIcc 0 time) (secondIn : second ∈ uIcc 0 time) :
    ‖∫ r in first..second, f r‖≤|time| *M := by
  have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r hr => bounded r ((uIcc_subset_uIcc firstIn secondIn) (uIoc_subset_uIcc hr)))
  exact estimate.trans ((mul_le_mul_of_nonneg_left (window_distance time first second firstIn secondIn) nonnegative).trans_eq (mul_comm _ _))

def sourceMajorant (direction : ℝ → GaugeProfile) (coupling : ℝ)
    (scalar scalarDirection : ℝ → ScalarProfile) (time : ℝ) : ℝ :=
  ‖scalarDriftMap (scalar time)‖+‖scalarDriftMap (scalarDirection time)‖+
    ‖localForce (direction time) coupling (scalarDirection time)‖

theorem sourceMajorant_continuous (direction : ℝ → GaugeProfile) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection) :
    Continuous (sourceMajorant direction coupling scalar scalarDirection) :=
  ((scalarDriftMap.continuous.comp continuousScalar).norm.add
    (scalarDriftMap.continuous.comp continuousScalarDirection).norm).add
    (HistoryLaplace.localForce_continuous direction continuousDirection coupling scalarDirection continuousScalarDirection).norm

theorem source_window_bound (direction : ℝ → GaugeProfile) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection) (time : ℝ) :
    ∃ M, 0≤M ∧ ∀ r ∈ uIcc 0 time, sourceMajorant direction coupling scalar scalarDirection r≤M := by
  obtain ⟨M,bounded⟩ := (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) time)).exists_bound_of_continuousOn
    (sourceMajorant_continuous direction continuousDirection coupling scalar scalarDirection continuousScalar continuousScalarDirection).continuousOn
  refine ⟨max 0 M,le_max_left _ _,fun r hr => ?_⟩
  exact (le_abs_self _).trans ((bounded r hr).trans (le_max_right _ _))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
