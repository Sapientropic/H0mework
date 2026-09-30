import H0mework.NavierStokes.UnheatedWriterTriad.WeightedSum
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.PrimitiveSource


set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadWeightedRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
noncomputable section
variable {nu : Viscosity}

theorem joint_row_integrable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (indices : IntegerWavevector × IntegerWavevector) :
    Integrable (NativeUnheatedTriadSource.jointRow seed wave i j response outside indices)
      (volume.restrict (Icc 0 horizon)) :=
  integrable_finsetSum _ (fun slot _ => NativeUnheatedTriadSource.row_integrable
    seed slot wave i j response outside indices horizon nonnegative)

theorem joint_row_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (time : ℝ) :
    Summable (fun indices => NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time) :=
  summable_sum (fun slot _ => (NativeUnheatedTriadSource.row_summable seed slot wave i j response outside time).of_norm)

theorem joint_row_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Summable (fun indices => ∫ time in Icc 0 horizon,
      ‖NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time‖) := by
  have generated := summable_sum (s := (Finset.univ : Finset (Fin 3))) (fun slot _ =>
    NativeUnheatedTriadSource.row_integrals_summable seed slot wave i j response outside horizon nonnegative)
  apply generated.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro indices
  rw [← integral_finsetSum _ (fun slot _ =>
    (NativeUnheatedTriadSource.row_integrable seed slot wave i j response outside indices horizon nonnegative).norm)]
  apply integral_mono (joint_row_integrable seed wave i j response outside horizon nonnegative indices).norm
    (integrable_finsetSum _ (fun slot _ =>
      (NativeUnheatedTriadSource.row_integrable seed slot wave i j response outside indices horizon nonnegative).norm))
  exact fun time => norm_sum_le _ _

theorem test_resources (horizon : ℝ) (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    AEStronglyMeasurable test (volume.restrict (Icc 0 horizon)) ∧
      ∃ cap : ℝ, ∀ᵐ time ∂volume.restrict (Icc 0 horizon), ‖test time‖ ≤ cap := by
  refine ⟨smooth.aestronglyMeasurable measurableSet_Icc, ?_⟩
  obtain ⟨cap, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn smooth
  exact ⟨cap, (ae_restrict_mem measurableSet_Icc).mono (fun time inside => bounded time inside)⟩

theorem joint_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    Summable (fun indices => ∫ time in Icc 0 horizon,
      test time • NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time) := by
  obtain ⟨measurable, cap, bounded⟩ := test_resources horizon test smooth
  exact NativeUnheatedTriadWeightedSum.integrals_summable _
    (joint_row_integrable seed wave i j response outside horizon nonnegative)
    (joint_row_integrals_summable seed wave i j response outside horizon nonnegative)
    test measurable cap bounded

theorem joint_weighted_fubini (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    (∫ time in Icc 0 horizon, test time • NativeUnheatedTriadSource.joint seed wave i j response outside time) =
      ∑' indices, ∫ time in Icc 0 horizon,
        test time • NativeUnheatedTriadSource.jointRow seed wave i j response outside indices time := by
  obtain ⟨measurable, cap, bounded⟩ := test_resources horizon test smooth
  simp_rw [NativeUnheatedTriadSource.joint_eq_tsum]
  exact NativeUnheatedTriadWeightedSum.weighted_integral_tsum _
    (joint_row_integrable seed wave i j response outside horizon nonnegative)
    (joint_row_integrals_summable seed wave i j response outside horizon nonnegative)
    test measurable cap bounded (Eventually.of_forall (joint_row_summable seed wave i j response outside))

theorem primitive_integrals_summable (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (_nonnegative : 0 ≤ horizon)
    (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    Summable (fun indices => ∫ time in Icc 0 horizon,
      test time • NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices time) := by
  obtain ⟨measurable, cap, bounded⟩ := test_resources horizon test smooth
  exact NativeUnheatedTriadWeightedSum.integrals_summable _
    (fun indices => NativeUnheatedTriadPrimitiveSource.row_integrable seed wave i j response outside indices 0 horizon)
    (NativeUnheatedTriadPrimitiveSource.row_integrals_summable seed wave i j response outside 0 horizon)
    test measurable cap bounded

theorem primitive_weighted_fubini (seed : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector)
    (i j response outside : Coordinate) (horizon : ℝ) (_nonnegative : 0 ≤ horizon)
    (test : ℝ → ℝ) (smooth : ContinuousOn test (Icc 0 horizon)) :
    (∫ time in Icc 0 horizon, test time • NativeUnheatedTriadPrimitiveSource.coefficient seed wave i j response outside time) =
      ∑' indices, ∫ time in Icc 0 horizon,
        test time • NativeUnheatedTriadPrimitiveSource.row seed wave i j response outside indices time := by
  obtain ⟨measurable, cap, bounded⟩ := test_resources horizon test smooth
  simp_rw [NativeUnheatedTriadPrimitiveSource.coefficient_eq_tsum]
  exact NativeUnheatedTriadWeightedSum.weighted_integral_tsum _
    (fun indices => NativeUnheatedTriadPrimitiveSource.row_integrable seed wave i j response outside indices 0 horizon)
    (NativeUnheatedTriadPrimitiveSource.row_integrals_summable seed wave i j response outside 0 horizon)
    test measurable cap bounded (Eventually.of_forall (fun time =>
      (NativeUnheatedTriadPrimitiveSource.row_summable seed wave i j response outside time).of_norm))

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadWeightedRows
