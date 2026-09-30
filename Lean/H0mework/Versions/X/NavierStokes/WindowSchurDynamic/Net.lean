import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianViscous

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicNet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse temporalBudget)
open NativeWindowHistoryCommonResponse (response)
open NativeWindowHistoryCommonForceBounds (budget)
open NativeWindowHistoryJacobianControl (form)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistoryJacobianViscous (commutatorWork retainedWork)
noncomputable section
variable {nu : Viscosity}

theorem common_work_form (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    NativeWindowHistoryCommonResponseWork.work seed M order time=
      2*form nu M (temporalResponse seed M time) (response seed M order time) := by
  have first := congrArg (2*·) (NativeWindowHistoryCommonResponseWork.principal_pairing nu M
    (temporalResponse seed M time) (response seed M order time))
  exact first.trans (congrArg (fun v : H => 2*inner ℝ (temporalResponse seed M time)
    (v+nu.coeff • laplacianAction nu M (response seed M order time)))
    (NativeWindowHistoryCommonResponse.response_projected seed M order time))

theorem source_common_work_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    |NativeWindowHistoryCommonResponseWork.work seed M order time|≤temporalBudget seed horizon+budget seed horizon order := by
  have first := NativeWindowHistoryJacobianControl.form_young seed M (temporalResponse seed M time) (response seed M order time) 1
  have last := NativeWindowHistoryJacobianControl.form_young seed M (temporalResponse seed M time) (response seed M order time) (-1)
  have w := NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have y := NativeWindowHistoryDynamicResponse.source_energy seed horizon M order time inside
  rw [common_work_form]
  apply abs_le.mpr
  constructor <;> nlinarith only [first,last,w,y]

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      NativeWindowHistoryDynamicEnergy.sourceRate seed M time≤
        -nu.coeff^2*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C+
          commutatorWork seed M time (temporalResponse seed M time)+retainedWork seed M time := by
  obtain ⟨first,B,B0,diagonalPaid⟩ := NativeWindowHistoryJacobianViscous.source_diagonal seed horizon nonnegative
  obtain ⟨last,A,A0,reactionPaid⟩ := NativeWindowHistoryDynamicResponse.source_reaction_bound seed horizon nonnegative
  refine ⟨max first last,B+A+temporalBudget seed horizon+budget seed horizon 1,?_,?_⟩
  · exact add_nonneg (add_nonneg (add_nonneg B0 A0)
      (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon))
      (NativeWindowHistoryCommonForceBounds.budget_nonnegative seed horizon 1)
  · intro M above time inside
    have diagonal := diagonalPaid M ((le_max_left _ _).trans above) time inside
    have reaction := (le_abs_self _).trans (reactionPaid M ((le_max_right _ _).trans above) time inside)
    have common := (neg_le_abs _).trans (source_common_work_bound seed horizon M 1 time inside)
    have actual := NativeWindowHistoryDynamicEnergy.sourceRate_original seed M time
    have joint := NativeWindowHistoryJacobianViscous.joint_split seed M time
    have split := NativeWindowHistoryJacobianViscous.reaction_split seed M time
    linarith only [diagonal,reaction,common,actual,joint,split]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicNet
