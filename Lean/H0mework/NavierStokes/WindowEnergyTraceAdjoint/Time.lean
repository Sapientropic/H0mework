import H0mework.NavierStokes.WindowEnergyTraceAdjoint.Source

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint
open PhysicsCore.StageNineDiracMatterGalerkinEvolution
noncomputable section
variable {nu : Viscosity}

theorem exists_backward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ)
    (ordered : start≤finish) (terminal : physicalSpace (modes M)) :
    ∃ curve : ℝ → physicalSpace (modes M),curve finish=terminal ∧∀ time∈Icc start finish,
      HasDerivWithinAt curve (-dual seed M time (curve time)) (Icc start finish) time := by
  obtain ⟨curve,initial,evolution⟩ := exists_galerkinLinearCoefficientCurve_on_Icc
    (fun elapsed => dual seed M (finish-elapsed)) ((dual_continuous seed M).comp (continuous_const.sub continuous_id))
    terminal 0 (finish-start) (by linarith)
  refine ⟨fun time => curve (finish-time),by simpa using initial,fun time inside => ?_⟩
  have maps : MapsTo (fun time : ℝ => finish-time) (Icc start finish) (Icc 0 (finish-start)) := by
    intro t ht; constructor <;> linarith [ht.1,ht.2]
  have path : HasDerivWithinAt (fun t : ℝ => finish-t) (-1) (Icc start finish) time := by
    simpa only [Pi.sub_apply,id_eq,zero_sub] using! ((hasDerivAt_const time finish).sub (hasDerivAt_id time)).hasDerivWithinAt
  have source := (evolution (finish-time) (maps inside)).scomp time path maps
  simpa only [galerkinLinearVelocity,sub_sub_cancel,neg_smul,one_smul,Function.comp_def] using! source

def backward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) : ℝ → physicalSpace (modes M) :=
  (exists_backward seed M start finish ordered terminal).choose

theorem backward_terminal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) : backward seed M start finish ordered terminal finish=terminal :=
  (exists_backward seed M start finish ordered terminal).choose_spec.1

theorem backward_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    HasDerivWithinAt (backward seed M start finish ordered terminal)
      (-dual seed M time (backward seed M start finish ordered terminal time)) (Icc start finish) time :=
  (exists_backward seed M start finish ordered terminal).choose_spec.2 time inside

theorem backward_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) : ContinuousOn (backward seed M start finish ordered terminal) (Icc start finish) :=
  fun time inside => (backward_derivative seed M start finish ordered terminal time inside).continuousWithinAt

theorem backward_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) :
    terminal-backward seed M start finish ordered terminal start=
      ∫time in start..finish,-dual seed M time (backward seed M start finish ordered terminal time) := by
  let curve:=backward seed M start finish ordered terminal
  have continuous : ContinuousOn curve (Icc start finish) := backward_continuous seed M start finish ordered terminal
  have ratePaid : IntervalIntegrable (fun time => -dual seed M time (curve time)) volume start finish := by
    have paid := ((dual_continuous seed M).continuousOn.clm_apply continuous).neg
    rw [← uIcc_of_le ordered] at paid
    exact paid.intervalIntegrable
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered continuous
    (fun time inside => (backward_derivative seed M start finish ordered terminal time (Ioo_subset_Icc_self inside)).hasDerivAt
      (Icc_mem_nhds inside.1 inside.2)) ratePaid
  dsimp only [curve] at written
  rw [backward_terminal] at written
  exact written.symm

theorem backward_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) : AbsolutelyContinuousOnInterval (backward seed M start finish ordered terminal) start finish := by
  let curve:=backward seed M start finish ordered terminal
  let rate:=fun time => -dual seed M time (curve time)
  have cont : ContinuousOn curve (Icc start finish) := backward_continuous seed M start finish ordered terminal
  have rateCont : ContinuousOn rate (Icc start finish) := ((dual_continuous seed M).continuousOn.clm_apply cont).neg
  have write (x y : ℝ) (xin : x∈Icc start finish) (yin : y∈Icc start finish) (xy : x≤y) :
      curve y-curve x=∫t in x..y,rate t := by
    have subset : Icc x y⊆Icc start finish := Icc_subset_Icc xin.1 yin.2
    have ratePaid := rateCont.mono subset
    rw [← uIcc_of_le xy] at ratePaid
    apply (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le xy (cont.mono subset) _ ratePaid.intervalIntegrable).symm
    intro t ht
    exact ((backward_derivative seed M start finish ordered terminal t (subset (Ioo_subset_Icc_self ht))).mono subset).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  apply NativeUnheatedIntegralBilinear.written_ac curve rate
    (by rw [← uIcc_of_le ordered] at rateCont; exact rateCont.intervalIntegrable)
  intro x xin y yin
  rw [uIcc_of_le ordered] at xin yin
  by_cases xy : x≤y
  · exact write x y xin yin xy
  · rw [intervalIntegral.integral_symm,← write y x yin xin (le_of_not_ge xy)]
    abel

theorem backward_energy_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    HasDerivWithinAt (fun t => ‖coefficients (modes M) (backward seed M start finish ordered terminal t)‖^2)
      (2*nu.coeff*curlPair (modes M) (backward seed M start finish ordered terminal time).1
        (backward seed M start finish ordered terminal time).1) (Icc start finish) time := by
  have generated := ((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivWithinAt time
    (backward_derivative seed M start finish ordered terminal time inside)).norm_sq
  have sign := physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu
    (-advector seed M time) (negative_reality (advector_reality seed M time)) (backward seed M start finish ordered terminal time)
  change inner ℝ (coefficients (modes M) _) (coefficients (modes M) (dual seed M time _))=
    -nu.coeff*curlPair (modes M) _ _ at sign
  convert! generated using 1
  simp only [map_neg,inner_neg_right,Function.comp_def]
  change 2*nu.coeff*curlPair (modes M) _ _=2*(-inner ℝ (coefficients (modes M) _)
    (coefficients (modes M) (dual seed M time _)))
  rw [sign]
  ring

theorem backward_mass_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (start finish : ℝ) (ordered : start≤finish)
    (terminal : physicalSpace (modes M)) (time : ℝ) (inside : time∈Icc start finish) :
    ‖coefficients (modes M) (backward seed M start finish ordered terminal time)‖≤‖coefficients (modes M) terminal‖ := by
  let curve:=backward seed M start finish ordered terminal
  have continuous : ContinuousOn (fun t => ‖coefficients (modes M) (curve t)‖^2) (Icc start finish) :=
    (((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
      (backward_continuous seed M start finish ordered terminal)).norm.pow 2)
  have mono : MonotoneOn (fun t => ‖coefficients (modes M) (curve t)‖^2) (Icc start finish) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc start finish) continuous
    · intro t ht
      rw [interior_Icc] at ht
      exact ((backward_energy_derivative seed M start finish ordered terminal t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [((backward_energy_derivative seed M start finish ordered terminal t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).deriv]
      apply mul_nonneg (by positivity [nu.coeff_pos])
      exact Finset.sum_nonneg fun k _ => by rw [complexCoordinateRealInner_self]; exact complexCoordinateVectorNormSq_nonneg _
  have bound := mono inside (right_mem_Icc.mpr ordered) inside.2
  change ‖coefficients (modes M) (curve time)‖^2≤‖coefficients (modes M) (curve finish)‖^2 at bound
  rw [show curve finish=terminal from backward_terminal seed M start finish ordered terminal] at bound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp bound

end
end SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
