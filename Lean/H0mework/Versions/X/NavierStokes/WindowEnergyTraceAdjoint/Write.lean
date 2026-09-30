import H0mework.Versions.X.NavierStokes.WindowEnergyTraceAdjoint.Joint

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWholeH1Mixed NativeUnheatedGlobalNegativeOne NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity}

private def pairRead (M : ℕ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (LinearMap.toContinuousLinearMap (coefficients (modes M)))
    (LinearMap.toContinuousLinearMap (coefficients (modes M)))

private theorem pairRead_apply (M : ℕ) (x y : physicalSpace (modes M)) : pairRead M x y=pairing (modes M) x y := rfl

private theorem pair_ac (M : ℕ) {x y : ℝ →physicalSpace (modes M)} {a b : ℝ}
    (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => pairing (modes M) (x t) (y t)) a b := by
  have add:=diagonal_ac (pairRead M) (first.add last)
  have sub:=diagonal_ac (pairRead M) (first.sub last)
  have paid:=(add.sub sub).const_mul (1/4 : ℝ)
  convert! paid using 1
  funext t
  simp only [pairRead_apply,Pi.add_apply,Pi.sub_apply,map_add,map_sub,add_apply,sub_apply]
  rw [pairing_symmetric (modes M) (y t) (x t)]
  ring

private theorem pair_integrable (M : ℕ) {x y : ℝ →physicalSpace (modes M)} {a b : ℝ}
    (paid : IntervalIntegrable x volume a b) (continuous : ContinuousOn y (uIcc a b)) :
    IntervalIntegrable (fun t => pairing (modes M) (x t) (y t)) volume a b := by
  let read (k : IntegerWavevector) (i : Coordinate) : physicalSpace (modes M) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (NativeWindowAugmentedFixedOperator.rowRead (modes M) k i)
  have parts (k : IntegerWavevector) (i : Coordinate) (part : ℂ →L[ℝ] ℝ) :
      IntervalIntegrable (fun t => part (read k i (x t))*part (read k i (y t))) volume a b := by
    have first:IntervalIntegrable (fun t => (part.comp (read k i)) (x t)) volume a b :=
      ⟨(part.comp (read k i)).integrable_comp paid.1,(part.comp (read k i)).integrable_comp paid.2⟩
    exact first.mul_continuousOn ((part.comp (read k i)).continuous.comp_continuousOn continuous)
  have rows (k : IntegerWavevector) (i : Coordinate) := (parts k i Complex.reCLM).add (parts k i Complex.imCLM)
  have sums:=IntervalIntegrable.sum (s := modes M) fun k _ => IntervalIntegrable.sum (s := Finset.univ) fun i _ => rows k i
  convert! sums using 1
  funext t
  rw [pairing_eq]
  simp only [Finset.sum_apply]
  rfl

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) :
    IntervalIntegrable (NativeWindowStageNineSource.forcing seed M) volume a b := by
  have source:=(NativeUnheatedSourceWeightedTail.nonlinear_integrable seed (max a b) (a0.trans (le_max_left _ _))).sub
    (NativeUnheatedSourceQuadraticApprox.value_integrable M seed (max a b) (a0.trans (le_max_left _ _)))
  have mapped:IntegrableOn (NativeWindowStageNineSource.forcing seed M) (Icc 0 (max a b)) (volume : Measure ℝ) :=
    (NativeWindowStageNineSource.lift (modes M)).integrable_comp source
  have localPaid:IntegrableOn (NativeWindowStageNineSource.forcing seed M) (uIcc a b) (volume : Measure ℝ) :=
    mapped.mono_set (fun t ht => ⟨(le_min a0 b0).trans ht.1,ht.2⟩)
  exact localPaid.intervalIntegrable

theorem value_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (value seed M) a b := by
  apply dominated (NativeWindowHierarchyPairWindow.state_ac_total seed a b) ‖NativeWindowStageNineSource.lift (modes M)‖
  intro x _ y _
  rw [dist_eq_norm,dist_eq_norm,value,value,← map_sub]
  exact (NativeWindowStageNineSource.lift (modes M)).le_opNorm _

theorem propagated_source_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) :
    pairing (modes M) (value seed M finish) (joint seed observation M F radius finish)-
      pairing (modes M) (value seed M start) (propagated seed observation M F radius start finish ordered start)=
        ∫time in start..finish,pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
          (propagated seed observation M F radius start finish ordered time) := by
  have wAC:=backward_ac seed M start finish ordered (joint seed observation M F radius finish)
  have continuous:=wAC.continuousOn
  have integrable:=pair_integrable M (forcing_integrable seed M start finish nonnegative (nonnegative.trans ordered)) continuous
  have written:=integral_of_ac_derivative _ _ (pair_ac M (value_ac seed M start finish) wAC) integrable (by
    filter_upwards [propagated_source_green seed observation M F radius start finish ordered nonnegative,
      (volume : Measure ℝ).ae_ne start,(volume : Measure ℝ).ae_ne finish] with t actual left right inside
    rw [uIcc_of_le ordered] at inside
    exact actual ⟨lt_of_le_of_ne inside.1 (Ne.symm left),lt_of_le_of_ne inside.2 right⟩)
  change pairing (modes M) (value seed M finish) (propagated seed observation M F radius start finish ordered finish)-
    pairing (modes M) (value seed M start) (propagated seed observation M F radius start finish ordered start)=_ at written
  rw [propagated,backward_terminal] at written
  exact written

theorem joint_ac (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) : AbsolutelyContinuousOnInterval (joint seed observation M F radius) a b := by
  let T:=LinearMap.toContinuousLinearMap (NativeWindowTraceOperator.jointTest seed observation (modes M) F radius)
  apply dominated (value_ac seed M a b) ‖T‖
  intro x _ y _
  change dist (T (value seed M x)) (T (value seed M y))≤_
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact T.le_opNorm _

theorem responseRate_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) : IntervalIntegrable (responseRate seed observation M F radius) volume a b := by
  let T:=LinearMap.toContinuousLinearMap (NativeWindowTraceOperator.jointTest seed observation (modes M) F radius)
  have first:Continuous (fun t => T (forward seed M t (value seed M t))) :=
    T.continuous.comp ((forward_continuous seed M).clm_apply (value_continuous seed M))
  have second:Continuous (fun t => dual seed M t (joint seed observation M F radius t)) :=
    (dual_continuous seed M).clm_apply (T.continuous.comp (value_continuous seed M))
  have last:IntervalIntegrable (fun t => T (NativeWindowStageNineSource.forcing seed M t)) volume a b :=
    ⟨T.integrable_comp (forcing_integrable seed M a b a0 b0).1,T.integrable_comp (forcing_integrable seed M a b a0 b0).2⟩
  exact ((first.intervalIntegrable a b).add (second.intervalIntegrable a b)).add last

theorem response_ac (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) :
    AbsolutelyContinuousOnInterval (response seed observation M F radius start finish ordered) start finish :=
  (joint_ac seed observation M F radius start finish).sub (backward_ac seed M start finish ordered _)

theorem response_source_write (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) :
    -pairing (modes M) (value seed M start) (response seed observation M F radius start finish ordered start)=
      ∫time in start..finish,pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
        (response seed observation M F radius start finish ordered time)+
          pairing (modes M) (value seed M time) (responseRate seed observation M F radius time) := by
  have errorAC:=response_ac seed observation M F radius start finish ordered
  have first:=pair_integrable M (forcing_integrable seed M start finish nonnegative (nonnegative.trans ordered)) errorAC.continuousOn
  have last:IntervalIntegrable (fun t => pairing (modes M) (value seed M t) (responseRate seed observation M F radius t)) volume start finish := by
    simpa only [pairing_symmetric (modes M)] using pair_integrable M
      (responseRate_integrable seed observation M F radius start finish nonnegative (nonnegative.trans ordered))
        (value_continuous seed M).continuousOn
  have written:=integral_of_ac_derivative _ _ (pair_ac M (value_ac seed M start finish) errorAC) (first.add last) (by
    filter_upwards [response_source_green seed observation M F radius start finish ordered nonnegative,
      (volume : Measure ℝ).ae_ne start,(volume : Measure ℝ).ae_ne finish] with t actual left right inside
    rw [uIcc_of_le ordered] at inside
    exact actual ⟨lt_of_le_of_ne inside.1 (Ne.symm left),lt_of_le_of_ne inside.2 right⟩)
  rw [response_terminal,map_zero,zero_sub] at written
  exact written

theorem value_mass_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0≤time) :
    ‖coefficients (modes M) (value seed M time)‖≤NativeUnifiedCompleteSource.budget seed := by
  rw [value,NativeWindowStageNineSource.lift_load seed time nonnegative]
  apply (NativeWholeResolvent.restrict_energy (modes M) (modes_zero M) (modes_closed M)
    (NativeUnheatedSourceQuadraticApprox.physicalSource seed time)).trans
  rw [NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
  exact NativeUnheatedSourceWeightedTail.velocity_bound seed time

theorem propagated_work_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (nonnegative : 0 ≤ start) :
    |∫time in start..finish,pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
      (propagated seed observation M F radius start finish ordered time)|≤
        2*NativeUnifiedCompleteSource.budget seed*‖coefficients (modes M) (joint seed observation M F radius finish)‖ := by
  rw [← propagated_source_write seed observation M F radius start finish ordered nonnegative]
  have boundA:=value_mass_bound seed M start nonnegative
  have boundB:=value_mass_bound seed M finish (nonnegative.trans ordered)
  have testBound:=propagated_mass_bound seed observation M F radius start finish ordered start (left_mem_Icc.mpr ordered)
  have B0:0≤NativeUnifiedCompleteSource.budget seed := (norm_nonneg _).trans boundA
  have first:|pairing (modes M) (value seed M finish) (joint seed observation M F radius finish)|≤
      NativeUnifiedCompleteSource.budget seed*‖coefficients (modes M) (joint seed observation M F radius finish)‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right boundB (norm_nonneg _))
  have last:|pairing (modes M) (value seed M start) (propagated seed observation M F radius start finish ordered start)|≤
      NativeUnifiedCompleteSource.budget seed*‖coefficients (modes M) (joint seed observation M F radius finish)‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul boundA testBound (norm_nonneg _) B0)
  exact (abs_sub _ _).trans ((add_le_add first last).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeWindowTraceAdjoint
