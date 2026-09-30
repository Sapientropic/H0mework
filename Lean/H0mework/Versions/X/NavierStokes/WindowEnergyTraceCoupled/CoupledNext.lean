import H0mework.Versions.X.NavierStokes.WindowEnergyTraceCoupled.Write

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowTraceAdjoint (value forward dual backward propagated)
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
noncomputable section
variable {nu : Viscosity}

private theorem unique_backward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) (ab : a≤b)
    {x y : ℝ →physicalSpace (modes M)}
    (first : ∀ t∈Icc a b,HasDerivWithinAt x (-dual seed M t (x t)) (Icc a b) t)
    (last : ∀ t∈Icc a b,HasDerivWithinAt y (-dual seed M t (y t)) (Icc a b) t)
    (terminal : x b=y b) : EqOn x y (Icc a b) := by
  let d:=fun t => x t-y t
  have derivative (t : ℝ) (inside : t∈Icc a b) : HasDerivWithinAt d (-dual seed M t (d t)) (Icc a b) t := by
    have actual:=(first t inside).sub (last t inside)
    change HasDerivWithinAt d (-dual seed M t (x t)- -dual seed M t (y t)) (Icc a b) t at actual
    convert actual using 1
    simp only [d,map_sub]
    abel
  have energyDerivative (t : ℝ) (inside : t∈Icc a b) :
      HasDerivWithinAt (fun t => ‖coefficients (modes M) (d t)‖^2)
        (2*nu.coeff*curlPair (modes M) (d t).1 (d t).1) (Icc a b) t := by
    have actual:=((LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivWithinAt t
      (derivative t inside)).norm_sq
    have sign:=physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu
      (-NativeWindowTraceAdjoint.advector seed M t) (negative_reality (NativeWindowTraceAdjoint.advector_reality seed M t)) (d t)
    change inner ℝ (coefficients (modes M) _) (coefficients (modes M) (dual seed M t _))=
      -nu.coeff*curlPair (modes M) _ _ at sign
    convert! actual using 1
    simp only [map_neg,inner_neg_right,Function.comp_def]
    change 2*nu.coeff*curlPair (modes M) _ _=2*(-inner ℝ (coefficients (modes M) _)
      (coefficients (modes M) (dual seed M t _)))
    rw [sign]
    ring
  have monotone:MonotoneOn (fun t => ‖coefficients (modes M) (d t)‖^2) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (fun t ht => (energyDerivative t ht).continuousWithinAt)
    · intro t ht
      rw [interior_Icc] at ht
      exact ((energyDerivative t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [((energyDerivative t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      exact mul_nonneg (by positivity [nu.coeff_pos]) (Finset.sum_nonneg fun k _ => by
        rw [complexCoordinateRealInner_self]; exact complexCoordinateVectorNormSq_nonneg _)
  intro t ht
  have estimate:=monotone ht (right_mem_Icc.mpr ab) ht.2
  change ‖coefficients (modes M) (d t)‖^2≤‖coefficients (modes M) (d b)‖^2 at estimate
  have endZero:d b=0 := sub_eq_zero.mpr terminal
  rw [endZero,map_zero,norm_zero,zero_pow (by norm_num)] at estimate
  have zero:coefficients (modes M) (d t)=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (coefficients (modes M) (d t))])
  apply coefficients_injective (modes M)
  exact sub_eq_zero.mp (by simpa only [d,map_sub] using zero)

theorem backward_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ)
    (start finish : ℝ) (ordered : start≤finish) (start0 : 0 ≤ start) (terminal : physicalSpace (modes M)) :
    EqOn (fun time => backward seed M (step.2.clockAdvance+start) (step.2.clockAdvance+finish)
      (by linarith) terminal (step.2.clockAdvance+time)) (backward step.1 M start finish ordered terminal) (Icc start finish) := by
  apply unique_backward step.1 M start finish ordered
  · intro t ht
    have maps:MapsTo (fun t : ℝ => step.2.clockAdvance+t) (Icc start finish)
        (Icc (step.2.clockAdvance+start) (step.2.clockAdvance+finish)) := by
      intro s hs; constructor <;> linarith [hs.1,hs.2]
    have path:HasDerivWithinAt (fun t : ℝ => step.2.clockAdvance+t) 1 (Icc start finish) t := by
      simpa only [zero_add] using! ((hasDerivAt_const t step.2.clockAdvance).add (hasDerivAt_id t)).hasDerivWithinAt
    have actual:=(NativeWindowTraceAdjoint.backward_derivative seed M (step.2.clockAdvance+start)
      (step.2.clockAdvance+finish) (by linarith) terminal (step.2.clockAdvance+t) (maps ht)).scomp t path maps
    have operator:=congrArg (fun tuple => tuple.2.2) (NativeWindowTraceAdjoint.source_next seed M step generated t (start0.trans ht.1))
    change dual seed M (step.2.clockAdvance+t)=dual step.1 M t at operator
    simp only [one_smul,Function.comp_def] at actual
    rw [operator] at actual
    exact actual
  · exact NativeWindowTraceAdjoint.backward_derivative step.1 M start finish ordered terminal
  · simp only [NativeWindowTraceAdjoint.backward_terminal]

theorem propagated_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (observation start finish : ℝ) (observed : 0≤observation) (ordered : start≤finish) (start0 : 0 ≤ start) :
    EqOn (fun time => propagated seed (step.2.clockAdvance+observation) M F radius
      (step.2.clockAdvance+start) (step.2.clockAdvance+finish) (by linarith) (step.2.clockAdvance+time))
      (propagated step.1 observation M F radius start finish ordered) (Icc start finish) := by
  have terminal:=congrArg Prod.fst (NativeWindowTraceAdjoint.source_next seed M step generated finish (start0.trans ordered))
  change value seed M (step.2.clockAdvance+finish)=value step.1 M finish at terminal
  simp only [propagated,NativeWindowTraceAdjoint.joint,
    NativeWindowTraceOperatorAction.jointTest_next seed step generated observation observed,terminal]
  exact backward_next seed step generated M start finish ordered start0 _

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (observation start finish : ℝ) (observed : 0≤observation) (ordered : start≤finish) (start0 : 0 ≤ start)
    (time : ℝ) (inside : time∈Icc start finish) :
    (combined seed (step.2.clockAdvance+observation) M F radius (step.2.clockAdvance+start) (step.2.clockAdvance+finish)
        (by linarith) (step.2.clockAdvance+time),
      energy seed (step.2.clockAdvance+observation) M F radius (step.2.clockAdvance+start) (step.2.clockAdvance+finish)
        (by linarith) (step.2.clockAdvance+time))=
      (combined step.1 observation M F radius start finish ordered time,energy step.1 observation M F radius start finish ordered time) := by
  have history:=propagated_next seed step generated M F radius observation start finish observed ordered start0 inside
  have source:=congrArg Prod.fst (NativeWindowTraceAdjoint.source_next seed M step generated time (start0.trans inside.1))
  change value seed M (step.2.clockAdvance+time)=value step.1 M time at source
  have original:combined seed (step.2.clockAdvance+observation) M F radius (step.2.clockAdvance+start) (step.2.clockAdvance+finish)
      (by linarith) (step.2.clockAdvance+time)=combined step.1 observation M F radius start finish ordered time := by
    simp only [combined,history,source]
  simp only [original,energy,NativeWindowTraceDualEvolution.energy_next seed M F radius step generated observation observed]

theorem response_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (observation start finish : ℝ) (observed : 0≤observation) (ordered : start≤finish) (start0 : 0 ≤ start) :
    EqOn (fun time => NativeWindowTraceAdjoint.response seed (step.2.clockAdvance+observation) M F radius
      (step.2.clockAdvance+start) (step.2.clockAdvance+finish) (by linarith) (step.2.clockAdvance+time))
      (NativeWindowTraceAdjoint.response step.1 observation M F radius start finish ordered) (Icc start finish) := by
  intro time inside
  have history:=propagated_next seed step generated M F radius observation start finish observed ordered start0 inside
  have source:=congrArg Prod.fst (NativeWindowTraceAdjoint.source_next seed M step generated time (start0.trans inside.1))
  change value seed M (step.2.clockAdvance+time)=value step.1 M time at source
  simp only [NativeWindowTraceAdjoint.response,NativeWindowTraceAdjoint.joint,
    NativeWindowTraceOperatorAction.jointTest_next seed step generated observation observed,source,history]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCoupled
