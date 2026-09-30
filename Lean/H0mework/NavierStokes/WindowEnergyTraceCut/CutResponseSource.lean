import H0mework.NavierStokes.WindowEnergyTraceEndpoint.Window
import H0mework.NavierStokes.WindowEnergyTraceAdjoint.Write

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint NativeUnheatedIntegralBilinear
open NativeWindowTraceAdjoint (value forward dual backward)
open NativeWindowTraceEndpointWindow (terminal terminal_continuous)
open NativeWindowTraceCutOperator (jointTest)
noncomputable section
variable {nu : Viscosity}

def forcing (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  jointTest seed frame (modes M) F radius (forward seed M time (value seed M time))+
    dual seed M time (terminal seed frame M F radius time)+
      jointTest seed frame (modes M) F radius (NativeWindowStageNineSource.forcing seed M time)

def response (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (time : ℝ) : physicalSpace (modes M) :=
  terminal seed frame M F radius time-backward seed M a b ab (terminal seed frame M F radius b) time

theorem terminal_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) : ∀ᵐ time : ℝ,HasDerivAt (terminal seed frame M F radius)
      (jointTest seed frame (modes M) F radius (NativeWindowStageNineSource.lift (modes M) (NativeUnheatedGlobalNegativeOne.rate seed time))) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed] with time actual
  exact (LinearMap.toContinuousLinearMap (jointTest seed frame (modes M) F radius)).hasFDerivAt.comp_hasDerivAt time
    ((NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual)

theorem response_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) : ∀ᵐ time : ℝ,time∈Ioo a b →
      HasDerivAt (response seed frame M F radius a b ab)
        (forcing seed frame M F radius time-dual seed M time (response seed frame M F radius a b ab time)) time := by
  filter_upwards [terminal_derivative seed frame M F radius,NativeWindowTraceAdjoint.source_action_ae seed M]
    with time derivative actual inside
  have backwardDerivative:=(NativeWindowTraceAdjoint.backward_derivative seed M a b ab (terminal seed frame M F radius b)
    time (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  have source:=derivative.sub backwardDerivative
  rw [actual (a0.trans inside.1.le)] at source
  convert! source using 1
  simp only [forcing,response,map_add,map_sub,terminal]
  abel

theorem terminal_ac (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) : AbsolutelyContinuousOnInterval (terminal seed frame M F radius) a b := by
  let T:=LinearMap.toContinuousLinearMap (jointTest seed frame (modes M) F radius)
  apply dominated (NativeWindowTraceAdjoint.value_ac seed M a b) ‖T‖
  intro x _ y _
  change dist (T (value seed M x)) (T (value seed M y))≤_
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact T.le_opNorm _

theorem response_ac (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) : AbsolutelyContinuousOnInterval (response seed frame M F radius a b ab) a b :=
  (terminal_ac seed frame M F radius a b).sub (NativeWindowTraceAdjoint.backward_ac seed M a b ab _)

theorem response_terminal (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) : response seed frame M F radius a b ab b=0 := by
  rw [response,NativeWindowTraceAdjoint.backward_terminal,sub_self]

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (a0 : 0≤a) (b0 : 0≤b) : IntervalIntegrable (forcing seed frame M F radius) volume a b := by
  let T:=LinearMap.toContinuousLinearMap (jointTest seed frame (modes M) F radius)
  have first:Continuous (fun t => T (forward seed M t (value seed M t))) :=
    T.continuous.comp ((NativeWindowTraceAdjoint.forward_continuous seed M).clm_apply (NativeWindowTraceAdjoint.value_continuous seed M))
  have second:Continuous (fun t => dual seed M t (terminal seed frame M F radius t)) :=
    (NativeWindowTraceAdjoint.dual_continuous seed M).clm_apply (terminal_continuous seed frame M F radius)
  have last:IntervalIntegrable (fun t => T (NativeWindowStageNineSource.forcing seed M t)) volume a b :=
    ⟨T.integrable_comp (NativeWindowTraceAdjoint.forcing_integrable seed M a b a0 b0).1,
      T.integrable_comp (NativeWindowTraceAdjoint.forcing_integrable seed M a b a0 b0).2⟩
  exact ((first.intervalIntegrable a b).add (second.intervalIntegrable a b)).add last

theorem dual_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    pairing (modes M) v (dual seed M time v)= -nu.coeff*curlPair (modes M) v.1 v.1 :=
  physicalOperator_pairing (modes M) (modes_zero M) (modes_closed M) nu (-NativeWindowTraceAdjoint.advector seed M time)
    (negative_reality (NativeWindowTraceAdjoint.advector_reality seed M time)) v

def work (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (time : ℝ) : ℝ :=
  pairing (modes M) (forcing seed frame M F radius time) (response seed frame M F radius a b ab time)

def dissipation (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (time : ℝ) : ℝ :=
  curlPair (modes M) (response seed frame M F radius a b ab time).1 (response seed frame M F radius a b ab time).1

def energy (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (time : ℝ) : ℝ :=
  (1/2 : ℝ)*‖coefficients (modes M) (response seed frame M F radius a b ab time)‖^2

theorem dissipation_nonnegative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (time : ℝ) : 0≤dissipation seed frame M F radius a b ab time :=
  Finset.sum_nonneg fun k _ => by rw [complexCoordinateRealInner_self]; exact complexCoordinateVectorNormSq_nonneg _

theorem dissipation_integrable (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) : IntervalIntegrable (dissipation seed frame M F radius a b ab) volume a b := by
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have continuous:=(response_ac seed frame M F radius a b ab).continuousOn
  have paired:ContinuousOn (fun t => pairing (modes M) (response seed frame M F radius a b ab t)
      (dual seed M t (response seed frame M F radius a b ab t))) (uIcc a b) :=
    (co.continuous.comp_continuousOn continuous).inner
      (co.continuous.comp_continuousOn ((NativeWindowTraceAdjoint.dual_continuous seed M).continuousOn.clm_apply continuous))
  have source:=(paired.const_mul (-nu.coeff⁻¹)).intervalIntegrable (μ := volume)
  convert! source using 1
  funext t
  rw [dual_energy]
  dsimp only [dissipation]
  field_simp [nu.coeff_pos.ne']

theorem energy_ac (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) : AbsolutelyContinuousOnInterval (energy seed frame M F radius a b ab) a b := by
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have source:=(diagonal_ac ((innerSL ℝ).bilinearComp co co) (response_ac seed frame M F radius a b ab)).const_mul (1/2 : ℝ)
  simpa only [ContinuousLinearMap.bilinearComp_apply,innerSL_apply_apply,real_inner_self_eq_norm_sq] using! source

theorem energy_derivative (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) : ∀ᵐ time : ℝ,time∈Ioo a b →
    HasDerivAt (energy seed frame M F radius a b ab)
      (work seed frame M F radius a b ab time+nu.coeff*dissipation seed frame M F radius a b ab time) time := by
  filter_upwards [response_derivative seed frame M F radius a b ab a0] with time derivative inside
  let co:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  have source:=((co.hasFDerivAt.comp_hasDerivAt time (derivative inside)).norm_sq).const_mul (1/2 : ℝ)
  have green:=dual_energy seed M time (response seed frame M F radius a b ab time)
  convert! source using 1
  simp only [map_sub,inner_sub_right]
  change work seed frame M F radius a b ab time+nu.coeff*dissipation seed frame M F radius a b ab time=
    (1/2 : ℝ)*(2*(pairing (modes M) (response seed frame M F radius a b ab time) (forcing seed frame M F radius time)-
      pairing (modes M) (response seed frame M F radius a b ab time) (dual seed M time (response seed frame M F radius a b ab time))))
  rw [green,pairing_symmetric (modes M) (response seed frame M F radius a b ab time)]
  dsimp only [work,dissipation]
  ring

theorem quadratic_write (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) :
    IntervalIntegrable (work seed frame M F radius a b ab) volume a b ∧
    (∫t in a..b,work seed frame M F radius a b ab t)=
      -energy seed frame M F radius a b ab a-nu.coeff*(∫t in a..b,dissipation seed frame M F radius a b ab t) := by
  let net:=fun t => work seed frame M F radius a b ab t+nu.coeff*dissipation seed frame M F radius a b ab t
  have ac:=energy_ac seed frame M F radius a b ab
  have actual:∀ᵐ t : ℝ,t∈uIcc a b →HasDerivAt (energy seed frame M F radius a b ab) (net t) t := by
    filter_upwards [energy_derivative seed frame M F radius a b ab a0,(volume : Measure ℝ).ae_ne a,(volume : Measure ℝ).ae_ne b]
      with t derivative left right inside
    rw [uIcc_of_le ab] at inside
    exact derivative ⟨lt_of_le_of_ne inside.1 (Ne.symm left),lt_of_le_of_ne inside.2 right⟩
  have netPaid:IntervalIntegrable net volume a b := by
    apply (intervalIntegrable_iff').mpr
    refine ((intervalIntegrable_iff').mp ac.intervalIntegrable_deriv).congr ?_
    filter_upwards [ae_restrict_of_ae actual,ae_restrict_mem measurableSet_uIcc] with t derivative inside
    exact (derivative inside).deriv
  have curlPaid:=(dissipation_integrable seed frame M F radius a b ab).const_mul nu.coeff
  have workPaid:IntervalIntegrable (work seed frame M F radius a b ab) volume a b := by
    convert! netPaid.sub curlPaid using 1
    funext t
    change _=(work seed frame M F radius a b ab t+_)-_
    ring
  have written:=integral_of_ac_derivative _ _ ac netPaid actual
  rw [energy,response_terminal,map_zero,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_sub] at written
  rw [intervalIntegral.integral_add workPaid curlPaid,intervalIntegral.integral_const_mul] at written
  exact ⟨workPaid,by linarith only [written]⟩

theorem net_nonpositive (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) : (∫t in a..b,work seed frame M F radius a b ab t)≤0 := by
  rw [(quadratic_write seed frame M F radius a b ab a0).2]
  have positive:=intervalIntegral.integral_nonneg (μ := volume) ab (fun t _ => dissipation_nonnegative seed frame M F radius a b ab t)
  have mass:0≤energy seed frame M F radius a b ab a := by unfold energy; positivity
  nlinarith only [mass,mul_nonneg nu.coeff_pos.le positive]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem response_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (frame0 : 0≤frame)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) (t : ℝ) (ht : t∈Icc a b) :
    response seed (step.2.clockAdvance+frame) M F radius (step.2.clockAdvance+a) (step.2.clockAdvance+b)
      (by linarith) (step.2.clockAdvance+t)=response step.1 frame M F radius a b ab t := by
  rw [response,response,NativeWindowTraceEndpointWindow.terminal_next seed step generated frame frame0 M F radius t (a0.trans ht.1),
    NativeWindowTraceEndpointWindow.terminal_next seed step generated frame frame0 M F radius b (a0.trans ab)]
  exact congrArg (fun v => terminal step.1 frame M F radius t-v)
    (NativeWindowTraceCoupled.backward_next seed step generated M a b ab a0 (terminal step.1 frame M F radius b) ht)

theorem work_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame : ℝ) (frame0 : 0≤frame)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) :
    (∫t in step.2.clockAdvance+a..step.2.clockAdvance+b,
      work seed (step.2.clockAdvance+frame) M F radius (step.2.clockAdvance+a) (step.2.clockAdvance+b) (by linarith) t)=
        ∫t in a..b,work step.1 frame M F radius a b ab t := by
  have current0 : 0 ≤ step.2.clockAdvance+a := add_nonneg step.2.clockAdvance_pos.le a0
  have initial : energy seed (step.2.clockAdvance+frame) M F radius (step.2.clockAdvance+a) (step.2.clockAdvance+b)
      (by linarith) (step.2.clockAdvance+a)=energy step.1 frame M F radius a b ab a := by
    simp only [energy,response_next seed step generated frame frame0 M F radius a b ab a0 a (left_mem_Icc.mpr ab)]
  have heat : (∫t in step.2.clockAdvance+a..step.2.clockAdvance+b,
      dissipation seed (step.2.clockAdvance+frame) M F radius (step.2.clockAdvance+a) (step.2.clockAdvance+b) (by linarith) t)=
        ∫t in a..b,dissipation step.1 frame M F radius a b ab t := by
    rw [← intervalIntegral.integral_comp_add_left]
    apply intervalIntegral.integral_congr
    intro t inside
    rw [uIcc_of_le ab] at inside
    simp only [dissipation,response_next seed step generated frame frame0 M F radius a b ab a0 t inside]
  rw [(quadratic_write seed (step.2.clockAdvance+frame) M F radius (step.2.clockAdvance+a) (step.2.clockAdvance+b) (by linarith) current0).2,
    (quadratic_write step.1 frame M F radius a b ab a0).2,initial,heat]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutResponse
