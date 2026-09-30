import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Lyapunov
import H0mework.Versions.X.NavierStokes.WindowHistory.Causal.Response

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

def testAction (M : ℕ) : Module.End ℝ (physicalSpace (modes M)) :=
  NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu

def load (observation : ℝ) (M : ℕ) (test : physicalSpace (modes M)) (time : ℝ) : physicalSpace (modes M) :=
  NativeForwardWindowSource.kernel (observation-time) • testAction (nu := nu) M test

theorem load_continuous (observation : ℝ) (M : ℕ) (test : physicalSpace (modes M)) :
    Continuous (load (nu := nu) observation M test) :=
  (NativeForwardWindowSource.kernel_smooth.continuous.comp (continuous_const.sub continuous_id)).smul continuous_const

def reversedAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (finish elapsed : ℝ) :=
  dual seed M (finish-elapsed)

def reversedLoad (observation : ℝ) (M : ℕ) (test : physicalSpace (modes M)) (finish elapsed : ℝ) :=
  load (nu := nu) observation M test (finish-elapsed)

theorem reversedAction_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (finish : ℝ) :
    Continuous (reversedAction seed M finish) :=
  (NativeWindowTraceAdjoint.dual_continuous seed M).comp (continuous_const.sub continuous_id)

theorem reversedLoad_continuous (observation : ℝ) (M : ℕ) (test : physicalSpace (modes M)) (finish : ℝ) :
    Continuous (reversedLoad (nu := nu) observation M test finish) :=
  (load_continuous (nu := nu) observation M test).comp (continuous_const.sub continuous_id)

def response (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (time : ℝ) : physicalSpace (modes M) :=
  NativeWindowHistoryCausalResponse.response (reversedAction seed M b) (reversedAction_continuous seed M b)
    (reversedLoad (nu := nu) observation M test b) (reversedLoad_continuous (nu := nu) observation M test b)
    0 (b-a) (sub_nonneg.mpr ab) (b-time)

theorem response_terminal (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) : response seed M observation test a b ab b=0 := by
  simp only [response,sub_self]
  exact NativeWindowHistoryCausalResponse.response_initial _ _ _ _ _ _ _

theorem response_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (time : ℝ) (inside : time∈Icc a b) :
    HasDerivWithinAt (response seed M observation test a b ab)
      (-dual seed M time (response seed M observation test a b ab time)-load (nu := nu) observation M test time) (Icc a b) time := by
  have maps : MapsTo (fun s : ℝ => b-s) (Icc a b) (Icc 0 (b-a)) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have clock : HasDerivWithinAt (fun s : ℝ => b-s) (-1) (Icc a b) time := by
    simpa only [Pi.sub_apply,id_eq,zero_sub] using!
      ((hasDerivAt_const time b).sub (hasDerivAt_id time)).hasDerivWithinAt
  have actual := (NativeWindowHistoryCausalResponse.response_derivative
    (reversedAction seed M b) (reversedAction_continuous seed M b)
    (reversedLoad (nu := nu) observation M test b) (reversedLoad_continuous (nu := nu) observation M test b)
    0 (b-a) (sub_nonneg.mpr ab) (b-time) (maps inside)).scomp time clock maps
  change HasDerivWithinAt (response seed M observation test a b ab)
    ((-1 : ℝ) • (dual seed M (b-(b-time)) (response seed M observation test a b ab time)+
      load (nu := nu) observation M test (b-(b-time)))) (Icc a b) time at actual
  rw [sub_sub_cancel] at actual
  apply actual.congr_deriv
  module

theorem source_green_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a≤b) (a0 : 0≤a) :
    ∀ᵐ time : ℝ,time∈Ioo a b → HasDerivAt
      (fun s => pairing (modes M) (value seed M s) (response seed M observation test a b ab s))
      (pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
        (response seed M observation test a b ab time)-
        NativeForwardWindowSource.kernel (observation-time)*pairing (modes M) (value seed M time)
          (testAction (nu := nu) M test)) time := by
  filter_upwards [NativeWindowHierarchyPairWindow.source_derivative_total seed,
    NativeWindowTraceAdjoint.source_action_ae seed M] with time actual source inside
  have du := (NativeWindowStageNineSource.lift (modes M)).hasFDerivAt.comp_hasDerivAt time actual
  change HasDerivAt (value seed M) _ time at du
  have dp := (response_derivative seed M observation test a b ab time
    (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
  let read := LinearMap.toContinuousLinearMap (coefficients (modes M))
  have pair := (read.hasFDerivAt.comp_hasDerivAt time du).inner ℝ
    (read.hasFDerivAt.comp_hasDerivAt time dp)
  rw [source (a0.trans inside.1.le)] at pair
  convert! pair using 1
  change _=pairing (modes M) (value seed M time)
    (-dual seed M time (response seed M observation test a b ab time)-load (nu := nu) observation M test time)+
    pairing (modes M) (forward seed M time (value seed M time)+NativeWindowStageNineSource.forcing seed M time)
      (response seed M observation test a b ab time)
  simp only [map_sub,map_neg,map_add,LinearMap.add_apply,
    load,map_smul,smul_eq_mul,NativeWindowTraceAdjoint.adjoint_pairing]
  ring

theorem response_metric_rate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M observation,
      ∀ (test : physicalSpace (modes M)) a b (ab : a ≤ b), ∀ time ∈ Ioo a b,
      time ∈ Ioo 0 horizon →
      let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ab
      let z := NativeWindowTraceDualEvolution.lifted seed M F radius time (p time)
      |deriv (fun t => NativeWindowTraceDualEvolution.energy seed M F radius t (p t)) time +
        NativeWindowTraceDualEvolution.lyapunov seed M F radius time z +
        2 * NativeForwardWindowSource.kernel (observation-time) * pairing (modes M) z (testAction (nu := nu) M test)| ≤
          C * NativeWindowTraceDualEvolution.energy seed M F radius time (p time) := by
  obtain ⟨low,C,C0,paid⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius M observation test a b ab time inside clock => ?_⟩
  let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let p := response seed M observation test a b ab
  have generated := fun t ht => (paid radius above outerRadius M t ht).1
  have original : HasDerivAt p
      (-load (nu := nu) observation M test time - dual seed M time (p time)) time := by
    have derivative := (response_derivative seed M observation test a b ab time
      (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
    apply derivative.congr_deriv
    abel
  have derivative := NativeWindowTraceDualEvolution.energy_hasDerivAt seed M F radius
    horizon time clock generated original
  rw [NativeWindowTraceDualEvolution.adjoint_generator seed M F radius time
    (generated time (Ioo_subset_Icc_self clock))] at derivative
  have cost := (paid radius above outerRadius M time (Ioo_subset_Icc_self clock)).2 (p time) |>.2.2
  dsimp only
  rw [derivative.deriv]
  simp only [map_neg, load, map_smul, smul_eq_mul]
  convert cost using 1
  rw [show ∀ A B K P : ℝ, -A + 2 * -(K * P) - B + A + 2 * K * P = -B by intros; ring, abs_neg]

theorem response_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a ≤ b) :
    ContinuousOn (response seed M observation test a b ab) (Icc a b) :=
  fun time inside => (response_derivative seed M observation test a b ab time inside).continuousWithinAt

theorem response_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a ≤ b) :
    AbsolutelyContinuousOnInterval (response seed M observation test a b ab) a b := by
  let p := response seed M observation test a b ab
  let rate := fun time => -dual seed M time (p time) - load (nu := nu) observation M test time
  have pc : ContinuousOn p (Icc a b) := response_continuous seed M observation test a b ab
  have rc : ContinuousOn rate (Icc a b) :=
    ((NativeWindowTraceAdjoint.dual_continuous seed M).continuousOn.clm_apply pc).neg.sub
      (load_continuous (nu := nu) observation M test).continuousOn
  have write (x y : ℝ) (xin : x ∈ Icc a b) (yin : y ∈ Icc a b) (xy : x ≤ y) :
      p y - p x = ∫ t in x..y, rate t := by
    have subset : Icc x y ⊆ Icc a b := Icc_subset_Icc xin.1 yin.2
    have paid := rc.mono subset
    rw [← uIcc_of_le xy] at paid
    apply (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le xy (pc.mono subset) _ paid.intervalIntegrable).symm
    intro t ht
    exact ((response_derivative seed M observation test a b ab t (subset (Ioo_subset_Icc_self ht))).mono subset).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  apply NativeUnheatedIntegralBilinear.written_ac p rate
    (by rw [← uIcc_of_le ab] at rc; exact rc.intervalIntegrable)
  intro x xin y yin
  rw [uIcc_of_le ab] at xin yin
  by_cases ordered : x ≤ y
  · exact write x y xin yin ordered
  · rw [intervalIntegral.integral_symm, ← write y x yin xin (le_of_not_ge ordered)]
    abel

theorem testAction_symmetric (M : ℕ) (x y : physicalSpace (modes M)) :
    pairing (modes M) x (testAction (nu := nu) M y) =
      pairing (modes M) (testAction (nu := nu) M x) y := by
  simp only [testAction, NativeWindowOperatorGreen.laplacian, LinearMap.smul_apply,
    map_smul, smul_eq_mul]
  rw [NativeWindowOperatorGreen.dissipative_adjoint]

theorem load_graph_paid (M : ℕ) (observation time : ℝ) (test z : physicalSpace (modes M)) :
    2 * NativeForwardWindowSource.kernel (observation-time) *
      pairing (modes M) z (testAction (nu := nu) M test) ≤
      (nu.coeff^2/2) * ‖coefficients (modes M) (testAction (nu := nu) M z)‖^2 +
        (2/nu.coeff^2) * NativeForwardWindowSource.kernel (observation-time)^2 *
          ‖coefficients (modes M) test‖^2 := by
  rw [testAction_symmetric]
  let k := NativeForwardWindowSource.kernel (observation-time)
  let d := ‖coefficients (modes M) (testAction (nu := nu) M z)‖
  let m := ‖coefficients (modes M) test‖
  have paired : |pairing (modes M) (testAction (nu := nu) M z) test| ≤ d*m :=
    abs_real_inner_le_norm (coefficients (modes M) (testAction (nu := nu) M z)) (coefficients (modes M) test)
  have source := (le_abs_self (pairing (modes M) (testAction (nu := nu) M z) test)).trans paired
  have scaled := mul_le_mul_of_nonneg_left source
    (mul_nonneg (show (0 : ℝ) ≤ 2 from by norm_num) (NativeForwardWindowSource.kernel_nonnegative (observation-time)))
  have identity : (nu.coeff^2/2)*d^2+(2/nu.coeff^2)*k^2*m^2-2*k*(d*m) =
      (nu.coeff^2*d-2*k*m)^2/(2*nu.coeff^2) := by
    field_simp [nu.coeff_pos.ne']
    ring
  have bound : 0 ≤ (nu.coeff^2/2)*d^2+(2/nu.coeff^2)*k^2*m^2-2*k*(d*m) := by
    rw [identity]
    positivity
  change 2*k*pairing (modes M) (testAction (nu := nu) M z) test ≤ _ at scaled
  change 2*k*pairing (modes M) (testAction (nu := nu) M z) test ≤ _
  linarith only [scaled, bound]

theorem source_response_graph_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ radius ≥ low, ∀ outerRadius M observation,
      ∀ (test : physicalSpace (modes M)) a b (ab : a ≤ b), ∀ time ∈ Ioo a b,
      time ∈ Ioo 0 horizon →
      let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
      let p := response seed M observation test a b ab
      let z := NativeWindowTraceDualEvolution.lifted seed M F radius time (p time)
      (nu.coeff^2/2) * ‖coefficients (modes M) (testAction (nu := nu) M z)‖^2 ≤
        deriv (fun t => NativeWindowTraceDualEvolution.energy seed M F radius t (p t)) time +
          NativeDistributedLyapunov.convectionWork seed M F radius time z +
          C * NativeWindowTraceDualEvolution.energy seed M F radius time (p time) +
          (2/nu.coeff^2) * NativeForwardWindowSource.kernel (observation-time)^2 *
            ‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,Ct,Ct0,clock⟩ := response_metric_rate seed horizon nonnegative
  obtain ⟨last,Ch,Ch0,heat⟩ := NativeDistributedLyapunov.source_lyapunov_gate seed horizon nonnegative
  refine ⟨max first last,Ct+Ch,add_nonneg Ct0 Ch0,
    fun radius above outerRadius M observation test a b ab time inside valid => ?_⟩
  have rate := clock radius ((le_max_left first last).trans above) outerRadius M observation test a b ab time inside valid
  have dissipative := heat radius ((le_max_right first last).trans above) outerRadius M time (Ioo_subset_Icc_self valid)
    (response seed M observation test a b ab time)
  let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let z := NativeWindowTraceDualEvolution.lifted seed M F radius time (response seed M observation test a b ab time)
  have forced := load_graph_paid (nu := nu) M observation time test z
  have lower := (neg_le_abs _).trans rate
  dsimp only [F,z,testAction] at *
  linarith only [lower,dissipative,forced]


end
end SaturationMonoid.NavierStokes.NativeWindowDistributedAdjoint
