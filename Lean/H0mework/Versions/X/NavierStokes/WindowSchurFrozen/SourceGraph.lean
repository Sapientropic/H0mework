import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.History
import H0mework.Versions.X.NavierStokes.WindowSchurMean.EffectiveGraph
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.CrossBudget

set_option autoImplicit false
open scoped BigOperators Topology Convolution ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySourceResolventGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM restrict_energy)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (velocityPath velocityRate forcingValue forwardFiber)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeWindowHistorySchurAdvectorFiber (family)
open NativeWindowHistoryDynamicHistory (transportSize transportSize_bound transportSize_nonnegative)
open NativeForwardWindowJets (kernelJet kernelJet_smooth kernelJet_compact)
open NativeUnheatedStressPairEvolution (kernelWeight kernelWeight_continuous kernelWeight_hasDerivAt)
noncomputable section
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) : wholePhysical :=
  kernel seed M sample (velocityPath seed M sample)

theorem velocity_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖velocityPath seed M time‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  rw [velocityPath,include_norm (modes M) (modes_zero M),← NativeWindowHistoryOseen.restrict_original_total seed time M]
  exact (restrict_energy (modes M) (modes_zero M) (modes_closed M) _).trans
    (NativeWindowTraceWholeHistory.original_bound seed time)

theorem value_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖value seed M time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (NativeWindowHistoryFrozenInverse.kernel_bound seed M time _).trans (velocity_bound seed M time)

theorem value_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (value seed M) :=
  (NativeWindowHistoryFrozenInverse.kernel_continuous seed M).clm_apply
    (NativeWindowHistoryOseen.velocityPath_continuous seed M)

def window (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → wholePhysical :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] value seed M

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (window seed M order) (window seed M (order+1) time) time := by
  have actual:=(kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp))
      ((value_continuous seed M).locallyIntegrable (μ := (volume : Measure ℝ))) time
  simpa only [window,kernelJet,iteratedDeriv_succ] using actual

theorem window_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    window seed M order time=∫sample in time+1..time+2,kernelWeight order time 0 sample • value seed M sample :=
  NativeWindowStressHeatTime.kernel_integral _ _ _

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖window seed M order time‖ ≤ NativeWindowFiniteStressUniform.kernelBound order*NativeUnifiedCompleteSource.budget seed := by
  rw [window_original]
  have point (sample : ℝ) (_ : sample∈uIoc (time+1) (time+2)) :
      ‖kernelWeight order time 0 sample • value seed M sample‖ ≤
        NativeWindowFiniteStressUniform.kernelBound order*NativeUnifiedCompleteSource.budget seed := by
    rw [norm_smul]
    simp only [kernelWeight,zero_add]
    exact mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample))
      (value_bound seed M sample) (norm_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have paid:=intervalIntegral.norm_integral_le_of_norm_le_const point
  simpa only [show time+2-(time+1)=(1:ℝ) by ring,abs_one,mul_one] using paid

open NativeFiniteActionResolvent (physicalSpace coefficients)
open NativeWindowHistoryAdjointSpatialHalf (moment outputSquare energyCap)
open NativeWindowHistoryAdjointSpatialFeedback (read read_output read_moment transportCap)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeUnheatedSexticLatticePower (radical)

private theorem add_square {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u+v‖^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
  have triangle:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
  nlinarith only [triangle,sq_nonneg (‖u‖-‖v‖)]

private theorem output_add (M : ℕ) (u v : physicalSpace (modes M)) :
    outputSquare false (modes M) (u+v) ≤ 2*(outputSquare false (modes M) u+outputSquare false (modes M) v) := by
  let L:=(read M (NativeWindowHistoryAdjointSpatialHalf.weight false)).comp (includeCLM (modes M) (modes_closed M))
  have same (w : physicalSpace (modes M)) : ‖L w‖^2=outputSquare false (modes M) w := by
    simp only [L,ContinuousLinearMap.comp_apply,read_output,restrict_include]
  rw [← same,← same,← same,map_add]
  exact add_square _ _

private theorem weak_le_moment (M : ℕ) (v : physicalSpace (modes M)) :
    outputSquare false (modes M) v ≤ moment (modes M) 2 v := by
  rw [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.moment_original]
  apply Finset.sum_le_sum
  intro k _
  have one : 1 ≤ radical k := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (NativeUnheatedSexticLatticePower.mass_one k))
  have inverse : NativeUnheatedSexticLatticePower.density 1 k ≤ 1 := by
    simpa only [NativeUnheatedSexticLatticePower.density,pow_one,one_div,inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) one
  have squared : NativeUnheatedSexticLatticePower.density 1 k^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (NativeUnheatedSexticLatticePower.density_positive 1 k).le inverse 2
  have fourth : 1 ≤ radical k^4 := by rw [NativeUnheatedSexticLatticePower.radical_fourth]; exact NativeUnheatedSexticLatticePower.mass_one k
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simpa only [NativeWindowHistoryAdjointSpatialHalf.weight,Bool.false_eq_true,if_false,one_pow] using squared.trans fourth

def physicalValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  NativeWindowHistoryFrozenInverse.physical seed M time (NativeWindowTraceAdjoint.value seed M time)

theorem value_included (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    value seed M time=includeCLM (modes M) (modes_closed M) (physicalValue seed M time) := by
  rw [value,velocityPath,NativeWindowHistoryHeatWindow.included]
  rfl

theorem value_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryHeatDual.energy nu M (physicalValue seed M time) ≤ NativeUnifiedCompleteSource.budget seed^2 := by
  have balance:=NativeWindowHistoryFrozenInverse.physical_balance seed M time (NativeWindowTraceAdjoint.value seed M time)
  have gradient : 0 ≤ NativeCommonAdvectorAction.curlPair (modes M) (physicalValue seed M time).1 (physicalValue seed M time).1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]; exact sq_nonneg _
  have mass:=pow_le_pow_left₀ (norm_nonneg _) (velocity_bound seed M time) 2
  rw [velocityPath,include_norm (modes M) (modes_zero M)] at mass
  change _=‖coefficients (modes M) (physicalValue seed M time)‖^2+
    ‖coefficients (modes M) (NativeWindowTraceAdjoint.value seed M time-physicalValue seed M time)‖^2+
    2*nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) (physicalValue seed M time).1 (physicalValue seed M time).1 at balance
  change ‖coefficients (modes M) (physicalValue seed M time)‖^2+
    nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) (physicalValue seed M time).1 (physicalValue seed M time).1 ≤ _
  nlinarith only [mass,balance,mul_nonneg nu.coeff_pos.le gradient,
    sq_nonneg ‖coefficients (modes M) (NativeWindowTraceAdjoint.value seed M time-physicalValue seed M time)‖]

theorem value_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    value seed M time+nu.coeff • laplacianFiber nu M (value seed M time)=
      velocityPath seed M time+family nu M (velocityPath seed M time) (value seed M time) := by
  have source:=NativeWindowHistoryDynamicTest.heat_kernel seed M time (velocityPath seed M time)
  simp only [NativeWindowHistoryDynamicTest.heat,add_apply,smul_apply,
    NativeWindowHistoryFrozenInverse.kernel_projected,NativeWindowHistoryDynamicTest.advection] at source
  have original : NativeWindowTraceWholeHistory.projection M (velocityPath seed M time)=velocityPath seed M time := by
    simp only [NativeWindowTraceWholeHistory.projection,velocityPath,ContinuousLinearMap.comp_apply,restrict_include]
  exact source.trans (congrArg (fun u : wholePhysical => u+family nu M (velocityPath seed M time) (value seed M time)) original)

theorem physical_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    physicalValue seed M time+nu.coeff • NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (physicalValue seed M time)=NativeWindowTraceAdjoint.value seed M time+
        NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
          (NativeWindowTraceAdjoint.value seed M time) (physicalValue seed M time) := by
  have source:=congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M)) (value_heat seed M time)
  simpa only [map_add,map_smul,value_included,velocityPath,NativeWindowHistorySchurAdvectorFiber.family_original,
    NativeWindowHistoryAnnihilationControl.laplacianFiber,NativeWindowHistoryOseen.lift_included,restrict_include] using! source

def halfCap (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  2*energyCap nu^2*(1+transportCap*(energyCap nu*NativeUnifiedCompleteSource.budget seed^2))

theorem halfCap_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ halfCap seed := by
  unfold halfCap
  positivity [NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu,
    NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative]

theorem value_half (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    moment (modes M) 3 (physicalValue seed M time) ≤ halfCap seed*moment (modes M) 2 (NativeWindowTraceAdjoint.value seed M time) := by
  have heat:=NativeWindowHistoryAdjointSpatialHalf.heat_gain nu (modes M) (modes_zero M) (modes_closed M)
    (physicalValue seed M time) _ (physical_heat seed M time)
  have low:=(NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M (physicalValue seed M time)).trans
    (mul_le_mul_of_nonneg_left (value_energy seed M time) (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le)
  have nonlinear:=NativeWindowHistoryAdjointSpatialHalf.transport_bound false (modes M) (modes_zero M) (modes_closed M)
    nu (NativeWindowTraceAdjoint.value seed M time) (physicalValue seed M time)
  change _ ≤ transportCap*moment (modes M) 2 (NativeWindowTraceAdjoint.value seed M time)*moment (modes M) 2 (physicalValue seed M time) at nonlinear
  have bounded:=nonlinear.trans (mul_le_mul_of_nonneg_left low (mul_nonneg
    NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative _ _ _)))
  have add:=output_add M (NativeWindowTraceAdjoint.value seed M time)
    (NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
      (NativeWindowTraceAdjoint.value seed M time) (physicalValue seed M time))
  have upper:=mul_le_mul_of_nonneg_left (add_le_add (weak_le_moment M (NativeWindowTraceAdjoint.value seed M time)) bounded) (by norm_num : (0:ℝ)≤2)
  exact heat.trans ((mul_le_mul_of_nonneg_left (add.trans upper) (sq_nonneg (energyCap nu))).trans_eq (by unfold halfCap; ring))

def nonlinearCap (seed : GeneratedWholeRestartCurrent nu) : ℝ := Real.sqrt (transportCap*halfCap seed)*energyCap nu

theorem nonlinearCap_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ nonlinearCap seed :=
  mul_nonneg (Real.sqrt_nonneg _) (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le

theorem value_nonlinear (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖family nu M (velocityPath seed M time) (value seed M time)‖ ≤
      nonlinearCap seed*NativeWindowHistoryCrossBudget.pointEnergy seed M time := by
  let u:=NativeWindowTraceAdjoint.value seed M time
  let y:=physicalValue seed M time
  let v:=NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu u y
  have strong : outputSquare true (modes M) v=‖includeCLM (modes M) (modes_closed M) v‖^2 := by
    rw [include_norm (modes M) (modes_zero M)]
    have source:=(NativeWindowHistoryCreationGeometry.pairing_mass (modes M) v).symm.trans
      (real_inner_self_eq_norm_sq (coefficients (modes M) v))
    simpa only [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.weight,
      if_true,one_pow,one_mul] using source
  have transport:=NativeWindowHistoryAdjointSpatialHalf.transport_bound true (modes M) (modes_zero M) (modes_closed M) nu u y
  change outputSquare true (modes M) v ≤ transportCap*moment (modes M) 2 u*moment (modes M) 3 y at transport
  rw [strong] at transport
  have scaled:=mul_le_mul_of_nonneg_left (value_half seed M time)
    (mul_nonneg NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative (modes M) 2 u))
  have normed : ‖includeCLM (modes M) (modes_closed M) v‖ ≤ Real.sqrt (transportCap*halfCap seed)*moment (modes M) 2 u := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative _ _ _))).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg NativeWindowHistoryAdjointSpatialFeedback.transportCap_nonnegative (halfCap_nonnegative seed))]
    exact transport.trans (scaled.trans_eq (by ring))
  have energy:=mul_le_mul_of_nonneg_left (NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M u)
    (Real.sqrt_nonneg (transportCap*halfCap seed))
  rw [NativeWindowHistorySchurAdvectorFiber.family_original,velocityPath,value_included,restrict_include,restrict_include]
  exact normed.trans (energy.trans_eq (by unfold nonlinearCap NativeWindowHistoryCrossBudget.pointEnergy; ring))

theorem value_graph (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖laplacianFiber nu M (value seed M time)‖ ≤ nu.coeff⁻¹*
      (2*NativeUnifiedCompleteSource.budget seed+nonlinearCap seed*NativeWindowHistoryCrossBudget.pointEnergy seed M time) := by
  have equation : nu.coeff • laplacianFiber nu M (value seed M time)=
      velocityPath seed M time+family nu M (velocityPath seed M time) (value seed M time)-value seed M time := by
    have source:=value_heat seed M time
    exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using source))
  have normed:=congrArg (fun v : wholePhysical => ‖v‖) equation
  rw [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le] at normed
  have upper:=(norm_sub_le
    (velocityPath seed M time+family nu M (velocityPath seed M time) (value seed M time)) (value seed M time)).trans
    (add_le_add (norm_add_le (velocityPath seed M time) (family nu M (velocityPath seed M time) (value seed M time))) le_rfl)
  have bounded:=(add_le_add (add_le_add (velocity_bound seed M time) (value_nonlinear seed M time)) (value_bound seed M time))
  have total : nu.coeff*‖laplacianFiber nu M (value seed M time)‖ ≤
      2*NativeUnifiedCompleteSource.budget seed+nonlinearCap seed*NativeWindowHistoryCrossBudget.pointEnergy seed M time :=
    normed.trans_le (upper.trans (bounded.trans_eq (by ring)))
  simpa only [← mul_assoc,inv_mul_cancel₀ nu.coeff_pos.ne',one_mul] using!
    mul_le_mul_of_nonneg_left total (inv_nonneg.mpr nu.coeff_pos.le)

def graphBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ :=
  max 0 (NativeWindowFiniteStressUniform.kernelBound order*nu.coeff⁻¹*
    (2*NativeUnifiedCompleteSource.budget seed+nonlinearCap seed*NativeWindowHistoryCrossBudget.energyBudget seed horizon))

theorem window_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) : ‖laplacianFiber nu M (window seed M order time)‖ ≤ graphBudget seed horizon order := by
  have ordered : time+1 ≤ time+2 := by linarith
  have integrable : IntervalIntegrable (fun sample => kernelWeight order time 0 sample • value seed M sample) volume (time+1) (time+2) :=
    ((value_continuous seed M).intervalIntegrable (μ := volume) (time+1) (time+2)).continuousOn_smul
      (kernelWeight_continuous order time 0).continuousOn
  rw [window_original,← (laplacianFiber nu M).intervalIntegral_comp_comm integrable]
  simp only [map_smul]
  let C:=NativeWindowFiniteStressUniform.kernelBound order*nu.coeff⁻¹
  have C0 : 0 ≤ C := mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive order).le (inv_nonneg.mpr nu.coeff_pos.le)
  let f:=fun sample => kernelWeight order time 0 sample • laplacianFiber nu M (value seed M sample)
  let majorant:=fun sample => C*(2*NativeUnifiedCompleteSource.budget seed+
    nonlinearCap seed*NativeWindowHistoryCrossBudget.pointEnergy seed M sample)
  have fi : IntervalIntegrable (fun s => ‖f s‖) volume (time+1) (time+2) :=
    (((kernelWeight_continuous order time 0).smul ((laplacianFiber nu M).continuous.comp
      (value_continuous seed M))).intervalIntegrable (time+1) (time+2)).norm
  have mi : IntervalIntegrable majorant volume (time+1) (time+2) :=
    (continuous_const.mul (continuous_const.add (continuous_const.mul
      (NativeWindowHistoryCrossBudget.pointEnergy_continuous seed M)))).intervalIntegrable (time+1) (time+2)
  have point (sample : ℝ) (_ : sample∈Icc (time+1) (time+2)) : ‖f sample‖ ≤ majorant sample := by
    rw [norm_smul]
    have weight : ‖kernelWeight order time 0 sample‖ ≤ NativeWindowFiniteStressUniform.kernelBound order := by
      simpa only [kernelWeight,zero_add] using NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)
    exact (mul_le_mul weight (value_graph seed M sample) (norm_nonneg _)
      (NativeWindowFiniteStressUniform.kernelBound_positive order).le).trans_eq (by dsimp only [C,majorant]; ring)
  have integralRead : (∫sample in time+1..time+2,majorant sample)=
      C*(2*NativeUnifiedCompleteSource.budget seed+nonlinearCap seed*(∫sample in time+1..time+2,
        NativeWindowHistoryCrossBudget.pointEnergy seed M sample)) := by
    rw [show majorant=(fun sample => C*(2*NativeUnifiedCompleteSource.budget seed+
      nonlinearCap seed*NativeWindowHistoryCrossBudget.pointEnergy seed M sample)) from rfl,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const
        (((NativeWindowHistoryCrossBudget.pointEnergy_continuous seed M).intervalIntegrable (μ := volume)
          (time+1) (time+2)).const_mul _),intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
    simp only [show time+2-(time+1)=(1:ℝ) by ring,one_smul]
  have paid:=mul_le_mul_of_nonneg_left (add_le_add (le_refl (2*NativeUnifiedCompleteSource.budget seed)) (mul_le_mul_of_nonneg_left
    (NativeWindowHistoryCrossBudget.source_window_energy seed horizon M time inside) (nonlinearCap_nonnegative seed))) C0
  exact (intervalIntegral.norm_integral_le_integral_norm ordered).trans
    ((intervalIntegral.integral_mono_on ordered fi mi point).trans
      (integralRead.trans_le (paid.trans (le_max_right _ _))))

theorem window_projected (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    NativeWindowTraceWholeHistory.projection M (window seed M order time)=window seed M order time := by
  have integrable : IntervalIntegrable (fun sample => kernelWeight order time 0 sample • value seed M sample) volume (time+1) (time+2) :=
    ((value_continuous seed M).intervalIntegrable (μ := volume) (time+1) (time+2)).continuousOn_smul
      (kernelWeight_continuous order time 0).continuousOn
  rw [window_original,← (NativeWindowTraceWholeHistory.projection M).intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro sample _
  simp only [map_smul,value_included,NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,restrict_include]

private theorem four_square {E : Type*} [SeminormedAddCommGroup E] (u v a b : E) :
    ‖u+v-a-b‖^2 ≤ 4*(‖u‖^2+‖v‖^2+‖a‖^2+‖b‖^2) := by
  have first:=add_square (u+v) (-(a+b))
  rw [norm_neg] at first
  have same : u+v-a-b=(u+v)+(-(a+b)) := by abel
  rw [same]
  nlinarith only [first,add_square u v,add_square a b]

def loadCap (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  4*(1+nu.coeff^2+(1+NativeWindowHistoryCreationSource.budget seed horizon 1)+
    NativeWindowHistoryAdjointSpatialFeedback.budget seed horizon*(1+nu.coeff))

theorem loadCap_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ loadCap seed horizon := by
  unfold loadCap
  positivity [nu.coeff_pos,NativeWindowHistoryCreationSource.budget_nonnegative seed horizon 1 (by norm_num),
    NativeWindowHistoryAdjointSpatialFeedback.budget_nonnegative seed horizon]

theorem load_graph_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) (u : wholePhysical) (supported : NativeWindowTraceWholeHistory.projection M u=u) :
    ‖NativeWindowMeanEffectiveGraph.load seed M time u‖^2 ≤
      loadCap seed horizon*(‖u‖^2+‖laplacianFiber nu M u‖^2) := by
  let v:=restrictCLM (modes M) (modes_zero M) (modes_closed M) u
  let T:=‖u‖^2+‖laplacianFiber nu M u‖^2
  let D:=NativeWindowHistoryCreationSource.budget seed horizon 1
  let B:=NativeWindowHistoryAdjointSpatialFeedback.budget seed horizon
  have D0 : 0 ≤ D:=NativeWindowHistoryCreationSource.budget_nonnegative seed horizon 1 (by norm_num)
  have B0 : 0 ≤ B:=NativeWindowHistoryAdjointSpatialFeedback.budget_nonnegative seed horizon
  have grad : inner ℝ u (laplacianFiber nu M u) ≤ T := by
    have cauchy:=real_inner_le_norm u (laplacianFiber nu M u)
    dsimp only [T]
    nlinarith only [cauchy,sq_nonneg (‖u‖-‖laplacianFiber nu M u‖),sq_nonneg ‖u‖,sq_nonneg ‖laplacianFiber nu M u‖]
  have mass : ‖u‖^2 ≤ T := le_add_of_nonneg_right (sq_nonneg _)
  have lap : ‖laplacianFiber nu M u‖^2 ≤ T := le_add_of_nonneg_left (sq_nonneg _)
  have included : includeCLM (modes M) (modes_closed M) v=u := supported
  have energy : NativeWindowHistoryHeatDual.energy nu M v=‖u‖^2+nu.coeff*inner ℝ u (laplacianFiber nu M u) := by
    rw [NativeWindowMetricGraphHistory.fiber_gradient]
    change ‖coefficients (modes M) v‖^2+_=_
    rw [← include_norm (modes M) (modes_zero M) (modes_closed M) v,included]
  have reaction:=NativeWindowHistoryAdjointSpatialFeedback.feedback_bound seed horizon M time inside v
  rw [included,energy] at reaction
  have rBound : ‖NativeWindowHistorySchurAction.feedback seed M time u‖^2 ≤ B*((1+nu.coeff)*T) := by
    exact reaction.trans (mul_le_mul_of_nonneg_left
      ((add_le_add mass (mul_le_mul_of_nonneg_left grad nu.coeff_pos.le)).trans_eq (by ring)) B0)
  have drift:=NativeWindowHistoryMeanDrift.source_whole_bound seed horizon 1 (by norm_num) M time inside u
  dsimp only at drift
  have normed:=real_inner_self_eq_norm_sq (coefficients (modes M)
    (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v))
  change NativeFiniteActionResolvent.pairing (modes M) _ _=‖coefficients (modes M) _‖^2 at normed
  rw [normed,← NativeWindowMetricGraphHistory.laplacian_norm,← NativeWindowMetricGraphHistory.fiber_gradient,one_mul] at drift
  have dBound : ‖NativeWindowHistoryMeanDrift.drift seed M time u‖^2 ≤ (1+D)*T :=
    drift.trans ((add_le_add lap (mul_le_mul_of_nonneg_left grad D0)).trans_eq (by ring))
  have equation : NativeWindowMeanEffectiveGraph.load seed M time u=u+nu.coeff • laplacianFiber nu M u-
      NativeWindowHistoryMeanDrift.drift seed M time u-NativeWindowHistorySchurAction.feedback seed M time u := by
    have actual:=NativeWindowMeanEffectiveGraph.load_split seed M time u
    rw [actual]
    abel
  rw [equation]
  have upper:=four_square u (nu.coeff • laplacianFiber nu M u)
    (NativeWindowHistoryMeanDrift.drift seed M time u) (NativeWindowHistorySchurAction.feedback seed M time u)
  rw [norm_smul,mul_pow,Real.norm_of_nonneg nu.coeff_pos.le] at upper
  have heat:=mul_le_mul_of_nonneg_left lap (sq_nonneg nu.coeff)
  have sum:=add_le_add (add_le_add (add_le_add mass heat) dBound) rBound
  exact upper.trans ((mul_le_mul_of_nonneg_left sum (by norm_num : (0:ℝ)≤4)).trans_eq (by unfold loadCap; dsimp only [D,B,T]; ring))

def loadedBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ :=
  loadCap seed horizon*((NativeWindowFiniteStressUniform.kernelBound order*NativeUnifiedCompleteSource.budget seed)^2+
    graphBudget seed horizon order^2)

/-- The source bound is after the actual Schur load, not before its two spatial derivatives. -/
theorem source_loaded_window_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) : ‖NativeWindowMeanEffectiveGraph.load seed M time (window seed M order time)‖^2 ≤
      loadedBudget seed horizon order :=
  (load_graph_bound seed horizon M time inside _ (window_projected seed M order time)).trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (pow_le_pow_left₀ (norm_nonneg _) (window_bound seed M order time) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (window_graph_bound seed horizon M order time inside) 2)) (loadCap_nonnegative seed horizon))

open NativeWindowHistoryOseen (H action)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryMeanBlocks (annihilation bath)
open NativeWindowHistoryBathResolvent (resolve)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeForwardWindowPairingReadout (averageMeasure)
local notation "Q" => NativeWindowHistoryMeanProjection.residual

def responseRead (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] wholePhysical :=
  (annihilation seed M time).comp ((resolve seed M time).comp Q)

private theorem schur_algebra {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m B : E →L[ℝ] F) (P A D R : E →L[ℝ] E) (C : F →L[ℝ] E) (A0 : F →L[ℝ] F) (x : E)
    (first : m (A x)=A0 (m x)+B x) (last : P (A x)=C (m x)+D x)
    (bathRead : D (P x)=D x) (annRead : B (P x)=B x)
    (inverse : R (P x-D (P x))=P x) :
    m x-(A0 (m x)+B (R (C (m x))))=m (x-A x)+B (R (P (x-A x))) := by
  have projected : P (x-A x)=(P x-D (P x))-C (m x) := by rw [map_sub,last,bathRead]; abel
  rw [projected,R.map_sub,inverse,B.map_sub,annRead,m.map_sub,first]
  abel

theorem implicit_schur (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : H) :
    NativeWindowMeanEffectiveGraph.load seed M time (mean x)=
      mean (x-action seed M time x)+responseRead seed M time (x-action seed M time x) := by
  simpa only [NativeWindowMeanEffectiveGraph.load,NativeWindowHistorySchurAction.effective,
    NativeWindowHistorySchurAction.feedback,NativeWindowHistorySchurAction.response,responseRead,
    ContinuousLinearMap.comp_apply,add_apply] using!
    schur_algebra (E := H) (F := wholePhysical) mean (annihilation seed M time) Q (action seed M time)
      (bath seed M time) (resolve seed M time) (NativeWindowHistoryMeanAction.creation seed M time)
      (NativeWindowHistoryMeanAction.meanOperator seed M time) x
      (NativeWindowHistoryMeanBlocks.mean_action_split seed M time x)
      (NativeWindowHistoryMeanBlocks.residual_action_split seed M time x)
      (NativeWindowHistoryBathResolvent.bath_residual seed M time x)
      (NativeWindowHistorySchurCompletion.annihilation_residual seed M time x)
      (NativeWindowHistoryBathResolvent.resolve_inverse seed M time (Q x))

theorem whole_kernel_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    kernelAction seed M time v-action seed M time (kernelAction seed M time v)=NativeWindowTraceWholeHistory.projected M v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (kernelAction seed M time v) (action seed M time (kernelAction seed M time v)),
    kernelAction_ae seed M time v,NativeWindowHistoryOseen.action_ae seed M time (kernelAction seed M time v),
    (NativeWindowTraceWholeHistory.projection M).coeFn_compLpL v] with lag subtract original acted target
  rw [subtract,Pi.sub_apply,original,acted,original,NativeWindowHistoryFrozenInverse.kernel_write]
  exact target.symm

theorem response_factor (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    mean (NativeWindowTraceWholeHistory.projected M v)+responseRead seed M time (NativeWindowTraceWholeHistory.projected M v)=
      NativeWindowMeanEffectiveGraph.load seed M time (mean (kernelAction seed M time v)) := by
  have actual:=implicit_schur seed M time (kernelAction seed M time v)
  rw [whole_kernel_write] at actual
  exact actual.symm

theorem mean_kernel_history (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (kernelAction seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M))=window seed M 0 time := by
  rw [NativeWindowHistoryMeanProjection.mean_original]
  have original : window seed M 0 time=∫lag,value seed M (time-lag) ∂averageMeasure := by
    rw [NativeForwardWindowPairingReadout.density_integral]
    rfl
  rw [original]
  apply integral_congr_ae
  filter_upwards [kernelAction_ae seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M),
    NativeWindowHistoryOseen.history_original seed M time] with lag acted raw
  rw [acted,raw]
  rfl

theorem response_history (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    responseRead seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      NativeWindowMeanEffectiveGraph.load seed M time (window seed M 0 time)-
        mean (NativeWindowTraceWholeHistory.finiteHistory seed time M) := by
  have actual:=response_factor seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)
  have kept : NativeWindowTraceWholeHistory.projected M (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      NativeWindowTraceWholeHistory.finiteHistory seed time M :=
    NativeWindowTraceWholeHistory.projected_idempotent M (NativeWindowTraceWholeHistory.history seed time)
  rw [kept,mean_kernel_history] at actual
  exact eq_sub_of_add_eq' actual

theorem source_response_history_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) : ‖responseRead seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)‖^2 ≤
      2*(loadedBudget seed horizon 0+NativeWindowHistorySchurTemporalControl.massBudget seed) := by
  let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
  have split:=NativeWindowHistoryMeanProjection.energy_split h
  change ‖h‖^2=‖NativeWindowHistoryMeanProjection.embed (mean h)‖^2+‖Q h‖^2 at split
  rw [NativeWindowHistoryMeanProjection.embed_norm] at split
  have mass : ‖mean h‖^2 ≤ NativeWindowHistorySchurTemporalControl.massBudget seed := by
    nlinarith only [split,sq_nonneg ‖Q h‖,NativeWindowHistorySchurTemporalControl.source_mass seed M time inside.1]
  rw [response_history]
  have difference:=add_square (NativeWindowMeanEffectiveGraph.load seed M time (window seed M 0 time)) (-mean h)
  rw [norm_neg] at difference
  exact difference.trans (mul_le_mul_of_nonneg_left (add_le_add
    (source_loaded_window_bound seed horizon M 0 time inside) mass) (by norm_num : (0:ℝ)≤2))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed M (step.2.clockAdvance+time)=value step.1 M time := by
  have original:=NativeWindowTraceAdjoint.source_next seed M step generated time nonnegative
  simp only [Prod.mk.injEq] at original
  simp only [value,velocityPath,original.1,NativeWindowHistoryFrozenInverse.kernel_next seed M step generated time nonnegative]

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    window seed M order (step.2.clockAdvance+time)=window step.1 M order time := by
  change (∫lag,kernelJet order lag • value seed M (step.2.clockAdvance+time-lag))=
    (∫lag,kernelJet order lag • value step.1 M (time-lag))
  apply integral_congr_ae
  filter_upwards with lag
  by_cases zero : kernelJet order lag=0
  · simp only [zero,zero_smul]
  · rw [add_sub_assoc,value_next seed M step generated (time-lag)
      (by linarith [NativeForwardWindowJets.kernelJet_nonpositive order lag zero])]

theorem responseRead_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    responseRead seed M (step.2.clockAdvance+time)=responseRead step.1 M time := by
  have blocks:=NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative
  have ann:=congrArg (fun p => p.2.2.1) blocks
  exact congrArg₂ (fun (B : H →L[ℝ] wholePhysical) (R : H →L[ℝ] H) => B.comp (R.comp Q)) ann
    (NativeWindowHistoryBathResolvent.resolve_next seed M step generated time nonnegative)

theorem response_history_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    responseRead seed M (step.2.clockAdvance+time) (NativeWindowTraceWholeHistory.finiteHistory seed (step.2.clockAdvance+time) M)=
      responseRead step.1 M time (NativeWindowTraceWholeHistory.finiteHistory step.1 time M) :=
  congrArg₂ (fun (B : H →L[ℝ] wholePhysical) (v : H) => B v) (responseRead_next seed M step generated time nonnegative)
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySourceResolventGraph
