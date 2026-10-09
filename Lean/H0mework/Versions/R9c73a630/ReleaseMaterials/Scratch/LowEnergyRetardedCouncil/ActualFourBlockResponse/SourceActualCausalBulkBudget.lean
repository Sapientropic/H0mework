import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkTime
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorBulkSourcePrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCausalBulkTime
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption SourceScalarPairedTransport
open SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open SourceBulkTimeBalance SourceScalarShiftedBulk SourceShiftedBulkTimeBudget ActualVectorJointCost
open ActualVectorBulkSourcePrice Lean Meta Elab Term
open scoped Topology InnerProductSpace BigOperators ENNReal
attribute [local irreducible] sourcePair bulkAction compressionCore raisedNoetherCurrent inverseForm coreTime

elab "paid_causal_bulk%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkTime 0) "LowEnergy") "ActualCausalBulkTime"
  let name := Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original signed bulk-time payment {name}"
  mkConstWithFreshMVarLevels name

set_option quotPrecheck false in
local notation "coefficient" => (paid_causal_bulk% coefficient)
set_option quotPrecheck false in
local notation "timeSum" => (paid_causal_bulk% timeSum)
set_option quotPrecheck false in
local notation "gapCoefficient" => (paid_causal_bulk% gapCoefficient)
set_option quotPrecheck false in
local notation "value" => (paid_causal_bulk% value)

private theorem current_time (advanced : Bool) (F : Index) (μ : ℝ) (T : End)
    (g : diagonal.domain) (t : ℝ) :
    timeSum advanced F μ (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j) t=
      (Real.exp (-2*μ*t) : ℂ)*(direction advanced*raisedNoetherCurrent F T (causalCoreTime advanced F g t) : ℝ) := by
  have hc := (paid_bulk_time% current_sum) F T g (fun i => phase (value advanced F i) t)
  change currentPair F T (∑i,phase (value advanced F i) t • channelTest F g i)
      (∑i,phase (value advanced F i) t • channelTest F g i)=
      ∑i,∑j,star (phase (value advanced F i) t)*phase (value advanced F j) t*gapCoefficient F T g i j at hc
  calc
    _ = (Real.exp (-2*μ*t) : ℂ)*(direction advanced : ℂ)*
        (∑i,∑j,star (phase (value advanced F i) t)*phase (value advanced F j) t*gapCoefficient F T g i j) := by
      change (∑i : Channel F,∑j : Channel F,
        Complex.exp (-gap μ (value advanced F i) (value advanced F j)*(t : ℂ))*
          ((direction advanced : ℂ)*gapCoefficient F T g i j))=_
      simp_rw [(paid_causal_bulk% time_factor)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [←hc,←(paid_causal_bulk% core_channels) advanced F g t,actual_diagonal_current]
      push_cast
      ring

private theorem algebra_balance (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    (2*μ : ℂ)*(∫t : ℝ in Set.Ioi 0,timeSum advanced F μ (coefficient F g T (bulkAction*T)) t)=
      sourcePair (T (coreEquiv.symm g)) (bulkAction (T (coreEquiv.symm g)))+
        2*(∫t : ℝ in Set.Ioi 0,timeSum advanced F μ
          (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j) t) := by
  have hi : (∑i,∑j,coefficient F g T (bulkAction*T) i j)=
      sourcePair (T (coreEquiv.symm g)) (bulkAction (T (coreEquiv.symm g))) :=
    (paid_bulk_time% initial_sum) F T g
  rw [(paid_causal_bulk% sum_integral) advanced F μ hμ,
    (paid_causal_bulk% sum_integral) advanced F μ hμ,←hi]
  have h := (paid_bulk_time% finite_balance) μ hμ (value advanced F) (coefficient F g T (bulkAction*T))
  refine h.trans ?_
  apply congrArg (fun z : ℂ => (∑i,∑j,coefficient F g T (bulkAction*T) i j)+2*z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hv (k : Channel F) : value advanced F k=direction advanced*channelValue F k := rfl
  have hg (u v : Channel F) : gapCoefficient F T g u v=
      (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*coefficient F g T (bulkAction*T) u v := rfl
  rw [hv i,hv j,hg i j]
  push_cast
  ring

/-- The actual signed-time trajectory pays its own complete compression current. -/
theorem actual_causal_time_noether_balance (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*
      (direction advanced*raisedNoetherCurrent F T (causalCoreTime advanced F g t))) (Set.Ioi 0) ∧
    2*μ*causalTimeEnergy advanced F μ T g=inverseForm (T (coreEquiv.symm g))+
      2*(∫t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
        (direction advanced*raisedNoetherCurrent F T (causalCoreTime advanced F g t))) := by
  have ht := (paid_causal_bulk% sum_integrable) advanced F μ hμ (coefficient F g T (bulkAction*T))
  have hc := (paid_causal_bulk% sum_integrable) advanced F μ hμ
    (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j)
  have he (t : ℝ) : (timeSum advanced F μ (coefficient F g T (bulkAction*T)) t).re=
      Real.exp (-2*μ*t)*inverseForm (T (causalCoreTime advanced F g t)) := by
    rw [(paid_causal_bulk% pair_time),Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact congrArg (fun r : ℝ => Real.exp (-2*μ*t)*r) (original_bulk_energy _)
  have hj (t : ℝ) : (timeSum advanced F μ
      (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j) t).re=
      Real.exp (-2*μ*t)*(direction advanced*raisedNoetherCurrent F T (causalCoreTime advanced F g t)) := by
    simp only [current_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨hc.re.congr (Eventually.of_forall hj),?_⟩
  have hb := congrArg Complex.re (algebra_balance advanced F μ hμ T g)
  have htr : (∫t : ℝ in Set.Ioi 0,timeSum advanced F μ (coefficient F g T (bulkAction*T)) t).re=
      ∫t : ℝ in Set.Ioi 0,(timeSum advanced F μ (coefficient F g T (bulkAction*T)) t).re := (integral_re ht).symm
  have hcr : (∫t : ℝ in Set.Ioi 0,timeSum advanced F μ
      (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j) t).re=
      ∫t : ℝ in Set.Ioi 0,(timeSum advanced F μ
        (fun i j => (direction advanced : ℂ)*gapCoefficient F T g i j) t).re := (integral_re hc).symm
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,mul_zero,add_zero,sub_zero,Complex.add_re,htr,hcr,he,hj,original_bulk_energy] at hb
  exact hb

private theorem pair_im_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*(sourcePair
      (A (causalCoreTime advanced F g t)) (B (causalCoreTime advanced F g t))).im) (Set.Ioi 0) := by
  have h := ((paid_causal_bulk% pair_parseval) advanced F μ hμ g A B).2.1.im
  change IntegrableOn (fun t : ℝ => ((Real.exp (-2*μ*t) : ℂ)*sourcePair
    (A (causalCoreTime advanced F g t)) (B (causalCoreTime advanced F g t))).im) (Set.Ioi 0) at h
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h

private theorem remaining_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*(direction advanced*
      remainingRaised F T (causalCoreTime advanced F g t))) (Set.Ioi 0) := by
  have h := ((pair_im_integrable advanced F μ hμ g (diagonalAction*T-T*compressionCore F) (bulkAction*T)).sub
    ((pair_im_integrable advanced F μ hμ g T (remainingCurrentComplete*T)).div_const 2)).const_mul (direction advanced)
  refine h.congr (Eventually.of_forall (fun t => ?_))
  have hd (q : QuantumTest) : raisedDefect F T q=(diagonalAction*T-T*compressionCore F) q := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  simp only [Pi.sub_apply,remainingRaised,hd,Module.End.mul_apply]
  ring

/-- The full scalar absorption is valid separately on both original time directions. -/
theorem actual_causal_current_bound (advanced : Bool) (F : Index) (T : End) (q : QuantumTest) :
    direction advanced*raisedNoetherCurrent F T q ≤ direction advanced*remainingRaised F T q+
      2*sourceTime 0*inverseForm (T q)+(sourceTime 0)^2*‖vacuum‖^2*‖embed (T q)‖^2 := by
  have he : raisedNoetherCurrent F T q=remainingRaised F T q-
      (sourcePair (T q) (scalarCurrentComplete (T q))).im/2 := by
    rw [raisedNoetherCurrent,original_complete_current_split]
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im,remainingRaised]
    ring
  have h := original_complete_scalar_bound (T q)
  cases advanced
  · rw [show direction false=1 by rfl,he]
    have hl := neg_abs_le ((sourcePair (T q) (scalarCurrentComplete (T q))).im/2)
    linarith
  · rw [show direction true= -1 by rfl,he]
    have hl := le_abs_self ((sourcePair (T q) (scalarCurrentComplete (T q))).im/2)
    linarith

theorem actual_causal_norm_parseval (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => ‖embed (T (state F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g))‖^2) ∧
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*‖embed (T (causalCoreTime advanced F g t))‖^2) (Set.Ioi 0) ∧
    (∫w : ℝ,‖embed (T (state F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g))‖^2)=2*Real.pi*causalNormTime advanced F μ T g := by
  obtain ⟨hf,ht,he⟩ := (paid_causal_bulk% pair_parseval) advanced F μ hμ g T T
  have hv (q : QuantumTest) : (sourcePair (T q) (T q)).re=‖embed (T q)‖^2 := by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed (T q))
  have htv (t : ℝ) : ((Real.exp (-2*μ*t) : ℂ)*sourcePair
      (T (causalCoreTime advanced F g t)) (T (causalCoreTime advanced F g t))).re=
      Real.exp (-2*μ*t)*‖embed (T (causalCoreTime advanced F g t))‖^2 := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hv]
  refine ⟨hf.re.congr (Eventually.of_forall (fun w => hv _)),ht.re.congr (Eventually.of_forall htv),?_⟩
  have h := congrArg Complex.re he
  have hr1 : (∫w : ℝ,sourcePair
      (T (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))
      (T (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))).re=
      ∫w : ℝ,(sourcePair
        (T (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))
        (T (state F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g))).re := (integral_re hf).symm
  have hr2 : (∫t : ℝ in Set.Ioi 0,(Real.exp (-2*μ*t) : ℂ)*sourcePair
      (T (causalCoreTime advanced F g t)) (T (causalCoreTime advanced F g t))).re=
      ∫t : ℝ in Set.Ioi 0,((Real.exp (-2*μ*t) : ℂ)*sourcePair
        (T (causalCoreTime advanced F g t)) (T (causalCoreTime advanced F g t))).re := (integral_re ht).symm
  rw [hr1,Complex.mul_re,show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,hr2] at h
  simpa only [hv,htv,causalNormTime] using h

/-- Complete shifted scalar absorption retains the original signed non-scalar current. -/
theorem actual_causal_shifted_time_absorption (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*(direction advanced*
      remainingRaised F T (causalCoreTime advanced F g t))) (Set.Ioi 0) ∧
    (μ-2*sourceTime 0)*causalTimeEnergy advanced F μ T g ≤
      inverseForm (T (coreEquiv.symm g))/2+causalRemainingTime advanced F μ T g+
        (sourceTime 0)^2*‖vacuum‖^2*causalNormTime advanced F μ T g := by
  obtain ⟨hj,hbalance⟩ := actual_causal_time_noether_balance advanced F μ hμ T g
  have he := (actual_causal_bulk_parseval advanced F μ hμ T g).2.1
  have hr := remaining_integrable advanced F μ hμ T g
  have hn := (actual_causal_norm_parseval advanced F μ hμ T g).2.1
  refine ⟨hr,?_⟩
  have hupper := (hr.add (he.const_mul (2*sourceTime 0))).add
    (hn.const_mul ((sourceTime 0)^2*‖vacuum‖^2))
  have hle := integral_mono hj hupper (fun t => by
    have h := mul_le_mul_of_nonneg_left (actual_causal_current_bound advanced F T (causalCoreTime advanced F g t))
      (Real.exp_pos (-2*μ*t)).le
    dsimp only [Pi.add_apply]
    nlinarith only [h])
  simp only [Pi.add_apply] at hle
  have hab := integral_add hr (he.const_mul (2*sourceTime 0))
  have habc := integral_add (hr.add (he.const_mul (2*sourceTime 0))) (hn.const_mul ((sourceTime 0)^2*‖vacuum‖^2))
  simp only [Pi.add_apply] at hab habc
  rw [habc,hab,integral_const_mul,integral_const_mul] at hle
  change _ ≤ causalRemainingTime advanced F μ T g+2*sourceTime 0*causalTimeEnergy advanced F μ T g+
    (sourceTime 0)^2*‖vacuum‖^2*causalNormTime advanced F μ T g at hle
  nlinarith only [hbalance,hle]

open SourceScalarInverseRetardedBudget SourceInverseFixedEnergyTail

theorem actual_causal_norm_time_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      causalNormTime advanced F μ (theta m ell) g ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_theta_frequency_norm_tail μ hμ g (2*Real.pi*ε) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have he := (actual_causal_norm_parseval advanced F μ hμ (theta m ell) g).2.2
  have h := hF advanced
  rw [he] at h
  nlinarith [Real.pi_pos]

/-- A common source event pays the fixed and norm tails before both time directions. -/
theorem actual_causal_shifted_time_energy_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
      (μ-2*sourceTime 0)*causalTimeEnergy advanced F μ (theta m ell) g ≤
        ε+causalRemainingTime advanced F μ (theta m ell) g := by
  intro ε hε
  let V : ℝ := (sourceTime 0)^2*‖vacuum‖^2
  obtain ⟨NI,hI⟩ := original_fixed_energy_tail (coreEquiv.symm g) ε hε
  obtain ⟨NN,hN⟩ := actual_causal_norm_time_tail μ hμ g ((ε/2)/(V+1)) (by dsimp [V];positivity)
  refine ⟨max NI NN,fun m hm ell hell => ?_⟩
  filter_upwards [hN m ((le_max_right _ _).trans hm) ell hell] with F hF
  intro advanced
  have hi := hI m ((le_max_left _ _).trans hm) ell hell
  have hb := (actual_causal_shifted_time_absorption advanced F μ hμ (theta m ell) g).2
  have hnorm : 0≤causalNormTime advanced F μ (theta m ell) g := integral_nonneg (fun _ => by positivity)
  have hmul := mul_le_mul_of_nonneg_left (hF advanced) (show 0≤V+1 by dsimp [V];positivity)
  rw [mul_div_cancel₀ _ (by dsimp [V];positivity : V+1≠0)] at hmul
  change _ ≤ inverseForm (theta m ell (coreEquiv.symm g))/2+causalRemainingTime advanced F μ (theta m ell) g+
    V*causalNormTime advanced F μ (theta m ell) g at hb
  nlinarith only [hi,hb,hmul,hnorm]

end LowEnergy.ActualCausalBulkTime
