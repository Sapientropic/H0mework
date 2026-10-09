import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceBulkTimeEnergyBudget
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeScalarOscillatorAbsorption

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceBulkTimeBalance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption
open SourceScalarPairedTransport SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair bulkAction compressionCore raisedNoetherCurrent inverseForm coreTime

private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def timeSum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*c i j
private def gapCoefficient (F : Index) (T : End) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  (Complex.I/2)*((channelValue F i : ℂ)-(channelValue F j : ℂ))*coefficient F g T (bulkAction*T) i j

private theorem time_factor (μ a b t : ℝ) :
    Complex.exp (-gap μ a b*(t : ℂ))=(Real.exp (-2*μ*t) : ℂ)*star (phase a t)*phase b t := by
  simp only [gap,phase,Complex.star_def,←Complex.exp_conj,Complex.ofReal_exp]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  push_cast
  ring

private theorem pair_sum (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑ i,c i • channelTest F g i)) (B (∑ j,c j • channelTest F g j))=
      ∑ i,∑ j,star (c i)*c j*coefficient F g A B i j := by
  simp only [coefficient,sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_time (F : Index) (μ : ℝ) (g : diagonal.domain) (A B : End) (t : ℝ) :
    timeSum F μ (coefficient F g A B) t=(Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t)) := by
  unfold timeSum
  simp_rw [time_factor]
  rw [coreTime,pair_sum]
  simp only [Finset.mul_sum,phase]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem decay_integrable (μ a b : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-gap μ a b*(t : ℂ))) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp [gap]
  linarith

private theorem decay_integral (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ t : ℝ in Set.Ioi 0,Complex.exp (-gap μ a b*(t : ℂ)))=(gap μ a b)⁻¹ := by
  have hn : (-gap μ a b).re<0 := by simp [gap];linarith
  rw [integral_exp_mul_complex_Ioi hn 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

private theorem sum_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    IntegrableOn (timeSum F μ c) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem sum_integral (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    (∫ t : ℝ in Set.Ioi 0,timeSum F μ c t)=
      ∑ i,∑ j,(gap μ (channelValue F i) (channelValue F j))⁻¹*c i j := by
  unfold timeSum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,decay_integral μ _ _ hμ]

private theorem current_sum (F : Index) (T : End) (g : diagonal.domain) (a : Channel F → ℂ) :
    currentPair F T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*gapCoefficient F T g i j := by
  have he : currentPair F T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*currentPair F T (channelTest F g i) (channelTest F g j) := by
    simp only [currentPair,map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,
      inner_smul_right,starRingEnd_apply,Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_comm (f := fun x i => a x * (star (a i) *
      inner ℂ (embed (bulkAction (T (channelTest F g i)))) (embed (T (compressionCore F (channelTest F g x))))))]
    simp only [←Finset.sum_sub_distrib,mul_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [actual_channel_gap,gapCoefficient,coefficient,Module.End.mul_apply] using he

private theorem current_time (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) (t : ℝ) :
    timeSum F μ (gapCoefficient F T g) t=(Real.exp (-2*μ*t) : ℂ)*
      (raisedNoetherCurrent F T (coreTime F g t) : ℂ) := by
  rw [←actual_diagonal_current,coreTime,current_sum]
  unfold timeSum
  simp_rw [time_factor]
  simp only [Finset.mul_sum,phase]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem core_zero (F : Index) (g : diagonal.domain) : coreTime F g 0=coreEquiv.symm g := by
  apply embed_injective
  rw [actual_core_time,SourceFiniteUnitary.time_zero]
  simpa only [one_apply_eq_self] using! (congrArg Subtype.val (coreEquiv.apply_symm_apply g)).symm

private theorem initial_sum (F : Index) (T : End) (g : diagonal.domain) :
    ∑ i,∑ j,coefficient F g T (bulkAction*T) i j=
      sourcePair (T (coreEquiv.symm g)) (bulkAction (T (coreEquiv.symm g))) := by
  have he := pair_time F 1 g T (bulkAction*T) 0
  simpa only [timeSum,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
    Real.exp_zero,Complex.ofReal_one,core_zero,Module.End.mul_apply] using he

attribute [local irreducible] coefficient gapCoefficient

private theorem finite_balance {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0 < μ)
    (v : ι → ℝ) (c : ι → ι → ℂ) :
    (2*μ : ℂ)*(∑ i,∑ j,(gap μ (v i) (v j))⁻¹*c i j)=
      (∑ i,∑ j,c i j)+2*(∑ i,∑ j,(gap μ (v i) (v j))⁻¹*
        ((Complex.I/2)*((v i : ℂ)-(v j : ℂ))*c i j)) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := gap_ne μ (v i) (v j) hμ
  field_simp
  simp only [gap]
  ring

private theorem algebra_balance (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    (2*μ : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (bulkAction*T)) t)=
      sourcePair (T (coreEquiv.symm g)) (bulkAction (T (coreEquiv.symm g)))+
        2*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F T g) t) := by
  rw [sum_integral F μ hμ,sum_integral F μ hμ,←initial_sum F T g]
  simpa only [gapCoefficient] using finite_balance μ hμ (channelValue F) (coefficient F g T (bulkAction*T))

/-- Exact damped energy balance of the original time trajectory, retaining its full raised defect. -/
theorem actual_time_noether_balance (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*raisedNoetherCurrent F T (coreTime F g t)) (Set.Ioi 0) ∧
    2*μ*timeEnergy F μ T g=inverseForm (T (coreEquiv.symm g))+
      2*(∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*raisedNoetherCurrent F T (coreTime F g t)) := by
  have ht := sum_integrable F μ hμ (coefficient F g T (bulkAction*T))
  have hc := sum_integrable F μ hμ (gapCoefficient F T g)
  have he (t : ℝ) : (timeSum F μ (coefficient F g T (bulkAction*T)) t).re=
      Real.exp (-2*μ*t)*inverseForm (T (coreTime F g t)) := by
    rw [pair_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact congrArg (fun r : ℝ => Real.exp (-2*μ*t)*r) (original_bulk_energy _)
  have hj (t : ℝ) : (timeSum F μ (gapCoefficient F T g) t).re=
      Real.exp (-2*μ*t)*raisedNoetherCurrent F T (coreTime F g t) := by
    rw [current_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨hc.re.congr (Eventually.of_forall hj),?_⟩
  have hb := congrArg Complex.re (algebra_balance F μ hμ T g)
  have htr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (bulkAction*T)) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (coefficient F g T (bulkAction*T)) t).re := (integral_re ht).symm
  have hcr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F T g) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (gapCoefficient F T g) t).re := (integral_re hc).symm
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,mul_zero,add_zero,sub_zero,Complex.add_re,htr,hcr,he,hj,original_bulk_energy] at hb
  exact hb

private theorem pair_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => (Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t))) (Set.Ioi 0) :=
  (sum_integrable F μ hμ (coefficient F g A B)).congr (Eventually.of_forall (pair_time F μ g A B))

private theorem pair_im_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*
      (sourcePair (A (coreTime F g t)) (B (coreTime F g t))).im) (Set.Ioi 0) := by
  have h := (pair_integrable F μ hμ g A B).im
  change IntegrableOn (fun t : ℝ => ((Real.exp (-2*μ*t) : ℂ)*sourcePair (A (coreTime F g t)) (B (coreTime F g t))).im) (Set.Ioi 0) at h
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h

/-- Original remaining current on the same finite graded trajectory, with its raised defect intact. -/
def remainingTime (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*remainingRaisedCurrent F T (coreTime F g t)

def normTime (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*‖embed (T (coreTime F g t))‖^2

private theorem remaining_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*remainingRaisedCurrent F T (coreTime F g t)) (Set.Ioi 0) := by
  have h := (pair_im_integrable F μ hμ g (diagonalAction*T-T*compressionCore F) (bulkAction*T)).sub
    ((pair_im_integrable F μ hμ g T (remainingCurrent*T)).div_const 2)
  refine h.congr (Eventually.of_forall (fun t => ?_))
  dsimp only [Pi.sub_apply]
  have hd (q : QuantumTest) : raisedDefect F T q=(diagonalAction*T-T*compressionCore F) q := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  simp only [remainingRaisedCurrent,hd,Module.End.mul_apply]
  ring

private theorem norm_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*‖embed (T (coreTime F g t))‖^2) (Set.Ioi 0) := by
  have h := (pair_integrable F μ hμ g T T).re
  refine h.congr (Eventually.of_forall (fun t => ?_))
  change ((Real.exp (-2*μ*t) : ℂ)*sourcePair (T (coreTime F g t)) (T (coreTime F g t))).re=_
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hp : (sourcePair (T (coreTime F g t)) (T (coreTime F g t))).re=‖embed (T (coreTime F g t))‖^2 := by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed (T (coreTime F g t)))
  exact congrArg (fun r : ℝ => Real.exp (-2*μ*t)*r) hp

private theorem current_bound (F : Index) (T : End) (q : QuantumTest) :
    raisedNoetherCurrent F T q ≤ remainingRaisedCurrent F T q+
      2*sourceTime 0*inverseForm (T q)+4*(sourceTime 0)^2*‖vacuum‖^2*‖embed (T q)‖^2 := by
  have he : raisedNoetherCurrent F T q=remainingRaisedCurrent F T q-
      (sourcePair (T q) (scalarCurrent (T q))).im/2 := by
    rw [raisedNoetherCurrent,original_current_split]
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im,
      remainingRaisedCurrent]
    ring
  rw [he]
  have h := original_scalar_current_bound (T q)
  have hlo := neg_abs_le ((sourcePair (T q) (scalarCurrent (T q))).im/2)
  linarith

/-- The original scalar oscillator is absorbed in the single-source time budget at the same source price 2n. -/
theorem actual_time_scalar_absorption (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*remainingRaisedCurrent F T (coreTime F g t)) (Set.Ioi 0) ∧
    (μ-2*sourceTime 0)*timeEnergy F μ T g  ≤
      inverseForm (T (coreEquiv.symm g))/2+remainingTime F μ T g+
        4*(sourceTime 0)^2*‖vacuum‖^2*normTime F μ T g := by
  obtain ⟨hj,hbalance⟩ := actual_time_noether_balance F μ hμ T g
  have he := (actual_bulk_parseval F μ hμ T g).2.1
  have hr := remaining_integrable F μ hμ T g
  have hn := norm_integrable F μ hμ T g
  refine ⟨hr,?_⟩
  have hupper := (hr.add (he.const_mul (2*sourceTime 0))).add
    (hn.const_mul (4*(sourceTime 0)^2*‖vacuum‖^2))
  have hle := integral_mono hj hupper (fun t => by
    have h := mul_le_mul_of_nonneg_left (current_bound F T (coreTime F g t))
      (Real.exp_pos (-2*μ*t)).le
    dsimp only [Pi.add_apply]
    nlinarith only [h])
  simp only [Pi.add_apply] at hle
  have hab := integral_add hr (he.const_mul (2*sourceTime 0))
  have habc := integral_add (hr.add (he.const_mul (2*sourceTime 0))) (hn.const_mul (4*(sourceTime 0)^2*‖vacuum‖^2))
  simp only [Pi.add_apply] at hab habc
  rw [habc,hab,integral_const_mul,integral_const_mul] at hle
  change _ ≤ remainingTime F μ T g+2*sourceTime 0*timeEnergy F μ T g+
    4*(sourceTime 0)^2*‖vacuum‖^2*normTime F μ T g at hle
  nlinarith only [hbalance,hle]

private def frequencySum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (w : ℝ) : ℂ :=
  ∑ i,∑ j,star (pole μ (channelValue F i) w)*pole μ (channelValue F j) w*c i j

private theorem frequency_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    Integrable (frequencySum F μ c) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem frequency_time (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    (∫ w : ℝ,frequencySum F μ c w)=(2*Real.pi : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeSum F μ c t) := by
  rw [sum_integral F μ hμ]
  unfold frequencySum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (two_pole_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const]
  change twoPole μ (channelValue F i) (channelValue F j)*_= _
  rw [two_pole_closed μ _ _ hμ]
  ring

private theorem norm_parseval (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => ‖embed (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2) ∧
    (∫ w : ℝ,‖embed (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)=
      2*Real.pi*normTime F μ T g := by
  have hp (q : QuantumTest) : (sourcePair q q).re=‖embed q‖^2 := by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed q)
  have hf (w : ℝ) : (frequencySum F μ (coefficient F g T T) w).re=
      ‖embed (T (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2 := by
    rw [←hp,actual_state_channels,pair_sum]
    rfl
  have ht (t : ℝ) : (timeSum F μ (coefficient F g T T) t).re=
      Real.exp (-2*μ*t)*‖embed (T (coreTime F g t))‖^2 := by
    rw [pair_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hp]
  have hfi := frequency_integrable F μ hμ (coefficient F g T T)
  have hti := sum_integrable F μ hμ (coefficient F g T T)
  refine ⟨hfi.re.congr (Eventually.of_forall hf),?_⟩
  have h := congrArg Complex.re (frequency_time F μ hμ (coefficient F g T T))
  have hr1 : (∫ w : ℝ,frequencySum F μ (coefficient F g T T) w).re=
      ∫ w : ℝ,(frequencySum F μ (coefficient F g T T) w).re := (integral_re hfi).symm
  have hr2 : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T T) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (coefficient F g T T) t).re := (integral_re hti).symm
  rw [hr1,Complex.mul_re,show (2*Real.pi : ℂ).re=2*Real.pi by simp,
    show (2*Real.pi : ℂ).im=0 by simp,zero_mul,sub_zero,hr2] at h
  simpa only [hf,ht,normTime] using! h

open SourceScalarInverseRetardedBudget SourceRelativePowerTail SourceRetardedForcingTail SourceInverseFixedEnergyTail

/-- The already paid original frequency tail generates a time-norm tail on the same graded trajectory and cofinal F. -/
theorem actual_norm_time_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),normTime F μ (theta m ell) g ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_theta_full_frequency_tail μ hμ g (2*Real.pi*ε) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  obtain ⟨hi,he⟩ := norm_parseval F μ hμ (theta m ell) g
  have hs (w : ℝ) : embed (theta m ell (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))=
      relativeTail m ell (finiteResolvent F (line μ w) (g : H)) := by
    rw [SourceNativeCutoffContact.theta_core]
    exact congrArg (relativeTail m ell) (congrArg Subtype.val (coreEquiv.apply_symm_apply _))
  simp_rw [hs] at hi he
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),he] at hF
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*Real.pi*ε)).mp hF
  nlinarith [Real.pi_pos]

/-- Fixed input and vacuum time prices are paid; the one surviving signed term keeps every original defect. -/
theorem actual_common_time_energy_budget (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (μ-2*sourceTime 0)*timeEnergy F μ (theta m ell) g ≤ ε+remainingTime F μ (theta m ell) g := by
  intro ε hε
  let V : ℝ := 4*(sourceTime 0)^2*‖vacuum‖^2
  have hV : 0 ≤ V := by dsimp [V];positivity
  obtain ⟨NI,hI⟩ := original_fixed_energy_tail (coreEquiv.symm g) ε hε
  obtain ⟨NN,hN⟩ := actual_norm_time_tail μ hμ g ((ε/2)/(V+1)) (by positivity)
  refine ⟨max NI NN,fun m hm ell hell => ?_⟩
  filter_upwards [hN m ((le_max_right _ _).trans hm) ell hell] with F hF
  have hi := hI m ((le_max_left _ _).trans hm) ell hell
  have hb := (actual_time_scalar_absorption F μ hμ (theta m ell) g).2
  have hnorm : 0 ≤ normTime F μ (theta m ell) g := integral_nonneg (fun _ => by positivity)
  have hmul := (mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ V+1))
  rw [mul_div_cancel₀ _ (by positivity : V+1≠0)] at hmul
  change _ ≤ inverseForm (theta m ell (coreEquiv.symm g))/2+remainingTime F μ (theta m ell) g+
    V*normTime F μ (theta m ell) g at hb
  nlinarith only [hi,hb,hmul,hnorm]

open SourceBulkTimeEnergyBudget SourceScalarSignedInverseReturn SourceInverseNeutralRemainderClosed

/-- The complete original cost consumes the one-source signed time remainder at the source oscillator gap. -/
theorem actual_original_remaining_time_budget (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (hgap : 2*sourceTime 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-2*sourceTime 0))*
            remainingTime F μ (theta m ell) g := by
  intro ε hε
  let P : ℝ := 4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2
  let v : ℝ := μ-2*sourceTime 0
  have hv : 0<v := sub_pos.mpr hgap
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp : 0 ≤ P := by
    have hc : 0 ≤ coefficientCost sharp := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp [P,formPrice]
    positivity
  let δ := v*(ε/2)/(P+1)
  have hδ : 0<δ := div_pos (mul_pos hv (by positivity)) (by positivity)
  obtain ⟨NC,hC⟩ := actual_original_time_energy_budget sharp μ hμ g k (ε/2) (by positivity)
  obtain ⟨NE,hE⟩ := actual_common_time_energy_budget μ hμ g δ hδ
  refine ⟨max NC NE,fun m hm ell hell => ?_⟩
  filter_upwards [hC m ((le_max_left _ _).trans hm) ell hell,
    hE m ((le_max_right _ _).trans hm) ell hell] with F hFC hFE
  have hc := mul_le_mul_of_nonneg_left hFC hv.le
  have he := mul_le_mul_of_nonneg_left hFE hp
  have hd : P*δ ≤ v*(ε/2) := by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<P+1)).mpr
    nlinarith only [mul_nonneg hv.le (le_of_lt hε)]
  change v*closedJointCost sharp m ell F μ (g : H) (k : H) ≤ v*(ε/2+P*timeEnergy F μ (theta m ell) g) at hc
  change P*(v*timeEnergy F μ (theta m ell) g) ≤ P*(δ+remainingTime F μ (theta m ell) g) at he
  have hfinal : closedJointCost sharp m ell F μ (g : H) (k : H)*v ≤
      v*ε+P*remainingTime F μ (theta m ell) g := by nlinarith only [hc,he,hd]
  have hb := (le_div_iff₀ hv).mpr hfinal
  calc
    _ ≤ (v*ε+P*remainingTime F μ (theta m ell) g)/v := hb
    _ = _ := by change _=ε+(P/v)*_;field_simp

end LowEnergy.SourceBulkTimeBalance
