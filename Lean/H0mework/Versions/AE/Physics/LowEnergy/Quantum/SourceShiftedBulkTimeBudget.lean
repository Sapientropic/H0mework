import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarShiftedBulk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceShiftedBulkTimeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption
open SourceScalarPairedTransport SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
open SourceBulkTimeBalance SourceScalarShiftedBulk
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair bulkAction compressionCore raisedNoetherCurrent inverseForm coreTime

private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def timeSum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*c i j
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

private theorem sum_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    IntegrableOn (timeSum F μ c) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

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

def remainingRaised (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (bulkAction (T q))).im-
    (sourcePair (T q) (remainingCurrentComplete (T q))).im/2

def remainingTimeComplete (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*remainingRaised F T (coreTime F g t)

private theorem remaining_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*remainingRaised F T (coreTime F g t)) (Set.Ioi 0) := by
  have h := (pair_im_integrable F μ hμ g (diagonalAction*T-T*compressionCore F) (bulkAction*T)).sub
    ((pair_im_integrable F μ hμ g T (remainingCurrentComplete*T)).div_const 2)
  refine h.congr (Eventually.of_forall (fun t => ?_))
  dsimp only [Pi.sub_apply]
  have hd (q : QuantumTest) : raisedDefect F T q=(diagonalAction*T-T*compressionCore F) q := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  simp only [remainingRaised,hd,Module.End.mul_apply]
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
    raisedNoetherCurrent F T q ≤ remainingRaised F T q+
      2*sourceTime 0*inverseForm (T q)+(sourceTime 0)^2*‖vacuum‖^2*‖embed (T q)‖^2 := by
  have he : raisedNoetherCurrent F T q=remainingRaised F T q-
      (sourcePair (T q) (scalarCurrentComplete (T q))).im/2 := by
    rw [raisedNoetherCurrent,original_complete_current_split]
    simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Complex.add_im,
      remainingRaised]
    ring
  rw [he]
  have h := original_complete_scalar_bound (T q)
  have hlo := neg_abs_le ((sourcePair (T q) (scalarCurrentComplete (T q))).im/2)
  linarith

/-- The complete shifted scalar block is absorbed on the original time trajectory at source price 2n. -/
theorem actual_shifted_time_absorption (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*remainingRaised F T (coreTime F g t)) (Set.Ioi 0) ∧
    (μ-2*sourceTime 0)*timeEnergy F μ T g  ≤
      inverseForm (T (coreEquiv.symm g))/2+remainingTimeComplete F μ T g+
        (sourceTime 0)^2*‖vacuum‖^2*normTime F μ T g := by
  obtain ⟨hj,hbalance⟩ := actual_time_noether_balance F μ hμ T g
  have he := (actual_bulk_parseval F μ hμ T g).2.1
  have hr := remaining_integrable F μ hμ T g
  have hn := norm_integrable F μ hμ T g
  refine ⟨hr,?_⟩
  have hupper := (hr.add (he.const_mul (2*sourceTime 0))).add
    (hn.const_mul ((sourceTime 0)^2*‖vacuum‖^2))
  have hle := integral_mono hj hupper (fun t => by
    have h := mul_le_mul_of_nonneg_left (current_bound F T (coreTime F g t))
      (Real.exp_pos (-2*μ*t)).le
    dsimp only [Pi.add_apply]
    nlinarith only [h])
  simp only [Pi.add_apply] at hle
  have hab := integral_add hr (he.const_mul (2*sourceTime 0))
  have habc := integral_add (hr.add (he.const_mul (2*sourceTime 0))) (hn.const_mul ((sourceTime 0)^2*‖vacuum‖^2))
  simp only [Pi.add_apply] at hab habc
  rw [habc,hab,integral_const_mul,integral_const_mul] at hle
  change _ ≤ remainingTimeComplete F μ T g+2*sourceTime 0*timeEnergy F μ T g+
    (sourceTime 0)^2*‖vacuum‖^2*normTime F μ T g at hle
  nlinarith only [hbalance,hle]

open SourceScalarInverseRetardedBudget SourceInverseFixedEnergyTail

/-- Fixed input and vacuum time prices are paid; the one surviving signed term keeps every original defect. -/
theorem actual_shifted_time_energy_budget (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (μ-2*sourceTime 0)*timeEnergy F μ (theta m ell) g ≤ ε+remainingTimeComplete F μ (theta m ell) g := by
  intro ε hε
  let V : ℝ := (sourceTime 0)^2*‖vacuum‖^2
  have hV : 0 ≤ V := by dsimp [V];positivity
  obtain ⟨NI,hI⟩ := original_fixed_energy_tail (coreEquiv.symm g) ε hε
  obtain ⟨NN,hN⟩ := actual_norm_time_tail μ hμ g ((ε/2)/(V+1)) (by positivity)
  refine ⟨max NI NN,fun m hm ell hell => ?_⟩
  filter_upwards [hN m ((le_max_right _ _).trans hm) ell hell] with F hF
  have hi := hI m ((le_max_left _ _).trans hm) ell hell
  have hb := (actual_shifted_time_absorption F μ hμ (theta m ell) g).2
  have hnorm : 0 ≤ normTime F μ (theta m ell) g := integral_nonneg (fun _ => by positivity)
  have hmul := (mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ V+1))
  rw [mul_div_cancel₀ _ (by positivity : V+1≠0)] at hmul
  change _ ≤ inverseForm (theta m ell (coreEquiv.symm g))/2+remainingTimeComplete F μ (theta m ell) g+
    V*normTime F μ (theta m ell) g at hb
  nlinarith only [hi,hb,hmul,hnorm]

open SourceBulkTimeEnergyBudget SourceScalarSignedInverseReturn SourceInverseNeutralRemainderClosed

/-- The original complete cost consumes the time remainder with its whole scalar vacuum offset removed. -/
theorem actual_original_shifted_time_budget (sharp : Bool) (μ : ℝ) (hμ : 0 < μ)
    (hgap : 2*sourceTime 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-2*sourceTime 0))*
            remainingTimeComplete F μ (theta m ell) g := by
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
  obtain ⟨NE,hE⟩ := actual_shifted_time_energy_budget μ hμ g δ hδ
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
  change P*(v*timeEnergy F μ (theta m ell) g) ≤ P*(δ+remainingTimeComplete F μ (theta m ell) g) at he
  have hfinal : closedJointCost sharp m ell F μ (g : H) (k : H)*v ≤
      v*ε+P*remainingTimeComplete F μ (theta m ell) g := by nlinarith only [hc,he,hd]
  have hb := (le_div_iff₀ hv).mpr hfinal
  calc
    _ ≤ (v*ε+P*remainingTimeComplete F μ (theta m ell) g)/v := hb
    _ = _ := by change _=ε+(P/v)*_;field_simp

end LowEnergy.SourceShiftedBulkTimeBudget
