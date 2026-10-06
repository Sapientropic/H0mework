import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceNativeCutoffContact
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.PositiveContractionRitt
open Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Op := E →L[ℂ] E

def gradient (Q : Op (E := E)) (n : ℕ) : Op (E := E) :=
  (n+1 : ℝ) • (Q^n*(1-Q))

private theorem first_peak (t : ℝ) (h0 : 0≤t) (h1 : t≤1) (n : ℕ) :
    (n+1 : ℝ)*t^n*(1-t)≤1 := by
  have hs : 0≤1-t := sub_nonneg.mpr h1
  have hh := Finset.single_le_sum
    (f := fun j => (1-t)^j*t^(n+1-j)*((n+1).choose j : ℝ))
    (fun j _ => by positivity) (show 1∈Finset.range (n+1+1) by simp)
  rw [←add_pow,show (1-t)+t=1 by ring,one_pow] at hh
  calc
    _ = (1-t)*t^n*(n+1 : ℝ) := by ring
    _ ≤ 1 := by
      simpa only [pow_one,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one] using hh

private theorem spectral_interval (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1)
    (t : ℝ) (ht : t∈spectrum ℝ Q) : 0≤t ∧ t≤1 := by
  refine ⟨spectrum_nonneg_of_nonneg h0 ht,?_⟩
  have hs : ∀ x∈spectrum ℝ Q,x≤1 :=
    (le_algebraMap_iff_spectrum_le (a := Q) (r := (1 : ℝ))).mp (by simpa using h1)
  exact hs t ht

private theorem gradient_cfc (Q : Op (E := E)) (h0 : 0≤Q) (n : ℕ) :
    cfc (fun t : ℝ => (n+1 : ℝ)*t^n*(1-t)) Q=gradient Q n := by
  have hQ : IsSelfAdjoint Q := .of_nonneg h0
  have hp : cfc (fun t : ℝ => t^n) Q=Q^n := cfc_pow_id Q n hQ
  have hs : cfc (fun t : ℝ => 1-t) Q=1-Q := by
    rw [cfc_sub (a := Q) (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      (hf := continuousOn_const) (hg := continuousOn_id),cfc_const 1 Q hQ,cfc_id' ℝ Q hQ]
    simp only [map_one]
  rw [cfc_mul (fun t : ℝ => (n+1 : ℝ)*t^n) (fun t : ℝ => 1-t) Q
    (by fun_prop) (by fun_prop),cfc_const_mul (n+1 : ℝ) (fun t : ℝ => t^n) Q (by fun_prop),hp,hs]
  exact (smul_mul_assoc (n+1 : ℝ) (Q^n) (1-Q)).symm

theorem gradient_norm (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (n : ℕ) :
    ‖gradient Q n‖≤1 := by
  rw [←gradient_cfc Q h0 n]
  apply norm_cfc_le (by norm_num)
  intro t ht
  obtain ⟨ht0,ht1⟩ := spectral_interval Q h0 h1 t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact first_peak t ht0 ht1 n

private theorem gradient_complement_cfc (Q : Op (E := E)) (h0 : 0≤Q) (n : ℕ) :
    cfc (fun t : ℝ => (n+1 : ℝ)*t^n*(1-t)^2) Q=gradient Q n*(1-Q) := by
  have hQ : IsSelfAdjoint Q := .of_nonneg h0
  have hs : cfc (fun t : ℝ => 1-t) Q=1-Q := by
    rw [cfc_sub (a := Q) (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      (hf := continuousOn_const) (hg := continuousOn_id),cfc_const 1 Q hQ,cfc_id' ℝ Q hQ]
    simp only [map_one]
  have hf : (fun t : ℝ => (n+1 : ℝ)*t^n*(1-t)^2)=
      fun t : ℝ => ((n+1 : ℝ)*t^n*(1-t))*(1-t) := by funext t;ring
  rw [hf,cfc_mul (fun t : ℝ => (n+1 : ℝ)*t^n*(1-t)) (fun t : ℝ => 1-t) Q
    (by fun_prop) (by fun_prop),gradient_cfc Q h0 n,hs]

theorem gradient_complement_norm (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (n : ℕ) :
    ‖gradient Q n*(1-Q)‖≤2/(n+2 : ℝ) := by
  rw [←gradient_complement_cfc Q h0 n]
  apply norm_cfc_le (by positivity)
  intro t ht
  obtain ⟨ht0,ht1⟩ := spectral_interval Q h0 h1 t ht
  have hs0 : 0≤1-t := sub_nonneg.mpr ht1
  have hs1 : 1-t≤1 := by linarith
  have hh := SourceNativeCutoffContact.squared_geometric_peak (1-t) hs0 hs1 n
  rw [show 1-(1-t)=t by ring] at hh
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (show (n+1 : ℝ)*t^n*(1-t)^2=(n+1 : ℝ)*(1-t)^2*t^n by ring) ▸ hh

private theorem gradient_range_tendsto (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (x : E) :
    Tendsto (fun n : ℕ => gradient Q n ((1-Q) x)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (2*‖x‖/ε)
  refine ⟨N,fun n hn => ?_⟩
  have hncast : (N : ℝ)≤n := by exact_mod_cast hn
  have hp : 0<(n+2 : ℝ) := by positivity
  have hlarge : 2*‖x‖/ε<(n+2 : ℝ) := hN.trans_le (by linarith)
  have hrate : 2/(n+2 : ℝ)*‖x‖<ε := by
    have hmul := (div_lt_iff₀ hε).mp hlarge
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hp).mpr
    simpa only [mul_comm] using hmul
  rw [dist_zero_right]
  have hb := (gradient Q n*(1-Q)).le_opNorm x
  exact (hb.trans (mul_le_mul_of_nonneg_right
    (gradient_complement_norm Q h0 h1 n) (norm_nonneg _))).trans_lt hrate

/-- The derivative peak vanishes strongly even when the complement has a
kernel; no injective inverse-radius premise is needed by the source history. -/
theorem gradient_strong (Q : Op (E := E)) (h0 : 0≤Q) (h1 : Q≤1) (x : E) :
    Tendsto (fun n : ℕ => gradient Q n x) atTop (𝓝 0) := by
  have hc : CauchySeq (fun n : ℕ => (Q^n) x) :=
    SourceRelativePowerTail.decreasing_distance_cauchy _
      (fun m n h => SourceRelativePowerTail.positive_power_distance Q h0 h1 x h)
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  have hQy : Q y=y := by
    have hleft := (Q.continuous.tendsto y).comp hy
    have hright := hy.comp (tendsto_add_atTop_nat 1)
    have he (n : ℕ) : Q ((Q^n) x)=(Q^(n+1)) x := by
      rw [pow_succ',mul_apply_eq_comp]
    exact tendsto_nhds_unique (hleft.congr' (Filter.Eventually.of_forall he)) hright
  have hzero (n : ℕ) : gradient Q n y=0 := by
    simp only [gradient,smul_apply,mul_apply_eq_comp,sub_apply,one_apply_eq_self,hQy,
      sub_self,map_zero,smul_zero]
  have hrange (M : ℕ) : ∃ z : E,x-(Q^M) x=(1-Q) z := by
    induction M with
    | zero => exact ⟨0,by simp⟩
    | succ M ih =>
      obtain ⟨z,hz⟩ := ih
      refine ⟨z+(Q^M) x,?_⟩
      rw [map_add,←hz,pow_succ']
      simp only [sub_apply,one_apply_eq_self,mul_apply_eq_comp]
      abel
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨M,hM⟩ := Metric.tendsto_atTop.1 hy (ε/3) (by positivity)
  obtain ⟨z,hz⟩ := hrange M
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 (gradient_range_tendsto Q h0 h1 z) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hnear : ‖(Q^M) x-y‖<ε/3 := by simpa only [dist_eq_norm] using hM M le_rfl
  have hsmall : ‖gradient Q n ((1-Q) z)‖<ε/3 := by simpa only [dist_zero_right] using hN n hn
  have he : gradient Q n x=gradient Q n ((1-Q) z)+gradient Q n ((Q^M) x-y) := by
    rw [←hz,←map_add,sub_add_sub_cancel,map_sub,hzero,sub_zero]
  rw [dist_zero_right,he]
  have hb := ((gradient Q n).le_opNorm ((Q^M) x-y)).trans
    (mul_le_mul_of_nonneg_right (gradient_norm Q h0 h1 n) (norm_nonneg _))
  rw [one_mul] at hb
  exact (norm_add_le _ _).trans_lt (by linarith)

end LowEnergy.PositiveContractionRitt
