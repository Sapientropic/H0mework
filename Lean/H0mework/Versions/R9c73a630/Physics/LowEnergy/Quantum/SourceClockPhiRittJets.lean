import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeCutoffContact
import Mathlib.Data.Nat.Choose.Cast

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ClockPhiRittJets

def theta (s : ℝ) (m ell : ℕ) : ℝ :=
  (1-s)^(m+1)-(1-s)^(ell+1)
def beta (s : ℝ) (m ell : ℕ) : ℝ :=
  (ell+1:ℝ)*(1-s)^ell-(m+1:ℝ)*(1-s)^m
def beta2 (s : ℝ) (m ell : ℕ) : ℝ :=
  (m:ℝ)*(m+1:ℝ)*(1-s)^(m-1)-
    (ell:ℝ)*(ell+1:ℝ)*(1-s)^(ell-1)

private theorem binomial_atom (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (n k : ℕ) (hk : k ≤ n) :
    ((n+1).choose (k+1):ℝ)*s^(k+1)*(1-s)^(n-k) ≤ 1 := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have ht := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+1-j)*((n+1).choose j:ℝ))
    (fun j _ => by positivity)
    (show k+1 ∈ Finset.range (n+1+1) by simp; omega)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at ht
  have he : n+1-(k+1)=n-k := by omega
  rw [he] at ht
  nlinarith only [ht]

private theorem first_atom (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*s*(1-s)^n ≤ 1 := by
  have h := binomial_atom s hs hs1 n 0 (Nat.zero_le n)
  simpa only [zero_add,pow_one,Nat.sub_zero,Nat.choose_one_right,
    Nat.cast_add,Nat.cast_one] using h

private theorem second_atom (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*s^2*(1-s)^n ≤ 2/(n+2:ℝ) := by
  have h := binomial_atom s hs hs1 (n+1) 1 (by omega)
  have hc : (((n+2).choose 2):ℝ)=(n+2:ℝ)*(n+1:ℝ)/2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have he : n+1-1=n := by omega
  simp only [he,hc] at h
  apply (le_div_iff₀ (by positivity : 0 < (n+2:ℝ))).mpr
  nlinarith only [h]

private theorem third_atom (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*(n+2:ℝ)*s^3*(1-s)^n ≤ 6/(n+3:ℝ) := by
  have h := binomial_atom s hs hs1 (n+2) 2 (by omega)
  have hc2 : (((n+3).choose 2):ℝ)=(n+3:ℝ)*(n+2:ℝ)/2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hcNat := Nat.choose_succ_right_eq (n+3) 2
  have hc := congrArg (fun j : ℕ => (j:ℝ)) hcNat
  have hc3 : (((n+3).choose 3):ℝ)=
      (n+3:ℝ)*(n+2:ℝ)*(n+1:ℝ)/6 := by
    simp only [show (2+1:ℕ)=3 by norm_num,Nat.cast_mul,
      show n+3-2=n+1 by omega,hc2,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat] at hc
    nlinarith only [hc]
  have he : n+2-2=n := by omega
  simp only [he,hc3] at h
  apply (le_div_iff₀ (by positivity : 0 < (n+3:ℝ))).mpr
  nlinarith only [h]

private theorem second_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*s^2*(1-s)^n ≤ 2/(n+2:ℝ) :=
  second_atom s hs hs1 n

private theorem third_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n:ℝ)*(n+1:ℝ)*s^3*(1-s)^(n-1) ≤ 6/(n+2:ℝ) := by
  cases n with
  | zero => norm_num
  | succ k =>
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    convert third_atom s hs hs1 k using 1 <;> ring

theorem theta_bounds (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m ell : ℕ) (hml : m ≤ ell) :
    |theta s m ell| ≤ 1 ∧ s*|theta s m ell| ≤ 2/(m+2:ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hq1 : 1-s ≤ 1 := by linarith
  have he := pow_le_pow_of_le_one hq hq1 (Nat.add_le_add_right hml 1)
  have ht : 0 ≤ theta s m ell := by
    unfold theta
    exact sub_nonneg.mpr he
  have htop : theta s m ell ≤ (1-s)^(m+1) := by
    unfold theta
    exact sub_le_self _ (pow_nonneg hq _)
  have hpow : (1-s)^(m+1) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hq hq1 (m+1)
  have hm : s*(1-s)^(m+1) ≤ 1/(m+2:ℝ) := by
    have h := first_atom s hs hs1 (m+1)
    apply (le_div_iff₀ (by positivity : 0 < (m+2:ℝ))).mpr
    have hc : (↑(m+1)+1:ℝ)=(m+2:ℝ) := by push_cast; ring
    rw [hc] at h
    simpa only [mul_comm,mul_left_comm,mul_assoc] using h
  rw [abs_of_nonneg ht]
  constructor
  · exact htop.trans hpow
  · have hh := mul_le_mul_of_nonneg_left htop hs
    have hd : 0 < (m+2:ℝ) := by positivity
    have htwo : 1/(m+2:ℝ) ≤ 2/(m+2:ℝ) := by
      apply (div_le_div_iff_of_pos_right hd).mpr
      norm_num
    exact (hh.trans hm).trans htwo

theorem beta_bounds (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m ell : ℕ) (hml : m ≤ ell) :
    s*|beta s m ell| ≤ 2 ∧ s^2*|beta s m ell| ≤ 4/(m+2:ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hb : |beta s m ell| ≤
      (ell+1:ℝ)*(1-s)^ell+(m+1:ℝ)*(1-s)^m := by
    unfold beta
    have ha : 0 ≤ (ell+1:ℝ)*(1-s)^ell := by positivity
    have hb : 0 ≤ (m+1:ℝ)*(1-s)^m := by positivity
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hfirst (k : ℕ) : s*((k+1:ℝ)*(1-s)^k) ≤ 1 := by
    convert first_atom s hs hs1 k using 1
    ring
  have hsecond (k : ℕ) : s^2*((k+1:ℝ)*(1-s)^k) ≤ 2/(k+2:ℝ) := by
    convert second_peak s hs hs1 k using 1
    ring
  have hden : 2/(ell+2:ℝ) ≤ 2/(m+2:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.add_le_add_right hml 2
  constructor
  · have h := mul_le_mul_of_nonneg_left hb hs
    calc
      _ ≤ s*((ell+1:ℝ)*(1-s)^ell+(m+1:ℝ)*(1-s)^m) := h
      _ = s*((ell+1:ℝ)*(1-s)^ell)+s*((m+1:ℝ)*(1-s)^m) := by ring
      _ ≤ 2 := by linarith only [hfirst ell,hfirst m]
  · have h := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
    calc
      _ ≤ s^2*((ell+1:ℝ)*(1-s)^ell+(m+1:ℝ)*(1-s)^m) := h
      _ = s^2*((ell+1:ℝ)*(1-s)^ell)+s^2*((m+1:ℝ)*(1-s)^m) := by ring
      _ ≤ 2/(ell+2:ℝ)+2/(m+2:ℝ) := add_le_add (hsecond ell) (hsecond m)
      _ ≤ 2/(m+2:ℝ)+2/(m+2:ℝ) := add_le_add_left hden _
      _ = 4/(m+2:ℝ) := by ring

theorem beta2_bound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell) :
    s^3*|beta2 s m ell| ≤ 12/(m+2:ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hb : |beta2 s m ell| ≤
      (m:ℝ)*(m+1:ℝ)*(1-s)^(m-1)+
      (ell:ℝ)*(ell+1:ℝ)*(1-s)^(ell-1) := by
    unfold beta2
    have ha : 0 ≤ (m:ℝ)*(m+1:ℝ)*(1-s)^(m-1) := by positivity
    have hb : 0 ≤ (ell:ℝ)*(ell+1:ℝ)*(1-s)^(ell-1) := by positivity
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hden : 6/(ell+2:ℝ) ≤ 6/(m+2:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.add_le_add_right hml 2
  have h := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ s^3)
  have hm' := third_peak s hs hs1 m
  have he' := third_peak s hs hs1 ell
  calc
    _ ≤ s^3*((m:ℝ)*(m+1:ℝ)*(1-s)^(m-1)+
      (ell:ℝ)*(ell+1:ℝ)*(1-s)^(ell-1)) := h
    _ = (m:ℝ)*(m+1:ℝ)*s^3*(1-s)^(m-1)+
      (ell:ℝ)*(ell+1:ℝ)*s^3*(1-s)^(ell-1) := by ring
    _ ≤ 6/(m+2:ℝ)+6/(ell+2:ℝ) := add_le_add hm' he'
    _ ≤ 6/(m+2:ℝ)+6/(m+2:ℝ) := add_le_add_right hden _
    _ = 12/(m+2:ℝ) := by ring

end LowEnergy.ClockPhiRittJets
