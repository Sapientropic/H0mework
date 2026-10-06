import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRittJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ClockPhiZeroOrderCoefficient
open ClockPhiRittJets

def profile (s : ℝ) (m ell : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let t := theta s m ell
  let b := beta s m ell
  !![(2*s*b-t)*t, -2*s^2*b*t;
     -2*s^2*b*t, s^2*(t+2*s*b)*t]

def derivative (s : ℝ) (m ell : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let t := theta s m ell
  let b := beta s m ell
  let c := beta2 s m ell
  !![2*s*(c*t+b^2), -4*s*b*t-2*s^2*(c*t+b^2);
     -4*s*b*t-2*s^2*(c*t+b^2),
     2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2)]

def zero (s : ℝ) (m ell : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => -s^2*(1-s^2)*derivative s m ell i j+
    (60*s+s^3)*profile s m ell i j

private theorem abs_add_bound (a b : ℝ) : |a+b| ≤ |a|+|b| := by
  apply abs_le.mpr
  constructor <;> have ha := le_abs_self a <;> have hb := le_abs_self b <;>
    have hna := neg_abs_le a <;> have hnb := neg_abs_le b <;> linarith

private theorem abs_sub_bound (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_bound a (-b)

private theorem poly_budget (s t b c r : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 0 ≤ r)
    (ht : |t| ≤ 1) (hst : s*|t| ≤ 2*r)
    (hsb : s*|b| ≤ 2) (hs2b : s^2*|b| ≤ 4*r)
    (hs3c : s^3*|c| ≤ 12*r) :
    ∀ i j : Fin 2,
      |(-s^2*(1-s^2)*
        (!![2*s*(c*t+b^2), -4*s*b*t-2*s^2*(c*t+b^2);
           -4*s*b*t-2*s^2*(c*t+b^2),
           2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2)] : Matrix (Fin 2) (Fin 2) ℝ) i j+
        (60*s+s^3)*
        (!![(2*s*b-t)*t, -2*s^2*b*t;
           -2*s^2*b*t, s^2*(t+2*s*b)*t] : Matrix (Fin 2) (Fin 2) ℝ) i j)| ≤
      704*r := by
  let T := |t|
  let B := |b|
  let C := |c|
  have hT : 0 ≤ T := abs_nonneg t
  have hB : 0 ≤ B := abs_nonneg b
  have hC : 0 ≤ C := abs_nonneg c
  have hs2 : 0 ≤ s^2 := sq_nonneg s
  have hs3 : 0 ≤ s^3 := by positivity
  have hs4 : 0 ≤ s^4 := by positivity
  have hs5 : 0 ≤ s^5 := by positivity
  have hT2 : T^2 ≤ T := by nlinarith only [hT,ht,sq_nonneg (T-1)]
  have hs2le : s^2 ≤ 1 := by nlinarith only [hs,hs1,sq_nonneg (s-1)]
  have hs3le : s^3 ≤ s^2 := by nlinarith only [hs,hs1,mul_nonneg hs2 (sub_nonneg.mpr hs1)]
  have hs4le : s^4 ≤ s^2 := by nlinarith only [hs2le,hs2,sq_nonneg (s^2-1)]
  have hs5le : s^5 ≤ s^3 := by nlinarith only [hs2le,hs3,mul_nonneg hs3 (sub_nonneg.mpr hs2le)]
  have hst2 : s*T^2 ≤ 2*r := by
    calc s*T^2 ≤ s*T := by nlinarith only [hs,hT2]
         _ ≤ 2*r := hst
  have hs2bT : s^2*B*T ≤ 4*r := by
    calc _ ≤ s^2*B := by
           have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ s^2*B)
           nlinarith only [hh]
         _ ≤ 4*r := hs2b
  have hs3cT : s^3*C*T ≤ 12*r := by
    calc _ ≤ s^3*C := by
           have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ s^3*C)
           nlinarith only [hh]
         _ ≤ 12*r := hs3c
  have hs3b2 : s^3*B^2 ≤ 8*r := by
    calc _ = (s*B)*(s^2*B) := by ring
         _ ≤ 2*(s^2*B) := mul_le_mul_of_nonneg_right hsb (by positivity)
         _ ≤ 2*(4*r) := mul_le_mul_of_nonneg_left hs2b (by norm_num)
         _ = 8*r := by ring
  have hs3bT : s^3*B*T ≤ 4*r := by
    calc _ ≤ s^2*B*T := by
           have hh := mul_le_mul_of_nonneg_right hs3le (by positivity : 0 ≤ B*T)
           nlinarith only [hh]
         _ ≤ 4*r := hs2bT
  have hs4cT : s^4*C*T ≤ 12*r := by
    calc _ ≤ s^3*C*T := by
           have hh := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ s^3*C*T)
           nlinarith only [hh]
         _ ≤ 12*r := hs3cT
  have hs4b2 : s^4*B^2 ≤ 8*r := by
    calc _ ≤ s^3*B^2 := by
           have hh := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ s^3*B^2)
           nlinarith only [hh]
         _ ≤ 8*r := hs3b2
  have hs5cT : s^5*C*T ≤ 12*r := by
    calc _ ≤ s^3*C*T := by
           have hh := mul_le_mul_of_nonneg_right hs5le (by positivity : 0 ≤ C*T)
           nlinarith only [hh]
         _ ≤ 12*r := hs3cT
  have hs5b2 : s^5*B^2 ≤ 8*r := by
    calc _ ≤ s^3*B^2 := by
           have hh := mul_le_mul_of_nonneg_right hs5le (by positivity : 0 ≤ B^2)
           nlinarith only [hh]
         _ ≤ 8*r := hs3b2
  have hs3T2 : s^3*T^2 ≤ 2*r := by
    calc _ ≤ s*T^2 := by
           have hh := mul_le_mul_of_nonneg_right hs2le (by positivity : 0 ≤ s*T^2)
           nlinarith only [hh]
         _ ≤ 2*r := hst2
  have hs4bT : s^4*B*T ≤ 4*r := by
    calc _ ≤ s^2*B*T := by
           have hh := mul_le_mul_of_nonneg_right hs4le (by positivity : 0 ≤ B*T)
           nlinarith only [hh]
         _ ≤ 4*r := hs2bT
  have hcoef : 0 ≤ 60*s+s^3 ∧ 60*s+s^3 ≤ 61*s := by
    constructor
    · positivity
    · nlinarith only [hs,hs1,hs2le]
  have hder : 0 ≤ s^2*(1-s^2) ∧ s^2*(1-s^2) ≤ s^2 := by
    constructor
    · exact mul_nonneg hs2 (sub_nonneg.mpr hs2le)
    · nlinarith only [hs2,sq_nonneg (s^2)]
  have hcp : |c*t+b^2| ≤ C*T+B^2 := by
    calc
      _ ≤ |c*t|+|b^2| := abs_add_bound _ _
      _ = C*T+B^2 := by simp only [abs_mul,abs_pow,show |c|=C by rfl,
        show |t|=T by rfl,show |b|=B by rfl]
  have he00 : |(2*s*b-t)*t| ≤ (2*s*B+T)*T := by
    calc
      _ = |2*s*b-t| * T := by rw [abs_mul]
      _ ≤ (|2*s*b|+T)*T :=
        mul_le_mul_of_nonneg_right (abs_sub_bound _ _) hT
      _ = (2*s*B+T)*T := by
        simp only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*s)]
        ring
  have hd00 : |2*s*(c*t+b^2)| ≤ 2*s*(C*T+B^2) := by
    calc
      _ = (2*s)* |c*t+b^2| := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*s)]
      _ ≤ 2*s*(C*T+B^2) :=
        mul_le_mul_of_nonneg_left hcp (by positivity)
  have he01 : |-2*s^2*b*t| ≤ 2*s^2*B*T := by
    change |-2*s^2*b*t| ≤ 2*s^2*|b| * |t|
    simp [abs_mul,abs_pow,abs_of_nonneg hs]
  have hd01 : |-4*s*b*t-2*s^2*(c*t+b^2)| ≤
      4*s*B*T+2*s^2*(C*T+B^2) := by
    have h4 : |-4*s*b*t|=4*s*B*T := by
      simp only [abs_mul,abs_neg,abs_of_nonneg hs]
      ring
    have h2 : |2*s^2*(c*t+b^2)| ≤ 2*s^2*(C*T+B^2) := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)*s^2)]
      exact mul_le_mul_of_nonneg_left hcp (by positivity)
    calc
      _ ≤ |-4*s*b*t|+|2*s^2*(c*t+b^2)| := abs_sub_bound _ _
      _ ≤ 4*s*B*T+2*s^2*(C*T+B^2) := by rw [h4]; exact add_le_add_right h2 _
  have he11 : |s^2*(t+2*s*b)*t| ≤ s^2*(T+2*s*B)*T := by
    calc
      _ = s^2* |t+2*s*b| * T := by
        rw [abs_mul,abs_mul,abs_of_nonneg hs2]
      _ ≤ s^2*(T+|2*s*b|)*T := by
        have hh := abs_add_bound t (2*s*b)
        have hhh := mul_le_mul_of_nonneg_left hh hs2
        have hhhh := mul_le_mul_of_nonneg_right hhh hT
        exact hhhh
      _ = s^2*(T+2*s*B)*T := by
        simp only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)*s)]
        ring
  have hd11 : |2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2)| ≤
      2*s*T^2+8*s^2*B*T+2*s^3*(C*T+B^2) := by
    have h12 := abs_add_bound (2*s*t^2) (8*s^2*b*t)
    have h123 := abs_add_bound (2*s*t^2+8*s^2*b*t) (2*s^3*(c*t+b^2))
    have hh := mul_le_mul_of_nonneg_left hcp (by positivity : 0 ≤ (2:ℝ)*s^3)
    calc
      _ ≤ |2*s*t^2+8*s^2*b*t|+|2*s^3*(c*t+b^2)| := h123
      _ ≤ |2*s*t^2|+|8*s^2*b*t|+|2*s^3*(c*t+b^2)| := by linarith only [h12]
      _ ≤ 2*s*T^2+8*s^2*B*T+2*s^3*(C*T+B^2) := by
        simp only [abs_mul,abs_pow,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)*s),
          abs_of_nonneg (by positivity : 0 ≤ (8:ℝ)*s^2),
          abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)*s^3)] at ⊢
        nlinarith only [hh]
  have hE00 : s*|(2*s*b-t)*t| ≤ 10*r := by
    have h := mul_le_mul_of_nonneg_left he00 hs
    nlinarith only [h,hs2bT,hst2]
  have hD00 : s^2*|2*s*(c*t+b^2)| ≤ 40*r := by
    have h := mul_le_mul_of_nonneg_left hd00 hs2
    nlinarith only [h,hs3cT,hs3b2]
  have hE01 : |-2*s^2*b*t| ≤ 8*r := by
    nlinarith only [he01,hs2bT]
  have hD01 : s^2*|-4*s*b*t-2*s^2*(c*t+b^2)| ≤ 56*r := by
    have h := mul_le_mul_of_nonneg_left hd01 hs2
    nlinarith only [h,hs3bT,hs4cT,hs4b2]
  have hE11 : s*|s^2*(t+2*s*b)*t| ≤ 10*r := by
    have h := mul_le_mul_of_nonneg_left he11 hs
    nlinarith only [h,hs3T2,hs4bT]
  have hD11 : s^2*|2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2)| ≤ 76*r := by
    have h := mul_le_mul_of_nonneg_left hd11 hs2
    nlinarith only [h,hs3T2,hs4bT,hs5cT,hs5b2]
  have hcoef1 : 60*s+s^3 ≤ 61 := by
    linarith only [hcoef.2,hs1]
  have hbasic (e d : ℝ) :
      |-s^2*(1-s^2)*d+(60*s+s^3)*e| ≤
        s^2*|d|+(60*s+s^3)*|e| := by
    have h := abs_add_bound (-s^2*(1-s^2)*d) ((60*s+s^3)*e)
    have he : |-s^2*(1-s^2)*d|=s^2*(1-s^2)*|d| := by
      rw [abs_mul,show -s^2*(1-s^2)=-(s^2*(1-s^2)) by ring,
        abs_neg,abs_of_nonneg hder.1]
    have hf : |(60*s+s^3)*e|=(60*s+s^3)*|e| := by
      rw [abs_mul,abs_of_nonneg hcoef.1]
    rw [he,hf] at h
    have hg := mul_le_mul_of_nonneg_right hder.2 (abs_nonneg d)
    linarith only [h,hg]
  have hZ00 :
      |-s^2*(1-s^2)*(2*s*(c*t+b^2))+
          (60*s+s^3)*((2*s*b-t)*t)| ≤ 650*r := by
    have h := hbasic ((2*s*b-t)*t) (2*s*(c*t+b^2))
    have hc := mul_le_mul_of_nonneg_right hcoef.2 (abs_nonneg ((2*s*b-t)*t))
    nlinarith only [h,hc,hE00,hD00]
  have hZ01 :
      |-s^2*(1-s^2)*(-4*s*b*t-2*s^2*(c*t+b^2))+
          (60*s+s^3)*(-2*s^2*b*t)| ≤ 544*r := by
    have h := hbasic (-2*s^2*b*t) (-4*s*b*t-2*s^2*(c*t+b^2))
    have hc := mul_le_mul_of_nonneg_right hcoef1 (abs_nonneg (-2*s^2*b*t))
    nlinarith only [h,hc,hE01,hD01]
  have hZ11 :
      |-s^2*(1-s^2)*(2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2))+
          (60*s+s^3)*(s^2*(t+2*s*b)*t)| ≤ 686*r := by
    have h := hbasic (s^2*(t+2*s*b)*t)
      (2*s*t^2+8*s^2*b*t+2*s^3*(c*t+b^2))
    have hc := mul_le_mul_of_nonneg_right hcoef.2
      (abs_nonneg (s^2*(t+2*s*b)*t))
    nlinarith only [h,hc,hE11,hD11]
  have h700 : 650*r ≤ 704*r := by nlinarith only [hr]
  have h701 : 544*r ≤ 704*r := by nlinarith only [hr]
  have h702 : 686*r ≤ 704*r := by nlinarith only [hr]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hZ00.trans h700
  · simpa using hZ01.trans h701
  · simpa using hZ01.trans h701
  · simpa using hZ11.trans h702

/-- Every entry of the original two-seed zero-order profile has a common cutoff
price, including both off-diagonal columns. -/
theorem zero_bound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell) (i j : Fin 2) :
    |zero s m ell i j| ≤ 704/(m+2:ℝ) := by
  let t := theta s m ell
  let b := beta s m ell
  let c := beta2 s m ell
  have ht := theta_bounds s hs hs1 m ell hml
  have hb := beta_bounds s hs hs1 m ell hml
  have hc := beta2_bound s hs hs1 m ell hm hml
  have hst : s*|t| ≤ 2*(1/(m+2:ℝ)) := by
    simpa [t,div_eq_mul_inv] using ht.2
  have hs2b : s^2*|b| ≤ 4*(1/(m+2:ℝ)) := by
    simpa [b,div_eq_mul_inv] using hb.2
  have hs3c : s^3*|c| ≤ 12*(1/(m+2:ℝ)) := by
    simpa [c,div_eq_mul_inv] using hc
  have hr : 0 ≤ 1/(m+2:ℝ) := by positivity
  have h := poly_budget s t b c (1/(m+2:ℝ)) hs hs1 hr
    ht.1 hst hb.1 hs2b hs3c i j
  simpa only [zero,profile,derivative,t,b,c,div_eq_mul_inv,one_mul] using h

end LowEnergy.ClockPhiZeroOrderCoefficient
