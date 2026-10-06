import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCoframeStrongJet
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCutoffDilationWard
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceHardyRetardedTail
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceFixedJetBudget
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeVolumeCurrent SourceCoframeStrongJet SourceCoframeScaleTransport
open SourceActualResolventEnergy SourceRelativePowerTail SourceHardyRetardedTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped InnerProductSpace Topology

def profile (r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) : ℂ :=
  inner ℂ (strongJet r k t) (finiteResolvent F z (strongJet s g t))

def profileJet : ℕ → ℕ → ℕ → Index → ℂ → QuantumTest → QuantumTest → ℝ → ℂ
  | 0,r,s,F,z,k,g,t => profile r s F z k g t
  | n+1,r,s,F,z,k,g,t => profileJet n (r+1) s F z k g t+profileJet n r (s+1) F z k g t

def profileJetBudget : ℕ → ℕ → ℕ → QuantumTest → QuantumTest → ℝ
  | 0,r,s,k,g => ‖embed ((dilation^r) k)‖^2*‖embed ((dilation^s) g)‖^2
  | n+1,r,s,k,g => 2*(profileJetBudget n (r+1) s k g+profileJetBudget n r (s+1) k g)

theorem profile_derivative (r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    HasDerivAt (profile r s F z k g)
      (profile (r+1) s F z k g t+profile r (s+1) F z k g t) t := by
  simpa only [profile,add_comm] using!
    (strong_jet_derivative r k t).inner ℂ (finite_profile_derivative F z s g t)

theorem profile_jet_derivative (n r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    HasDerivAt (profileJet n r s F z k g) (profileJet (n+1) r s F z k g t) t := by
  induction n generalizing r s with
  | zero => exact profile_derivative r s F z k g t
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

theorem profile_jet_one (r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    profileJet 1 r s F z k g t=profile (r+1) s F z k g t+profile r (s+1) F z k g t := rfl

theorem profile_jet_two (r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    profileJet 2 r s F z k g t=profile (r+2) s F z k g t+
      2*profile (r+1) (s+1) F z k g t+profile r (s+2) F z k g t := by
  simp only [profileJet,Nat.add_assoc]
  ring

theorem profile_jet_three (r s : ℕ) (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    profileJet 3 r s F z k g t=profile (r+3) s F z k g t+
      3*profile (r+2) (s+1) F z k g t+3*profile (r+1) (s+2) F z k g t+
      profile r (s+3) F z k g t := by
  simp only [profileJet,Nat.add_assoc]
  ring

theorem profile_jet_budget_nonneg (n r s : ℕ) (k g : QuantumTest) :
    0 ≤ profileJetBudget n r s k g := by
  induction n generalizing r s with
  | zero => exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  | succ n ih => exact mul_nonneg (by norm_num) (add_nonneg (ih _ _) (ih _ _))

theorem profile_jet_budget_three (r s : ℕ) (k g : QuantumTest) :
    profileJetBudget 3 r s k g=8*(
      ‖embed ((dilation^(r+3)) k)‖^2*‖embed ((dilation^s) g)‖^2+
      3*‖embed ((dilation^(r+2)) k)‖^2*‖embed ((dilation^(s+1)) g)‖^2+
      3*‖embed ((dilation^(r+1)) k)‖^2*‖embed ((dilation^(s+2)) g)‖^2+
      ‖embed ((dilation^r) k)‖^2*‖embed ((dilation^(s+3)) g)‖^2) := by
  simp only [profileJetBudget,Nat.add_assoc]
  ring

private theorem inner_square (x y : H) : ‖inner ℂ x y‖^2 ≤ ‖x‖^2*‖y‖^2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (inner ℂ x y)) (norm_inner_le_norm (𝕜 := ℂ) x y) 2

private theorem response_square_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    Integrable (fun ω : ℝ => ‖inner ℂ x (finiteResolvent F (line μ ω) y)‖^2) := by
  have hi : Integrable (fun ω : ℝ => ‖finiteResolvent F (line μ ω) y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integrable F μ hμ y
  have hc : Continuous (fun ω : ℝ => inner ℂ x (finiteResolvent F (line μ ω) y)) :=
    continuous_const.inner ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)
  apply (hi.const_mul (‖x‖^2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact inner_square _ _

private theorem response_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (x y : H) :
    (∫ ω : ℝ, ‖inner ℂ x (finiteResolvent F (line μ ω) y)‖^2) ≤
      (Real.pi/μ)*(‖x‖^2*‖y‖^2) := by
  have hi : Integrable (fun ω : ℝ => ‖finiteResolvent F (line μ ω) y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integrable F μ hμ y
  have h := integral_mono (response_square_integrable F μ hμ x y) (hi.const_mul (‖x‖^2))
    (fun ω => inner_square x (finiteResolvent F (line μ ω) y))
  have he : (∫ ω : ℝ, ‖finiteResolvent F (line μ ω) y‖^2)=(Real.pi/μ)*‖y‖^2 := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integral F μ hμ y
  rw [integral_const_mul,he] at h
  exact h.trans_eq (by ring)

private theorem two_square (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_add_le a b
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]

theorem profile_jet_frequency_continuous (n r s : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (k g : QuantumTest) (t : ℝ) : Continuous (fun ω => profileJet n r s F (line μ ω) k g t) := by
  induction n generalizing r s with
  | zero =>
    exact continuous_const.inner
      ((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const)
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

theorem profile_jet_square_integrable (n r s : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (k g : QuantumTest) (t : ℝ) :
    Integrable (fun ω : ℝ => ‖profileJet n r s F (line μ ω) k g t‖^2) := by
  induction n generalizing r s with
  | zero => exact response_square_integrable F μ hμ _ _
  | succ n ih =>
    have hi := ((ih (r+1) s).add (ih r (s+1))).const_mul 2
    apply hi.mono' ((profile_jet_frequency_continuous (n+1) r s F μ hμ k g t).norm.pow 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact two_square _ _

/-- The original finite resolvent is integrated first; the cost is independent of F and orbit time. -/
theorem actual_profile_jet_energy (n r s : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (k g : QuantumTest) (t : ℝ) :
    (∫ ω : ℝ, ‖profileJet n r s F (line μ ω) k g t‖^2) ≤
      (Real.pi/μ)*profileJetBudget n r s k g := by
  induction n generalizing r s with
  | zero => simpa only [profileJet,profileJetBudget,strong_jet_norm] using!
      response_energy F μ hμ (strongJet r k t) (strongJet s g t)
  | succ n ih =>
    have hl := profile_jet_square_integrable n (r+1) s F μ hμ k g t
    have hr := profile_jet_square_integrable n r (s+1) F μ hμ k g t
    have hm := integral_mono (profile_jet_square_integrable (n+1) r s F μ hμ k g t)
      ((hl.add hr).const_mul 2) (fun ω => two_square
        (profileJet n (r+1) s F (line μ ω) k g t) (profileJet n r (s+1) F (line μ ω) k g t))
    rw [integral_const_mul] at hm
    simp only [Pi.add_apply] at hm
    rw [integral_add hl hr] at hm
    have h := mul_le_mul_of_nonneg_left (add_le_add (ih (r+1) s) (ih r (s+1))) (by norm_num : (0 : ℝ) ≤ 2)
    exact hm.trans (h.trans_eq (by simp only [profileJetBudget]; ring))

theorem actual_profile_jet_lintegral (n r s : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (k g : QuantumTest) (t : ℝ) :
    (∫⁻ ω : ℝ, ENNReal.ofReal (‖profileJet n r s F (line μ ω) k g t‖^2)) ≤
      ENNReal.ofReal ((Real.pi/μ)*profileJetBudget n r s k g) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (profile_jet_square_integrable n r s F μ hμ k g t)
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (actual_profile_jet_energy n r s F μ hμ k g t)

/-- A transported compression is read by moving both fixed sources; no fixed-F scale derivative is asserted. -/
theorem moving_resolvent_pair (F : Index) (z : ℂ) (k g : QuantumTest) (t : ℝ) :
    inner ℂ (embed k) (((hilbertFlow t).conjStarAlgEquiv (finiteResolvent F z)) (embed g))=
      profile 0 0 F z k g (-t) := by
  have hn (x : H) : (hilbertFlow t).symm x=hilbertFlow (-t) x := by
    apply (hilbertFlow t).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hilbertFlow_add,add_neg_cancel,hilbertFlow_zero]
  have h := (hilbertFlow t).inner_map_map ((hilbertFlow t).symm (embed k))
    (finiteResolvent F z ((hilbertFlow t).symm (embed g)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℂ (embed k) (hilbertFlow t (finiteResolvent F z ((hilbertFlow t).symm (embed g))))=_
  rw [h,hn,hn,hilbertFlow_on_core,hilbertFlow_on_core]
  simp [profile,strongJet]

open GaussRadialDomain

def tailAction (m ell : ℕ) : CoreEnd :=
  (1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)

private theorem power_core (n : ℕ) (f : QuantumTest) :
    embed (((1-inverseAction)^n) f)=((1-inverseRadius)^n) (embed f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change embed (((1-inverseAction)^n) f-inverseAction (((1-inverseAction)^n) f))=
      ((1-inverseRadius)^n) (embed f)-inverseRadius (((1-inverseRadius)^n) (embed f))
    rw [map_sub,←inverse_core,ih]

theorem tail_core (m ell : ℕ) (f : QuantumTest) :
    embed (tailAction m ell f)=relativeTail m ell (embed f) := by
  simp only [tailAction,LinearMap.sub_apply,map_sub,power_core,relativeTail,sourceComplement,sub_apply]

private theorem power_dilation (n : ℕ) (f : QuantumTest) :
    dilation (((1-inverseAction)^n) f)=((1-inverseAction)^n) (dilation f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change dilation (((1-inverseAction)^n) f-inverseAction (((1-inverseAction)^n) f))=
      ((1-inverseAction)^n) (dilation f)-inverseAction (((1-inverseAction)^n) (dilation f))
    rw [map_sub]
    have hi := LinearMap.congr_fun SourceCutoffDilationWard.inverse_dilation.eq (((1-inverseAction)^n) f)
    change dilation (inverseAction (((1-inverseAction)^n) f))=
      inverseAction (dilation (((1-inverseAction)^n) f)) at hi
    rw [hi,ih]

theorem tail_dilation (m ell : ℕ) (f : QuantumTest) :
    dilation (tailAction m ell f)=tailAction m ell (dilation f) := by
  change dilation (((1-inverseAction)^(m+1)) f-((1-inverseAction)^(ell+1)) f)=
    ((1-inverseAction)^(m+1)) (dilation f)-((1-inverseAction)^(ell+1)) (dilation f)
  rw [map_sub,power_dilation,power_dilation]

private theorem dilation_tail_iterate (r m ell : ℕ) (f : QuantumTest) :
    (dilation^r) (tailAction m ell f)=tailAction m ell ((dilation^r) f) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ']
    change dilation ((dilation^r) (tailAction m ell f))=
      tailAction m ell (dilation ((dilation^r) f))
    rw [ih,tail_dilation]

theorem tail_jet_core (r m ell : ℕ) (f : QuantumTest) :
    embed ((dilation^r) (tailAction m ell f))=
      relativeTail m ell (embed ((dilation^r) f)) := by
  rw [dilation_tail_iterate,tail_core]

private theorem fixed_scaled_jet_tail (r : ℕ) (f : QuantumTest) (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      C*‖embed ((dilation^r) (tailAction m ell f))‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := original_relative_tail (embed ((dilation^r) f))
    (Real.sqrt (ε/(C+1))) (Real.sqrt_pos.mpr (div_pos hε hp))
  refine ⟨N,fun m hm ell hell => ?_⟩
  rw [tail_jet_core]
  have ht := hN m hm ell hell
  have hs := Real.sq_sqrt (div_pos hε hp).le
  have hb : ‖relativeTail m ell (embed ((dilation^r) f))‖^2 ≤ ε/(C+1) := by
    nlinarith [norm_nonneg (relativeTail m ell (embed ((dilation^r) f))),Real.sqrt_nonneg (ε/(C+1))]
  calc
    _  ≤  (C+1)*‖relativeTail m ell (embed ((dilation^r) f))‖^2 := by
      nlinarith [sq_nonneg ‖relativeTail m ell (embed ((dilation^r) f))‖]
    _  ≤  (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hb hp.le
    _ = ε := mul_div_cancel₀ ε hp.ne'

theorem fixed_left_jet_budget_tail (n r s : ℕ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      profileJetBudget n r s (tailAction m ell k) g ≤ ε := by
  induction n generalizing r s with
  | zero =>
    intro ε hε
    obtain ⟨N,hN⟩ := fixed_scaled_jet_tail r k (‖embed ((dilation^s) g)‖^2) (sq_nonneg _) ε hε
    refine ⟨N,fun m hm ell hell => ?_⟩
    change ‖embed ((dilation^r) (tailAction m ell k))‖^2*‖embed ((dilation^s) g)‖^2 ≤ ε
    rw [mul_comm]
    exact hN m hm ell hell
  | succ n ih =>
    intro ε hε
    obtain ⟨N₁,h₁⟩ := ih (r+1) s (ε/4) (by positivity)
    obtain ⟨N₂,h₂⟩ := ih r (s+1) (ε/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    have hleft := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
    have hright := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
    change 2*(_+_) ≤ ε
    linarith

theorem fixed_right_jet_budget_tail (n r s : ℕ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      profileJetBudget n r s k (tailAction m ell g) ≤ ε := by
  induction n generalizing r s with
  | zero => exact fixed_scaled_jet_tail s g (‖embed ((dilation^r) k)‖^2) (sq_nonneg _)
  | succ n ih =>
    intro ε hε
    obtain ⟨N₁,h₁⟩ := ih (r+1) s (ε/4) (by positivity)
    obtain ⟨N₂,h₂⟩ := ih r (s+1) (ε/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    have hleft := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
    have hright := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
    change 2*(_+_) ≤ ε
    linarith

/-- A fixed original left source carries the cutoff tail uniformly in F, orbit time, and upper cutoff. -/
theorem fixed_left_profile_tail (n r s : ℕ) (μ : ℝ) (hμ : 0<μ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index, ∀ t : ℝ,
      (∫⁻ ω : ℝ, ENNReal.ofReal (‖profileJet n r s F (line μ ω) (tailAction m ell k) g t‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<Real.pi/μ := div_pos Real.pi_pos hμ
  obtain ⟨N,hN⟩ := fixed_left_jet_budget_tail n r s k g (ε/(Real.pi/μ)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell F t => ?_⟩
  apply (actual_profile_jet_lintegral n r s F μ hμ (tailAction m ell k) g t).trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hell) hC.le).trans_eq
    (mul_div_cancel₀ ε hC.ne')

/-- The right endpoint uses the same original finite resolvent and the literal core restriction of theta. -/
theorem fixed_right_profile_tail (n r s : ℕ) (μ : ℝ) (hμ : 0<μ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index, ∀ t : ℝ,
      (∫⁻ ω : ℝ, ENNReal.ofReal (‖profileJet n r s F (line μ ω) k (tailAction m ell g) t‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<Real.pi/μ := div_pos Real.pi_pos hμ
  obtain ⟨N,hN⟩ := fixed_right_jet_budget_tail n r s k g (ε/(Real.pi/μ)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell F t => ?_⟩
  apply (actual_profile_jet_lintegral n r s F μ hμ k (tailAction m ell g) t).trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hell) hC.le).trans_eq
    (mul_div_cancel₀ ε hC.ne')

end LowEnergy.SourceFixedJetBudget
