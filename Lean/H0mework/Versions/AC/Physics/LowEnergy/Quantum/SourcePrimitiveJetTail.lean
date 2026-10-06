import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCurrentEndpointEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourcePrimitiveJetTail
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm
open SourceCurrentEndpointEnergy SourceMixedNativeReturn SourceFixedJetBudget
open SourceHamiltonianScaleJet SourceCoframeVolumeCurrent SourceCoframeDilation
open GaussUnitaryHistory SourceResolventBandLimit
open scoped InnerProductSpace

def shiftedD : CoreEnd := dilation+(2*Complex.I) • 1

private theorem scale_to_shift (A : CoreEnd) (h : scaleDerivative A=(-3 : ℂ) • A)
    (f : QuantumTest) : dilation (A f)=A (shiftedD f) := by
  have he := LinearMap.congr_fun h f
  change (3*Complex.I/2) • (dilation (A f)-A (dilation f))=(-3 : ℂ) • A f at he
  have hc : (-2*Complex.I/3)*(3*Complex.I/2)=(1 : ℂ) := by
    calc _ = -(Complex.I*Complex.I) := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  have he' := congrArg (fun x : QuantumTest => (-2*Complex.I/3) • x) he
  rw [smul_smul,smul_smul,hc,one_smul] at he'
  have hc' : (-2*Complex.I/3)*(-3 : ℂ)=2*Complex.I := by ring
  rw [hc'] at he'
  change dilation (A f)=A (dilation f+(2*Complex.I) • f)
  rw [map_add,map_smul]
  exact (sub_eq_iff_eq_add.mp he').trans (add_comm _ _)

theorem primitive_dilation (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    dilation (primitive sharp m ell f)=primitive sharp m ell (shiftedD f) :=
  scale_to_shift _ (primitive_scale sharp m ell) f

private theorem test_pair_ext (f g : QuantumTest)
    (h : ∀ a, sourcePair a f=sourcePair a g) : f=g := by
  have hz : inner ℂ (embed (f-g)) (embed (f-g))=0 := by
    calc
      _ = sourcePair (f-g) f-sourcePair (f-g) g := by
        conv_lhs => rw [show embed (f-g)=embed f-embed g from map_sub embed f g]
        exact inner_sub_right _ _ _
      _ = 0 := sub_eq_zero.mpr (h (f-g))
  apply sub_eq_zero.mp
  exact embed_injective (((inner_self_eq_zero (𝕜 := ℂ)).mp hz).trans (map_zero embed).symm)

private theorem primitive_reverse_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (primitiveAdjoint sharp m ell g)=sourcePair (primitive sharp m ell f) g := by
  have h := congrArg (starRingEnd ℂ) (primitive_pair sharp m ell g f)
  simp only [sourcePair,inner_conj_symm] at h
  exact h.symm

theorem primitive_adjoint_dilation (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    dilation (primitiveAdjoint sharp m ell f)=primitiveAdjoint sharp m ell (shiftedD f) := by
  apply test_pair_ext
  intro a
  rw [dilation_pair,primitive_reverse_pair,primitive_reverse_pair]
  have hs := primitive_dilation sharp m ell a
  change dilation (primitive sharp m ell a)=
    primitive sharp m ell (dilation a+(2*Complex.I) • a) at hs
  rw [map_add,map_smul] at hs
  have ha : primitive sharp m ell (dilation a)=
      dilation (primitive sharp m ell a)-(2*Complex.I) • primitive sharp m ell a := by
    exact eq_sub_iff_add_eq.mpr hs.symm
  rw [ha]
  change sourcePair (dilation (primitive sharp m ell a)-(2*Complex.I) • primitive sharp m ell a) f=
    sourcePair (primitive sharp m ell a) (dilation f+(2*Complex.I) • f)
  simp only [sourcePair,map_sub,map_smul,map_add,inner_sub_left,inner_add_right,
    inner_smul_left,inner_smul_right,map_mul,map_ofNat,Complex.conj_I]
  have hd := dilation_pair (primitive sharp m ell a) f
  change inner ℂ (embed (primitive sharp m ell a)) (embed (dilation f))=
    inner ℂ (embed (dilation (primitive sharp m ell a))) (embed f) at hd
  rw [hd]
  ring

private theorem iterate_shift (A : CoreEnd) (h : ∀ f, dilation (A f)=A (shiftedD f))
    (r : ℕ) (f : QuantumTest) : (dilation^r) (A f)=A ((shiftedD^r) f) := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ',pow_succ']
    change dilation ((dilation^r) (A f))=A (shiftedD ((shiftedD^r) f))
    rw [ih,h]

theorem primitive_jet_return (sharp : Bool) (m ell r : ℕ) (f : QuantumTest) :
    (dilation^r) (primitive sharp m ell f)=primitive sharp m ell ((shiftedD^r) f) :=
  iterate_shift _ (primitive_dilation sharp m ell) r f

theorem primitive_adjoint_jet_return (sharp : Bool) (m ell r : ℕ) (f : QuantumTest) :
    (dilation^r) (primitiveAdjoint sharp m ell f)=primitiveAdjoint sharp m ell ((shiftedD^r) f) :=
  iterate_shift _ (primitive_adjoint_dilation sharp m ell) r f

theorem primitive_jet_tail (sharp : Bool) (r : ℕ) (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed ((dilation^r) (primitive sharp m ell f))‖ ≤ ε := by
  simp only [primitive_jet_return]
  exact actual_primitive_tail sharp ((shiftedD^r) f)

theorem primitive_adjoint_jet_tail (sharp : Bool) (r : ℕ) (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed ((dilation^r) (primitiveAdjoint sharp m ell f))‖ ≤ ε := by
  simp only [primitive_adjoint_jet_return]
  exact actual_primitive_adjoint_tail sharp ((shiftedD^r) f)

private theorem fixed_square_tail (A : ℕ → ℕ → QuantumTest) (r : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed ((dilation^r) (A m ell))‖ ≤ ε) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      C*‖embed ((dilation^r) (A m ell))‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := h (Real.sqrt (ε/(C+1))) (Real.sqrt_pos.mpr (div_pos hε hp))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have hb := pow_le_pow_left₀ (norm_nonneg _) (hN m hm ell hell) 2
  rw [Real.sq_sqrt (div_pos hε hp).le] at hb
  calc
    _ ≤ (C+1)*‖embed ((dilation^r) (A m ell))‖^2 := by
      nlinarith [sq_nonneg ‖embed ((dilation^r) (A m ell))‖]
    _ ≤ (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hb hp.le
    _ = _ := mul_div_cancel₀ ε hp.ne'

theorem left_primitive_budget_tail (sharp : Bool) (n r s : ℕ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      profileJetBudget n r s (primitiveAdjoint sharp m ell k) g ≤ ε := by
  induction n generalizing r s with
  | zero =>
    intro ε hε
    obtain ⟨N,hN⟩ := fixed_square_tail (fun m ell => primitiveAdjoint sharp m ell k) r
      (‖embed ((dilation^s) g)‖^2) (sq_nonneg _) (primitive_adjoint_jet_tail sharp r k) ε hε
    refine ⟨N,fun m hm ell hell => ?_⟩
    change ‖embed ((dilation^r) (primitiveAdjoint sharp m ell k))‖^2*‖embed ((dilation^s) g)‖^2 ≤ ε
    rw [mul_comm]
    exact hN m hm ell hell
  | succ n ih =>
    intro ε hε
    obtain ⟨N₁,h₁⟩ := ih (r+1) s (ε/4) (by positivity)
    obtain ⟨N₂,h₂⟩ := ih r (s+1) (ε/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
    have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
    change 2*(_+_) ≤ ε
    linarith

theorem right_primitive_budget_tail (sharp : Bool) (n r s : ℕ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      profileJetBudget n r s k (primitive sharp m ell g) ≤ ε := by
  induction n generalizing r s with
  | zero =>
    exact fixed_square_tail (fun m ell => primitive sharp m ell g) s
      (‖embed ((dilation^r) k)‖^2) (sq_nonneg _) (primitive_jet_tail sharp s g)
  | succ n ih =>
    intro ε hε
    obtain ⟨N₁,h₁⟩ := ih (r+1) s (ε/4) (by positivity)
    obtain ⟨N₂,h₂⟩ := ih r (s+1) (ε/4) (by positivity)
    refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
    have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
    have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
    change 2*(_+_) ≤ ε
    linarith

theorem actual_left_primitive_profile_tail (sharp : Bool) (n r s : ℕ)
    (μ : ℝ) (hμ : 0<μ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index, ∀ t : ℝ,
      (∫⁻ w : ℝ, ENNReal.ofReal
        (‖profileJet n r s F (line μ w) (primitiveAdjoint sharp m ell k) g t‖^2)) ≤
      ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<Real.pi/μ := div_pos Real.pi_pos hμ
  obtain ⟨N,hN⟩ := left_primitive_budget_tail sharp n r s k g (ε/(Real.pi/μ)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell F t => ?_⟩
  apply (actual_profile_jet_lintegral n r s F μ hμ (primitiveAdjoint sharp m ell k) g t).trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hell) hC.le).trans_eq
    (mul_div_cancel₀ ε hC.ne')

theorem actual_right_primitive_profile_tail (sharp : Bool) (n r s : ℕ)
    (μ : ℝ) (hμ : 0<μ) (k g : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index, ∀ t : ℝ,
      (∫⁻ w : ℝ, ENNReal.ofReal
        (‖profileJet n r s F (line μ w) k (primitive sharp m ell g) t‖^2)) ≤
      ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<Real.pi/μ := div_pos Real.pi_pos hμ
  obtain ⟨N,hN⟩ := right_primitive_budget_tail sharp n r s k g (ε/(Real.pi/μ)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell F t => ?_⟩
  apply (actual_profile_jet_lintegral n r s F μ hμ k (primitive sharp m ell g) t).trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hell) hC.le).trans_eq
    (mul_div_cancel₀ ε hC.ne')

end LowEnergy.SourcePrimitiveJetTail
