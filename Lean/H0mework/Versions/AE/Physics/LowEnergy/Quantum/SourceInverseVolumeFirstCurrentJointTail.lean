import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentForceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentJointTail
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceInverseFirstCurrentGaugeJets SourceInverseFirstCurrentForceTail SourceScalarForceBudget
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventBandLimit
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ENNReal

private theorem scaled_target (C ε : ℝ) (hC : 0 ≤ C) (hε : 0<ε) :
    ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) ≤ ENNReal.ofReal ε := by
  rw [←ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0<C+1 := by linarith
  exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) (div_pos hε hp).le).trans_eq
    (mul_div_cancel₀ ε hp.ne')

private def CofinalEnergyTail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2)) ≤ ENNReal.ofReal ε

private theorem cofinal_energy_smul (f : ℕ → ℕ → Index → ℝ → ℂ) (c : ℂ)
    (hf : CofinalEnergyTail f) : CofinalEnergyTail (fun m ell F w => c*f m ell F w) := by
  intro ε hε
  have hc : 0<‖c‖^2+1 := by positivity
  obtain ⟨N,hN⟩ := hf (ε/(‖c‖^2+1)) (div_pos hε hc)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  simp only [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (mul_le_mul_of_nonneg_left hF (by positivity)).trans
    (scaled_target (‖c‖^2) ε (sq_nonneg _) hε)

private theorem cofinal_energy_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : CofinalEnergyTail f) (hg : CofinalEnergyTail g) :
    CofinalEnergyTail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell] with F hl hr
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring


/-- The exact original source mass normalizes the entire remaining response; no new scale is supplied. -/
def remainingProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (remainingResponse sharp m ell F g z (g : H))

private theorem mass_ne : (oscillatorMass : ℂ)≠0 := by
  exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ)≠0) (pow_ne_zero 2 source_time_nonzero))

private theorem actual_reduced_profile (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) (w : ℝ) :
    jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k=
      ((oscillatorMass : ℂ)⁻¹/6)*filteredProfile sharp m ell F (line μ w) (coreEquiv.symm g) (coreEquiv.symm k)+
        remainingProfile sharp m ell F g k (line μ w) := by
  have h := congrArg (fun c : ℂ => (oscillatorMass : ℂ)⁻¹*c)
    (actual_joint_response sharp m ell F μ hμ g k w)
  rw [←mul_assoc,inv_mul_cancel₀ mass_ne,one_mul] at h
  exact h.trans (by unfold remainingProfile;ring)

private theorem filtered_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : QuantumTest) :
    Continuous (fun w : ℝ => filteredProfile sharp m ell F (line μ w) g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc (u v : QuantumTest) : Continuous (fun w : ℝ =>
      inner ℂ (embed v) (wholeResponse sharp m ell F (line μ w) (embed u))) := by
    unfold wholeResponse
    exact continuous_const.inner (((hr.mul continuous_const).mul hr).clm_apply continuous_const)
  have he : (fun w : ℝ => filteredProfile sharp m ell F (line μ w) g k)=fun w =>
      inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed (SourceGaugeCoframeJets.G (SourceGaugeCoframeJets.G g))))+
      2*inner ℂ (embed (SourceGaugeCoframeJets.G k)) (wholeResponse sharp m ell F (line μ w) (embed (SourceGaugeCoframeJets.G g)))+
      inner ℂ (embed (SourceGaugeCoframeJets.G (SourceGaugeCoframeJets.G k))) (wholeResponse sharp m ell F (line μ w) (embed g))+
      3*inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed (SourceGaugeCoframeJets.G g)))+
      3*inner ℂ (embed (SourceGaugeCoframeJets.G k)) (wholeResponse sharp m ell F (line μ w) (embed g))+
      2*inner ℂ (embed k) (wholeResponse sharp m ell F (line μ w) (embed g)) :=
    funext (fun w => actual_filtered_profile sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k)
  rw [he]
  exact (((((hc _ _).add ((hc _ _).const_mul 2)).add (hc _ _)).add
    ((hc _ _).const_mul 3)).add ((hc _ _).const_mul 3)).add ((hc _ _).const_mul 2)

/-- The original closed joint cost has precisely the remaining signed response as its next tail responsibility. -/
theorem actual_joint_remaining_tail_iff (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    (∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
    (∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖remainingProfile sharp m ell F g k (line μ w)‖^2)) ≤ ENNReal.ofReal ε) := by
  let J : ℕ → ℕ → Index → ℝ → ℂ := fun m ell F w =>
    jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k
  let Q : ℕ → ℕ → Index → ℝ → ℂ := fun m ell F w => remainingProfile sharp m ell F g k (line μ w)
  let P : ℕ → ℕ → Index → ℝ → ℂ := fun m ell F w =>
    ((oscillatorMass : ℂ)⁻¹/6)*filteredProfile sharp m ell F (line μ w) (coreEquiv.symm g) (coreEquiv.symm k)
  have hP : CofinalEnergyTail P := by
    apply cofinal_energy_smul
    intro ε hε
    obtain ⟨N,hN⟩ := actual_filtered_profile_tail sharp μ hμ (coreEquiv.symm g) (coreEquiv.symm k) ε hε
    exact ⟨N,fun m hm ell hell => Eventually.of_forall (hN m hm ell hell)⟩
  have hc : ∀ m ell F,Continuous (P m ell F) := fun m ell F =>
    (filtered_continuous sharp m ell F μ hμ (coreEquiv.symm g) (coreEquiv.symm k)).const_mul _
  have he : J=fun m ell F w => P m ell F w+Q m ell F w := by
    funext m ell F w
    exact actual_reduced_profile sharp m ell F μ hμ g k w
  have hJQ : CofinalEnergyTail J ↔ CofinalEnergyTail Q := by
    constructor
    · intro hj
      have hn := cofinal_energy_smul P (-1) hP
      have h := cofinal_energy_add (fun m ell F w => (-1 : ℂ)*P m ell F w) J
        (fun m ell F => (hc m ell F).const_mul (-1)) hn hj
      simpa only [he,neg_one_mul,neg_add_cancel_left] using h
    · intro hq
      rw [he]
      exact cofinal_energy_add P Q hc hP hq
  have hCJ :
      (∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
        ∀ᶠ F in (sourceFilter : Filter Index),closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
      CofinalEnergyTail J := by
    constructor <;> intro h ε hε
    · obtain ⟨N,hN⟩ := h ε hε
      refine ⟨N,fun m hm ell hell => ?_⟩
      filter_upwards [hN m hm ell hell] with F hF
      exact (actual_joint_closed_lintegral sharp m ell F μ hμ g k).trans_le (ENNReal.ofReal_le_ofReal hF)
    · obtain ⟨N,hN⟩ := h ε hε
      refine ⟨N,fun m hm ell hell => ?_⟩
      filter_upwards [hN m hm ell hell] with F hF
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp
        ((actual_joint_closed_lintegral sharp m ell F μ hμ g k).symm.trans_le hF)
  exact hCJ.trans hJQ
end LowEnergy.SourceInverseFirstCurrentJointTail
