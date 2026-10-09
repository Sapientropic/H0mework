import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceBoundedInsertionTime
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceBoundedInsertionTail
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory SourceBoundedInsertionResponse
open SourceBoundedInsertionTime SourceRelativePowerTail SourceRetardedForcingTail
open SourceRetardedBandCurrent SourceActualResolventEnergy SourceInverseSourceLeg
open SourceResolventBandLimit FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped Topology InnerProductSpace

private theorem young (a b δ : ℝ) (hδ : 0<δ) : a*b ≤ δ*a^2+(4*δ)⁻¹*b^2 := by
  have he : (4*δ)*((4*δ)⁻¹*b^2)=b^2 := by rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
  nlinarith [sq_nonneg (2*δ*a-b)]

private theorem energy_int (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    Integrable (fun w => ‖finiteResolvent F (line μ w) x‖^2) := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integrable F μ hμ x
private theorem energy_mass (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫ w : ℝ,‖finiteResolvent F (line μ w) x‖^2)=Real.pi/μ*‖x‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integral F μ hμ x

private theorem inserted_energy_int (F : Index) (μ : ℝ) (hμ : 0<μ) (B : H →L[ℂ] H) (g : H) :
    Integrable (fun w => ‖B (finiteResolvent F (line μ w) g)‖^2) := by
  have hc : Continuous (fun w => B (finiteResolvent F (line μ w) g)) :=
    B.continuous.comp ((finite_frequency_continuous μ hμ F).clm_apply continuous_const)
  apply ((energy_int F μ hμ g).const_mul (‖B‖^2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall (fun w => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_pow,Pi.pow_apply] using! pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2)

private theorem amplitude_energy_bound (F : Index) (μ : ℝ) (hμ : 0<μ) (B : H →L[ℂ] H)
    (g k : diagonal.domain) (δ : ℝ) (hδ : 0<δ) :
    (∫ w : ℝ,‖amplitude F μ B (g : H) (k : H) w‖) ≤
      δ*(Real.pi/μ*‖(k : H)‖^2)+(4*δ)⁻¹*(∫ w : ℝ,‖B (finiteResolvent F (line μ w) (g : H))‖^2) := by
  have ha := ((actual_full_frequency_response μ hμ B g k).1 F).norm
  have hk := energy_int F μ hμ (k : H)
  have hb := inserted_energy_int F μ hμ B (g : H)
  have hi := integral_mono ha ((hk.const_mul δ).add (hb.const_mul ((4*δ)⁻¹))) (fun w => by
    rw [actual_causal_pair F μ hμ]
    have hn := norm_inner_le_norm (𝕜 := ℂ) (finiteResolvent F (star (line μ w)) (k : H))
      (B (finiteResolvent F (line μ w) (g : H)))
    rw [actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne')] at hn
    exact hn.trans (young _ _ δ hδ))
  have he := integral_add (hk.const_mul δ) (hb.const_mul ((4*δ)⁻¹))
  simp only [Pi.add_apply] at hi he
  rw [he,integral_const_mul,integral_const_mul,energy_mass F μ hμ] at hi
  exact hi

/-- The original forcing-energy tail pays the complete complex amplitude on the same F. -/
theorem actual_common_frequency_tail (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫ w : ℝ,‖amplitude F μ (A*relativeTail m ell) (g : H) (k : H) w‖)<ε := by
  intro ε hε
  let K := Real.pi/μ*‖(k : H)‖^2
  have hK : 0≤K := by dsimp [K];positivity
  let δ := ε/(4*(K+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have he : δ*(4*(K+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hd : δ*K<ε/4 := by nlinarith
  obtain ⟨N,hN⟩ := bounded_forcing_full_frequency_tail μ hμ A g (δ*ε) (mul_pos hδ hε)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have hi := inserted_energy_int F μ hμ (A*relativeTail m ell) (g : H)
  have hr : (∫ w : ℝ,‖(A*relativeTail m ell) (finiteResolvent F (line μ w) (g : H))‖^2)≤δ*ε := by
    have ht : (∫⁻ w : ℝ,ENNReal.ofReal (‖(A*relativeTail m ell) (finiteResolvent F (line μ w) (g : H))‖^2))≤ENNReal.ofReal (δ*ε) := hF
    rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))] at ht
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ht
  have hb := amplitude_energy_bound F μ hμ (A*relativeTail m ell) g k δ hδ
  have hh : (4*δ)⁻¹*(δ*ε)=ε/4 := by field_simp
  have hh' := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr (by positivity : 0≤4*δ))
  rw [hh] at hh'
  change _≤δ*K+_ at hb
  linarith

private theorem time_norm (f : ℝ → ℂ) (t : ℝ) :
    ‖timeTransform f t‖≤(2*Real.pi)⁻¹*(∫ w : ℝ,‖f w‖) := by
  rw [timeTransform,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2*Real.pi)⁻¹)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq ?_) (by positivity)
  simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]

/-- One cutoff and one eventual-F event control the complete time axis. -/
theorem actual_common_time_tail (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ t : ℝ,
        ‖response F μ (A*relativeTail m ell) (g : H) (k : H) t‖<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_common_frequency_tail μ hμ A g k (2*Real.pi*ε) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro t
  apply (time_norm (amplitude F μ (A*relativeTail m ell) (g : H) (k : H)) t).trans_lt
  have h := mul_lt_mul_of_pos_left hF (by positivity : 0<(2*Real.pi)⁻¹)
  simpa only [←mul_assoc,inv_mul_cancel₀ (by positivity : (2*Real.pi)≠0),one_mul] using h

/-- The same uniform tail descends to the existing history response. -/
theorem actual_whole_time_tail (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ t : ℝ,
      ‖wholeResponse μ hμ (A*relativeTail m ell) (g : H) (k : H) t‖<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_common_time_tail μ hμ A g k (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hell t => ?_⟩
  obtain ⟨F,hF,hlim⟩ := ((hN m hm ell hell).and
    (actual_uniform_time_response μ hμ (A*relativeTail m ell) g k (ε/2) (by positivity))).exists
  calc
    _ = ‖response F μ (A*relativeTail m ell) (g : H) (k : H) t-
        (response F μ (A*relativeTail m ell) (g : H) (k : H) t-
          wholeResponse μ hμ (A*relativeTail m ell) (g : H) (k : H) t)‖ := by congr 1;abel
    _ ≤ ‖response F μ (A*relativeTail m ell) (g : H) (k : H) t‖+
        ‖response F μ (A*relativeTail m ell) (g : H) (k : H) t-
          wholeResponse μ hμ (A*relativeTail m ell) (g : H) (k : H) t‖ := norm_sub_le _ _
    _ < ε/2+ε/2 := add_lt_add (hF t) (hlim t)
    _ = ε := by ring

end LowEnergy.SourceBoundedInsertionTail
