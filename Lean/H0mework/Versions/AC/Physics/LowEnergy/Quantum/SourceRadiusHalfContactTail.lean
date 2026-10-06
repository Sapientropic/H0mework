import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRadiusHalfWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfContactTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm
open GaussLiveMomentum GaussNativeEnergy SourceQuantumScalarChart
open SourceRadiusHalfWindow SourceScalarPositiveBulkWard SourceResolventBandLimit
open SourceActualResolventEnergy SourceInverseSourceLeg FullYSourceResolventGraphSplice
open MeasureTheory

/-- The complete native70 error on the actual retarded or advanced source leg. -/
def frequencyError (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) : ℝ :=
  let z := if advanced then star (line μ w) else line μ w
  let hz : z.im≠0 := by
    cases advanced <;> simpa only [z,Bool.false_eq_true,if_false,if_true,Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  let f := state F z hz g
  ∑ i : ScalarIndex,‖embed (covariantMomentum (scalarDirection i) (halfAction m ell f)-
    halfAction m ell (covariantMomentum (scalarDirection i) f))‖^2

/-- Every F and every upper cutoff have the same fixed-source full-frequency price. -/
theorem actual_half_contact_full_frequency (advanced : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (frequencyError advanced m ell F μ hμ g w)) ≤
      ENNReal.ofReal ((3/(4*(m+1 : ℝ)))*(Real.pi/μ*‖(g : H)‖^2)) := by
  have hc : 0≤3/(4*(m+1 : ℝ)) := by positivity
  have hb (w : ℝ) : frequencyError advanced m ell F μ hμ g w ≤
      (3/(4*(m+1 : ℝ)))*‖finiteResolvent F (line μ w) (g : H)‖^2 := by
    unfold frequencyError
    dsimp only
    have he (z : ℂ) (hz : z.im≠0) : embed (state F z hz g)=finiteResolvent F z (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    cases advanced
    · have h := original_half_transport_error m ell (state F (line μ w) (by simpa only [line_im] using hμ.ne') g)
      rw [he] at h
      exact h
    · have h := original_half_transport_error m ell (state F (star (line μ w))
        (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne') g)
      rw [he,actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne')] at h
      exact h
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (3/(4*(m+1 : ℝ)))*
        ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (hb w)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have he := actual_square_lintegral F μ hμ (g : H)
      have hr : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))=
          ENNReal.ofReal (Real.pi/μ*‖(g : H)‖^2) := by simpa only [line,mul_comm] using he
      rw [hr,←ENNReal.ofReal_mul hc]

/-- The source-generated contact error tends to zero uniformly over all original F and both causal legs. -/
theorem actual_half_contact_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell : ℕ, ∀ F : Index, ∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (frequencyError advanced m ell F μ hμ g w)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := (3/4 : ℝ)*(Real.pi/μ*‖(g : H)‖^2)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell F advanced => ?_⟩
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hC : C<(N : ℝ)*ε := (div_lt_iff₀ hε).mp hN
  have hprice : (3/(4*(m+1 : ℝ)))*(Real.pi/μ*‖(g : H)‖^2) ≤ ε := by
    have hce : C≤ε*(m+1 : ℝ) := by nlinarith
    have hd : C/(m+1 : ℝ)≤ε := (div_le_iff₀ (by positivity)).mpr hce
    exact (show (3/(4*(m+1 : ℝ)))*(Real.pi/μ*‖(g : H)‖^2)=C/(m+1 : ℝ) by dsimp only [C];field_simp).trans_le hd
  exact (actual_half_contact_full_frequency advanced m ell F μ hμ g).trans (ENNReal.ofReal_le_ofReal hprice)

end LowEnergy.SourceRadiusHalfContactTail
