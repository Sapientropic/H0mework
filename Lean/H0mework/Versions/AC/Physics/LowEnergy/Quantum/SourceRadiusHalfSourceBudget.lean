import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRadiusHalfSeedTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfSourceBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceRadiusHalfWindow SourceRadiusHalfResponse SourceRadiusHalfSeedTail SourceRadiusBandGradient
open SourceRadiusPairedScalarPrice SourceResolventBandLimit FullYSourceResolventGraphSplice
open scoped InnerProductSpace

def causalSign (advanced : Bool) : ℝ := if advanced then -1 else 1
def causalPoint (advanced : Bool) (μ w : ℝ) : ℂ := if advanced then star (line μ w) else line μ w
private theorem causal_im (advanced : Bool) (μ w : ℝ) : (causalPoint advanced μ w).im=causalSign advanced*μ := by
  cases advanced <;> simp [causalPoint,causalSign,line_im]

theorem causal_nonreal (advanced : Bool) (μ w : ℝ) (hμ : 0<μ) : (causalPoint advanced μ w).im≠0 := by
  cases advanced <;> simpa only [causalPoint,Bool.false_eq_true,if_false,if_true,Complex.star_def,
    Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'

private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_embed]
  exact (GaussGradedCompression.compression_pair F _ _).symm

private theorem nonreal_balance (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    let f := state F z hz g
    z.im*‖embed (halfAction m ell f)‖^2=
      -(sourcePair (halfAction m ell f) (halfAction m ell (coreEquiv.symm g))).im-
      (sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im := by
  let f := state F z hz g
  have hc : compressionCore F f=coreEquiv.symm g+z • f := by
    have h := actual_raised_source F z hz g 1
    simp only [Module.End.one_apply,raisedDefect,mul_one,one_mul,sub_self,LinearMap.zero_apply,zero_add,
      defectAction,LinearMap.sub_apply] at h
    change diagonalAction f=coreEquiv.symm g+z • f+(diagonalAction f-compressionCore F f) at h
    linear_combination (norm := module) h
  have hroute : compressionCore F (halfAction m ell f)=
      halfAction m ell (coreEquiv.symm g)+z • halfAction m ell f+correctedCurrent F m ell f := by
    have h := LinearMap.congr_fun (original_corrected_current F m ell) f
    simp only [LinearMap.sub_apply,Module.End.mul_apply,hc,map_add,map_smul] at h
    linear_combination (norm := module) -h
  have hreal : (sourcePair (halfAction m ell f) (compressionCore F (halfAction m ell f))).im=0 := by
    have h := congrArg Complex.im (pair_conjugate (halfAction m ell f) (compressionCore F (halfAction m ell f)))
    rw [←compression_pair] at h
    simp only [Complex.conj_im] at h
    linarith
  have hnorm : inner ℂ (embed (halfAction m ell f)) (embed (halfAction m ell f))=
      ((‖embed (halfAction m ell f)‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed (halfAction m ell f))
  have h := congrArg (fun q => (sourcePair (halfAction m ell f) q).im) hroute
  rw [hreal] at h
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right] at h
  rw [hnorm] at h
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add] at h
  change z.im*‖embed (halfAction m ell f)‖^2=
    -(inner ℂ (embed (halfAction m ell f)) (embed (halfAction m ell (coreEquiv.symm g)))).im-
    (inner ℂ (embed (halfAction m ell f)) (embed (correctedCurrent F m ell f))).im
  linarith only [h]

/-- Both causal orientations retain their actual source current and the correct imaginary sign. -/
theorem actual_causal_localized_balance (advanced : Bool) (F : Index) (m ell : ℕ) (μ w : ℝ)
    (hμ : 0<μ) (g : diagonal.domain) :
    let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
    μ*‖embed (halfAction m ell f)‖^2=
      -causalSign advanced*(sourcePair (halfAction m ell f) (halfAction m ell (coreEquiv.symm g))).im-
      causalSign advanced*(sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im := by
  dsimp only
  let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
  have h := nonreal_balance F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
  change (causalPoint advanced μ w).im*‖embed (halfAction m ell f)‖^2=_ at h
  rw [causal_im] at h
  have hs : causalSign advanced*causalSign advanced=1 := by cases advanced <;> norm_num [causalSign]
  calc
    _=(causalSign advanced*causalSign advanced)*(μ*‖embed (halfAction m ell f)‖^2) := by rw [hs,one_mul]
    _=causalSign advanced*((causalSign advanced*μ)*‖embed (halfAction m ell f)‖^2) := by ring
    _=_ := by rw [h];ring

private theorem absorb (μ a b c ε : ℝ) (hμ : 0<μ)
    (hbalance : μ*a^2 ≤ a*b-c) (hseed : b^2 ≤ μ^2*ε) :
    a^2 ≤ ε-(2/μ)*c := by
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hμ)).mp
  have h := mul_le_mul_of_nonneg_left hbalance (by positivity : 0 ≤ 2*μ)
  have he : μ^2*(ε-(2/μ)*c)=μ^2*ε-2*μ*c := by field_simp
  rw [mul_comm (a^2),mul_comm (ε-(2/μ)*c),he]
  nlinarith only [h,hseed,sq_nonneg (μ*a-b)]

/-- The original compact source pays the fixed endpoint uniformly in all F, frequencies, upper windows and both causal legs. -/
theorem actual_half_source_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell : ℕ,∀ F : Index,∀ w : ℝ,∀ advanced : Bool,
      let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
      ‖embed (halfAction m ell f)‖^2 ≤ ε-(2/μ)*causalSign advanced*
        (sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im := by
  intro ε hε
  obtain ⟨N,hN⟩ := original_half_seed_tail (coreEquiv.symm g) (μ^2*ε) (by positivity)
  refine ⟨N,fun m hm ell F w advanced => ?_⟩
  let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
  have hb := actual_causal_localized_balance advanced F m ell μ w hμ g
  change μ*‖embed (halfAction m ell f)‖^2=_ at hb
  have hp : |(sourcePair (halfAction m ell f) (halfAction m ell (coreEquiv.symm g))).im| ≤
      ‖embed (halfAction m ell f)‖*‖embed (halfAction m ell (coreEquiv.symm g))‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hsign : -causalSign advanced*(sourcePair (halfAction m ell f) (halfAction m ell (coreEquiv.symm g))).im ≤
      ‖embed (halfAction m ell f)‖*‖embed (halfAction m ell (coreEquiv.symm g))‖ := by
    cases advanced <;> norm_num only [causalSign,Bool.false_eq_true,if_false,if_true,neg_neg,one_mul,neg_mul] at *
    · exact (neg_le_abs _).trans hp
    · exact (le_abs_self _).trans hp
  have h := absorb μ ‖embed (halfAction m ell f)‖ ‖embed (halfAction m ell (coreEquiv.symm g))‖
    (causalSign advanced*(sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im) ε hμ
    (by rw [hb];exact sub_le_sub_right hsign _) (hN m hm ell)
  simpa only [mul_assoc] using h

/-- The same half-window measures the original first-radius energy, rather than a substitute observable. -/
theorem original_radius_half_identity (m ell : ℕ) (f : QuantumTest) :
    radiusMoment m ell (embed f)=‖embed (halfAction m ell f)‖^2+
      2*(sourcePair f (halfAction m ell f)).re := by
  unfold radiusMoment
  rw [←original_band_core,←original_half_square]
  change (sourcePair f (halfAction m ell (halfAction m ell f)+(2 : ℂ) • halfAction m ell f)).re=_
  have hp : sourcePair f (halfAction m ell (halfAction m ell f))=
      sourcePair (halfAction m ell f) (halfAction m ell f) := multiply_pair _ _ _ _
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_re]
  change (sourcePair f (halfAction m ell (halfAction m ell f))).re+
    ((2 : ℂ)*sourcePair f (halfAction m ell f)).re=_
  rw [hp]
  have hn : (sourcePair (halfAction m ell f) (halfAction m ell f)).re=‖embed (halfAction m ell f)‖^2 := by
    change RCLike.re (inner ℂ (embed (halfAction m ell f)) (embed (halfAction m ell f)))=_
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hn]
  norm_num [Complex.mul_re]
  rfl

/-- The original first-radius moment consumes the paid source term and the full signed compression current. -/
theorem actual_radius_source_budget (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell : ℕ,∀ F : Index,∀ w : ℝ,∀ advanced : Bool,
      let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
      let B := ε-(2/μ)*causalSign advanced*(sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im
      0 ≤ B ∧ radiusMoment m ell (embed f) ≤ B+2*(μ⁻¹*‖(g : H)‖)*Real.sqrt B := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_half_source_budget μ hμ g ε hε
  refine ⟨N,fun m hm ell F w advanced => ?_⟩
  let f := state F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g
  let B := ε-(2/μ)*causalSign advanced*(sourcePair (halfAction m ell f) (correctedCurrent F m ell f)).im
  have hb : ‖embed (halfAction m ell f)‖^2 ≤ B := hN m hm ell F w advanced
  have hB : 0 ≤ B := (sq_nonneg _).trans hb
  have hl : ‖embed (halfAction m ell f)‖ ≤ Real.sqrt B :=
    (Real.le_sqrt (norm_nonneg _) hB).mpr hb
  have hzi : |(causalPoint advanced μ w).im|=μ := by
    cases advanced <;> simp [causalPoint,line_im,abs_of_pos hμ]
  have he : embed f=finiteResolvent F (causalPoint advanced μ w) (g : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hr : ‖embed f‖ ≤ μ⁻¹*‖(g : H)‖ := by
    rw [he]
    exact ((finiteResolvent F (causalPoint advanced μ w)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (by simpa only [hzi,one_div] using
        (finite_resolvent_norm F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ))) (norm_nonneg _))
  have hp : (sourcePair f (halfAction m ell f)).re ≤ ‖embed f‖*‖embed (halfAction m ell f)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hmul := mul_le_mul hr hl (norm_nonneg _) (by positivity : 0 ≤ μ⁻¹*‖(g : H)‖)
  refine ⟨hB,?_⟩
  change radiusMoment m ell (embed f) ≤ B+2*(μ⁻¹*‖(g : H)‖)*Real.sqrt B
  rw [original_radius_half_identity]
  nlinarith only [hb,hp,hmul]

end LowEnergy.SourceRadiusHalfSourceBudget
