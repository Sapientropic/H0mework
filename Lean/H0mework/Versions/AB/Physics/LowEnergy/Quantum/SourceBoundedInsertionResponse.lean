import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianSpectralPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceBoundedInsertionResponse
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceHamiltonianSpectralEnergy SourceHamiltonianSpectralFrequency SourceResolventLorentzian SourceResolventBandLimit
open SourceActualResolventEnergy FullYSourceResolventGraphSplice SourceInverseSourceLeg MeasureTheory Filter
open SourceFamilyHilbert SourceFamilyOperator
open scoped Topology InnerProductSpace

private theorem limit_lipschitz {ι E : Type*} [PseudoMetricSpace E] (l : Filter ι) [NeBot l]
    (f : ι → ℝ → E) (p : ℝ → E) (L : NNReal) (hf : ∀ i,LipschitzWith L (f i))
    (hp : ∀ w,Tendsto (fun i => f i w) l (𝓝 (p w))) : LipschitzWith L p := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact le_of_tendsto ((hp x).dist (hp y)) (Eventually.of_forall (fun i => (hf i).dist_le_mul x y))

/-- Equal-mass positive source envelopes control complex phases on arbitrary filters. -/
private theorem complex_frequency_L1 {ι : Type*} (l : Filter ι) [NeBot l]
    (f : ι → ℝ → ℂ) (a : ℝ → ℂ) (d : ι → ℝ → ℝ) (D : ℝ → ℝ) (L K : NNReal)
    (hf : ∀ i,LipschitzWith L (f i)) (hd : ∀ i,LipschitzWith K (d i))
    (ha : ∀ w,Tendsto (fun i => f i w) l (𝓝 (a w)))
    (hD : ∀ w,Tendsto (fun i => d i w) l (𝓝 (D w)))
    (hdi : ∀ i,Integrable (d i)) (hDi : Integrable D)
    (hdom : ∀ i w,‖f i w‖ ≤ d i w) (hm : ∀ i,(∫ w,d i w)=∫ w,D w) :
    (∀ i,Integrable (f i)) ∧ Integrable a ∧
      Tendsto (fun i => ∫ w : ℝ,‖f i w-a w‖) l (𝓝 0) := by
  have hal := limit_lipschitz l f a L hf ha
  have hDl := limit_lipschitz l d D K hd hD
  have had (w : ℝ) : ‖a w‖ ≤ D w :=
    le_of_tendsto_of_tendsto (ha w).norm (hD w) (Eventually.of_forall (fun i => hdom i w))
  have hai : Integrable a := hDi.mono' hal.continuous.aestronglyMeasurable (Eventually.of_forall had)
  have hfi (i : ι) : Integrable (f i) :=
    (hdi i).mono' (hf i).continuous.aestronglyMeasurable (Eventually.of_forall (hdom i))
  refine ⟨hfi,hai,?_⟩
  let s := fun i w => d i w+D w-‖f i w-a w‖
  have hsl (i : ι) : LipschitzWith (K+K+(L+L)) (s i) := by
    have hn : LipschitzWith (L+L) (fun w => ‖f i w-a w‖) := by
      simpa only [one_mul,Function.comp_apply] using! lipschitzWith_one_norm.comp ((hf i).sub hal)
    exact ((hd i).add hDl).sub hn
  have hsi (i : ι) : Integrable (s i) := ((hdi i).add hDi).sub ((hfi i).sub hai).norm
  have hsn (i : ι) (w : ℝ) : 0 ≤ s i w := by
    have h := (norm_sub_le (f i w) (a w)).trans (add_le_add (hdom i w) (had w))
    exact sub_nonneg.mpr h
  have hsp (w : ℝ) : Tendsto (fun i => s i w) l (𝓝 (2*D w)) := by
    have h := ((hD w).add (tendsto_const_nhds (x := D w))).sub ((ha w).sub (tendsto_const_nhds (x := a w))).norm
    simpa only [sub_self,norm_zero,sub_zero,two_mul] using h
  have hband : Tendsto (fun R : ℝ => ∫ w in -R..R,2*D w) atTop (𝓝 (2*∫ w,D w)) := by
    simpa only [integral_const_mul,id_eq] using!
      intervalIntegral_tendsto_integral (hDi.const_mul 2) tendsto_neg_atTop_atBot tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR,hmass⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((tendsto_order.mp hband).1 (2*(∫ w,D w)-ε/2) (by linarith))).exists
  have hlim := band_integral_limit l s (fun w => 2*D w) (K+K+(L+L)) hsl hsp (-R) R
  filter_upwards [(tendsto_order.mp hlim).1 ((∫ w in -R..R,2*D w)-ε/2) (by linarith)] with i hi
  have hle : (∫ w in -R..R,s i w) ≤ ∫ w,s i w := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (hsn i)) (hsi i)
  have he : (∫ w,s i w)=2*(∫ w,D w)-(∫ w,‖f i w-a w‖) := by
    have hh := integral_sub ((hdi i).add hDi) ((hfi i).sub hai).norm
    simp only [Pi.add_apply,Pi.sub_apply] at hh
    rw [show (∫ w,s i w)=(∫ w,d i w+D w-‖f i w-a w‖) from rfl,hh,integral_add (hdi i) hDi,hm]
    ring
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  linarith

/-- Literal finite-source retarded word, with its original complex phase. -/
def amplitude (F : Index) (μ : ℝ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) : ℂ :=
  inner ℂ k (finiteResolvent F (line μ w) (A (finiteResolvent F (line μ w) g)))

/-- The same word is evaluated on the existing source history, without a new occurrence. -/
def wholeAmplitude (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) : ℂ :=
  inner ℂ (inclusion k) (sameResolvent (line μ w) (by simpa only [line_im] using hμ.ne')
    (reader A (sameResolvent (line μ w) (by simpa only [line_im] using hμ.ne') (inclusion g))))

private theorem pointwise (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) :
    Tendsto (fun F => amplitude F μ A g k w) (sourceFilter : Filter Index) (𝓝 (wholeAmplitude μ hμ A g k w)) := by
  let R := resolventFamily (line μ w) (by simpa only [line_im] using hμ.ne')
  have h := pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter k)
    (act sourceFilter R (act sourceFilter (SourceFamilyOperator.constant A)
      (act sourceFilter R (SourceFamilyHilbert.constant sourceFilter g))))
  change Tendsto (fun F => amplitude F μ A g k w) _ _ at h
  unfold wholeAmplitude sameResolvent reader
  change Tendsto _ _ (𝓝 (inner ℂ ((SourceFamilyHilbert.constant sourceFilter k) : HistorySpace)
    (lift sourceFilter R (lift sourceFilter (SourceFamilyOperator.constant A)
      (lift sourceFilter R ((SourceFamilyHilbert.constant sourceFilter g) : HistorySpace))))))
  rw [lift_coe,lift_coe,lift_coe,inner_coe]
  exact h

private theorem amplitude_lipschitz (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) :
    LipschitzWith ⟨‖k‖*variation μ [A]*‖g‖,by have := variation_nonneg μ hμ [A];positivity⟩
      (amplitude F μ A g k) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  have hw (w : ℝ) : amplitude F μ A g k w=inner ℂ k (word (GaussGradedCompression.compression F) μ w [A] g) := rfl
  rw [dist_eq_norm,hw,hw]
  rw [←inner_sub_right]
  have hd := word_difference (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) μ hμ [A] t s
  have he := ((word (GaussGradedCompression.compression F) μ t [A]-
    word (GaussGradedCompression.compression F) μ s [A]).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg g))
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left he (norm_nonneg k)).trans_eq (by
    change ‖k‖ * (variation μ [A] * |t-s| * ‖g‖) = (‖k‖ * variation μ [A] * ‖g‖) * dist t s
    rw [Real.dist_eq]
    ring))

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf


private theorem finite_pair (F : Index) (z : ℂ) (hz : z.im≠0) (k f : H) :
    inner ℂ k (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k) f :=
  resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz k f

/-- The literal retarded word equals the actual advanced-left/retarded-right source pair. -/
theorem actual_causal_pair (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) :
    amplitude F μ A g k w=inner ℂ (finiteResolvent F (star (line μ w)) k)
      (A (finiteResolvent F (line μ w) g)) :=
  finite_pair F (line μ w) (by simpa only [line_im] using hμ.ne') k _

def envelope (F : Index) (μ : ℝ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) : ℝ :=
  (‖A‖/2)*(‖finiteResolvent F (line μ w) g‖^2+‖finiteResolvent F (line μ w) k‖^2)

private theorem amplitude_bound (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) (w : ℝ) :
    ‖amplitude F μ A g k w‖ ≤ envelope F μ A g k w := by
  rw [actual_causal_pair F μ hμ]
  have hp := (norm_inner_le_norm (𝕜 := ℂ) (finiteResolvent F (star (line μ w)) k)
    (A (finiteResolvent F (line μ w) g))).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm (finiteResolvent F (line μ w) g)) (norm_nonneg _))
  rw [actual_conjugate_leg_norm F (line μ w) (by simpa only [line_im] using hμ.ne')] at hp
  unfold envelope
  have hy := mul_nonneg (norm_nonneg A)
    (sq_nonneg (‖finiteResolvent F (line μ w) g‖-‖finiteResolvent F (line μ w) k‖))
  nlinarith

private theorem energy_int (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    Integrable (fun w => ‖finiteResolvent F (line μ w) x‖^2) := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integrable F μ hμ x
private theorem energy_mass (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫ w : ℝ,‖finiteResolvent F (line μ w) x‖^2)=Real.pi/μ*‖x‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I] using! actual_square_integral F μ hμ x

/-- Bounded source insertions retain their complex phase in the original full-frequency limit. -/
theorem actual_full_frequency_response (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : diagonal.domain) :
    (∀ F : Index,Integrable (amplitude F μ A (g : H) (k : H))) ∧
      Integrable (wholeAmplitude μ hμ A (g : H) (k : H)) ∧
      Tendsto (fun F => ∫ w : ℝ,‖amplitude F μ A (g : H) (k : H) w-wholeAmplitude μ hμ A (g : H) (k : H) w‖)
        (sourceFilter : Filter Index) (𝓝 0) := by
  obtain ⟨ν,hνfin,hνmass,hν⟩ := actual_source_energy_measure g
  obtain ⟨κ,hκfin,hκmass,hκ⟩ := actual_source_energy_measure k
  let := hνfin
  let := hκfin
  obtain ⟨hνi,hνm⟩ := spectral_frequency_mass ν μ hμ
  obtain ⟨hκi,hκm⟩ := spectral_frequency_mass κ μ hμ
  have hn : ν.real Set.univ=‖(g : H)‖^2 := by rw [Measure.real,hνmass,ENNReal.toReal_ofReal (sq_nonneg _)]
  have hk : κ.real Set.univ=‖(k : H)‖^2 := by rw [Measure.real,hκmass,ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hn] at hνm
  rw [hk] at hκm
  let c : ℝ := ‖A‖/2
  let D := fun w => c*(profile ν μ w+profile κ μ w)
  let K : H → NNReal := fun x => ⟨2*μ⁻¹*(μ⁻¹*μ⁻¹)*‖x‖^2,by positivity⟩
  let L : NNReal := ⟨‖(k : H)‖*variation μ [A]*‖(g : H)‖,by have := variation_nonneg μ hμ [A];positivity⟩
  have hl (F : Index) (x : H) : LipschitzWith (K x) (fun w => ‖finiteResolvent F (line μ w) x‖^2) :=
    word_square_lipschitz (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) μ hμ [] x
  have hdl (F : Index) : LipschitzWith (‖c‖₊*(K (g : H)+K (k : H))) (envelope F μ A (g : H) (k : H)) := by
    simpa only [Function.comp_apply,smul_eq_mul] using! (lipschitzWith_smul c).comp ((hl F (g : H)).add (hl F (k : H)))
  have hdp (w : ℝ) : Tendsto (fun F => envelope F μ A (g : H) (k : H) w) (sourceFilter : Filter Index) (𝓝 (D w)) := by
    have he (a : ℝ) : ‖((a : ℂ)-line μ w)⁻¹‖^2=kernel μ a w := by
      simpa only [line,mul_comm (μ : ℂ) Complex.I] using inverse_norm_square μ a w
    have h := (((hν (line μ w) (by simpa only [line_im] using hμ.ne')).2).add
      ((hκ (line μ w) (by simpa only [line_im] using hμ.ne')).2)).const_mul c
    simpa only [envelope,D,profile,c,he] using! h
  have hdi (F : Index) : Integrable (envelope F μ A (g : H) (k : H)) :=
    ((energy_int F μ hμ (g : H)).add (energy_int F μ hμ (k : H))).const_mul c
  have hDi : Integrable D := (hνi.add hκi).const_mul c
  have hdm (F : Index) : (∫ w,envelope F μ A (g : H) (k : H) w)=∫ w,D w := by
    simp only [envelope,D,integral_const_mul,
      integral_add (energy_int F μ hμ (g : H)) (energy_int F μ hμ (k : H)),
      integral_add hνi hκi,energy_mass F μ hμ,hνm,hκm,c]
  exact complex_frequency_L1 (sourceFilter : Filter Index)
    (fun F => amplitude F μ A (g : H) (k : H)) (wholeAmplitude μ hμ A (g : H) (k : H))
    (fun F => envelope F μ A (g : H) (k : H)) D L (‖c‖₊*(K (g : H)+K (k : H)))
    (fun F => amplitude_lipschitz F μ hμ A (g : H) (k : H)) hdl
    (pointwise μ hμ A (g : H) (k : H)) hdp hdi hDi
    (fun F w => amplitude_bound F μ hμ A (g : H) (k : H) w) hdm

end LowEnergy.SourceBoundedInsertionResponse
