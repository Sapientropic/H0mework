import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeChannelSourceJets
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceHamiltonianSpectralMeasure
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement
open SourceInverseNoetherChannelGap SourceInverseChannelSourceJets SourceInverseElectricMomentChannels
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace Topology

attribute [local irreducible] sourceBasis channel channelValue

/-- Every actual channel contributes its source mass, including the complete escape channel. -/
def sourceMeasure (F : Index) (g : H) : Measure ℝ :=
  ∑ i : Channel F,ENNReal.ofReal (‖channel F i g‖^2) • Measure.dirac (channelValue F i)

private theorem channel_resolution (F : Index) (g : H) : ∑ i : Channel F,channel F i g=g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F g+(∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=g
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i : H))=((supportSpan F).orthogonalProjectionOnto g : H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

private theorem unit_projection_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v g : E) (hv : ‖v‖=1) :
    inner ℂ g ((inner ℂ v g) • v)=((‖(inner ℂ v g) • v‖^2 : ℝ) : ℂ) := by
  rw [inner_smul_right,norm_smul,hv,mul_one]
  rw [←inner_conj_symm g v]
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' (inner ℂ v g)

private theorem channel_pair (F : Index) (g : H) (i : Channel F) :
    inner ℂ g (channel F i g)=((‖channel F i g‖^2 : ℝ) : ℂ) := by
  cases i with
  | none =>
    have he : inner ℂ (escapeProjection F g) (supportProjection F g)=0 :=
      (supportSpan F).starProjection_inner_eq_zero g _ (Submodule.starProjection_apply_mem _ g)
    have hr : g=escapeProjection F g+supportProjection F g := by
      change g=(g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g
      abel
    simp only [channel]
    change inner ℂ g (escapeProjection F g)=_
    calc
      _ = inner ℂ (escapeProjection F g+supportProjection F g) (escapeProjection F g) :=
        congrArg (fun x : H => inner ℂ x (escapeProjection F g)) hr
      _ = _ := by
        rw [inner_add_left,inner_eq_zero_symm.mp he,add_zero]
        simpa only [Complex.ofReal_pow] using! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (escapeProjection F g)
  | some i =>
    have hs : channel F (some i) g=inner ℂ ((sourceBasis F) i : H) g • ((sourceBasis F) i : H) := by
      rw [channel,OrthonormalBasis.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    have hn : ‖((sourceBasis F) i : H)‖=1 := by
      change ‖(sourceBasis F) i‖=1
      exact (sourceBasis F).orthonormal.norm_eq_one i
    rw [hs]
    exact unit_projection_pair _ _ hn

/-- The full finite source spectrum has exactly the original input norm as its mass. -/
theorem actual_channel_mass (F : Index) (g : H) : ∑ i : Channel F,‖channel F i g‖^2=‖g‖^2 := by
  have h := congrArg (fun x : H => (inner ℂ g x).re) (channel_resolution F g)
  simp only [inner_sum,Complex.re_sum,channel_pair,Complex.ofReal_re] at h
  have hi : (inner ℂ g g).re=‖g‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) g).symm
  exact h.trans hi

theorem actual_measure_mass (F : Index) (g : H) :
    sourceMeasure F g Set.univ=ENNReal.ofReal (‖g‖^2) := by
  simp only [sourceMeasure,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),actual_channel_mass]

instance (F : Index) (g : H) : IsFiniteMeasure (sourceMeasure F g) :=
  ⟨by rw [actual_measure_mass];exact ENNReal.ofReal_lt_top⟩

private theorem measure_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : Index) (g : H) (f : ℝ → G) :
    (∫ x,f x ∂sourceMeasure F g)=∑ i : Channel F,(‖channel F i g‖^2) • f (channelValue F i) := by
  unfold sourceMeasure
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The same positive measure reads the actual resolvent on both nonreal half-planes. -/
theorem actual_stieltjes (F : Index) (g : H) (z : ℂ) (hz : z.im≠0) :
    (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂sourceMeasure F g)=inner ℂ g (finiteResolvent F z g) := by
  rw [measure_integral,actual_channels F z hz,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right,channel_pair]
  simp only [Complex.real_smul,Complex.ofReal_pow]
  ring

/-- Every fixed even moment is generated by the original Hamiltonian source jet on one cofinal event. -/
theorem actual_even_moment (n : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫ a : ℝ,a^(2*n) ∂sourceMeasure F (g : H))=‖(iterate n g : H)‖^2 := by
  filter_upwards [actual_channel_source_jet n g] with F hF
  have he (h : diagonal.domain) (i : Channel F) :
      embed (channelTest F h i)=channel F i (h : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hc (i : Channel F) : channel F i (iterate n g : H)=(channelValue F i : ℂ)^n • channel F i (g : H) := by
    have h := congrArg embed (hF i)
    simpa only [map_smul,he] using h
  rw [measure_integral,←actual_channel_mass F (iterate n g : H)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow]
  simp only [smul_eq_mul]
  rw [←pow_mul,show n*2=2*n by omega,pow_mul,pow_mul,sq_abs]
  ring

private theorem measure_integrable (F : Index) (g : H) (f : ℝ → ℝ) :
    Integrable f (sourceMeasure F g) := by
  unfold sourceMeasure
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A single original first-jet event controls every spectral radius. -/
theorem actual_spectral_tail (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (R : ℝ),0<R →
      (sourceMeasure F (g : H)).real {a : ℝ | R ≤ |a|} ≤ ‖(iterate 1 g : H)‖^2/R^2 := by
  filter_upwards [actual_even_moment 1 g] with F hF R hR
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := sourceMeasure F (g : H)) (f := fun a : ℝ => a^2)
    (Eventually.of_forall (fun a => sq_nonneg a)) (measure_integrable F (g : H) _) (R^2)
  have hs : {a : ℝ | R^2 ≤ a^2}={a : ℝ | R ≤ |a|} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro ha
    · nlinarith [sq_abs a,abs_nonneg a]
    · nlinarith [sq_abs a,abs_nonneg a]
  norm_num only [Nat.reduceMul] at hF
  rw [hs,hF] at hm
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [mul_comm] using hm

/-- Normalization is the original source mass, with no external residue factor. -/
def sourceProbability (F : Index) (g : H) (hg : g≠0) : ProbabilityMeasure ℝ :=
  ⟨(ENNReal.ofReal (‖g‖^2))⁻¹ • sourceMeasure F g,⟨by
    rw [Measure.smul_apply,actual_measure_mass,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [hg])
      ENNReal.ofReal_ne_top⟩⟩

private theorem probability_tail (F : Index) (g : diagonal.domain) (hg : (g : H)≠0)
    (hF : ∀ (R : ℝ),0<R → (sourceMeasure F (g : H)).real {a : ℝ | R ≤ |a|} ≤
      ‖(iterate 1 g : H)‖^2/R^2) (R : ℝ) (hR : 0<R) :
    (sourceProbability F (g : H) hg : Measure ℝ).real {a : ℝ | R ≤ |a|} ≤
      (‖(iterate 1 g : H)‖^2/‖(g : H)‖^2)/R^2 := by
  change ((ENNReal.ofReal (‖(g : H)‖^2))⁻¹ • sourceMeasure F (g : H)).real _ ≤ _
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (hF R hR) (inv_nonneg.mpr (sq_nonneg ‖(g : H)‖))
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h

/-- The original ultrafilter itself generates a positive weak spectral limit for every nonzero source. -/
theorem actual_probability_limit (g : diagonal.domain) (hg : (g : H)≠0) :
    ∃ ν : ProbabilityMeasure ℝ,
      Tendsto (fun F => sourceProbability F (g : H) hg) (sourceFilter : Filter Index) (𝓝 ν) := by
  let P := fun F => sourceProbability F (g : H) hg
  let good : Set Index := {F | ∀ (R : ℝ),0<R →
    (sourceMeasure F (g : H)).real {a : ℝ | R ≤ |a|} ≤ ‖(iterate 1 g : H)‖^2/R^2}
  have hgood : good∈sourceFilter := actual_spectral_tail g
  let S : Set (ProbabilityMeasure ℝ) := P '' good
  have ht : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ∈S} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨δ,_,hd,hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    have hδ : 0<δ := ENNReal.ofReal_pos.mp hd
    let M : ℝ := ‖(iterate 1 g : H)‖^2/‖(g : H)‖^2
    have hM : 0 ≤ M := by dsimp [M];positivity
    let R := M/δ+1
    have hR : 0<R := by dsimp [R];positivity
    have hMR : M/R^2 ≤ δ := by
      apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
      have hm : M/δ*δ=M := div_mul_cancel₀ _ hδ.ne'
      have hq : 0 ≤ M/δ := div_nonneg hM hδ.le
      have hrr : R ≤ R^2 := by dsimp [R];nlinarith [sq_nonneg (M/δ)]
      have hrm : M ≤ δ*R := by dsimp [R];nlinarith only [hm,hδ]
      exact hrm.trans (mul_le_mul_of_nonneg_left hrr hδ.le)
    refine ⟨Set.Icc (-R) R,isCompact_Icc,?_⟩
    rintro μ ⟨p,⟨F,hF,rfl⟩,rfl⟩
    have hb := probability_tail F g hg hF R hR
    have hsub : (Set.Icc (-R) R)ᶜ ⊆ {a : ℝ | R ≤ |a|} := by
      intro a ha
      by_contra h
      have hab : |a|<R := lt_of_not_ge h
      exact ha ⟨(abs_lt.mp hab).1.le,(abs_lt.mp hab).2.le⟩
    have he : (P F : Measure ℝ).real (Set.Icc (-R) R)ᶜ ≤ δ :=
      (measureReal_mono hsub).trans (hb.trans hMR)
    calc
      _ = ENNReal.ofReal ((P F : Measure ℝ).real (Set.Icc (-R) R)ᶜ) := (ofReal_measureReal (by finiteness)).symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal he
      _ ≤ ε := hδε.le
  have hc := isCompact_closure_of_isTightMeasureSet ht
  have hm : closure S∈sourceFilter.map P := by
    rw [Ultrafilter.mem_map]
    exact Filter.mem_of_superset hgood (fun F hF => subset_closure ⟨F,hF,rfl⟩)
  obtain ⟨ν,_,hν⟩ := hc.ultrafilter_le_nhds' (sourceFilter.map P) hm
  exact ⟨ν,hν⟩

private def stieltjesTest (z : ℂ) (hz : z.im≠0) : BoundedContinuousFunction ℝ ℂ := by
  have hn (a : ℝ) : (a : ℂ)-z≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hz hi
  have hb (a : ℝ) : ‖((a : ℂ)-z)⁻¹‖ ≤ |z.im|⁻¹ := by
    rw [norm_inv]
    apply inv_anti₀ (abs_pos.mpr hz)
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,abs_neg] using
      Complex.abs_im_le_norm ((a : ℂ)-z)
  exact BoundedContinuousFunction.mkOfBound
    ⟨fun a : ℝ => ((a : ℂ)-z)⁻¹,Continuous.inv₀ (by fun_prop) hn⟩ (2*|z.im|⁻¹)
    (fun a b => by
      rw [dist_eq_norm]
      apply (norm_sub_le _ _).trans
      change ‖((a : ℂ)-z)⁻¹‖+‖((b : ℂ)-z)⁻¹‖ ≤ 2*|z.im|⁻¹
      linarith [hb a,hb b])

/-- One generated positive limit simultaneously reads every nonreal source resolvent. -/
theorem actual_stieltjes_limit (g : diagonal.domain) (hg : (g : H)≠0) :
    ∃ ν : ProbabilityMeasure ℝ,
      Tendsto (fun F => sourceProbability F (g : H) hg) (sourceFilter : Filter Index) (𝓝 ν) ∧
      ∀ (z : ℂ),z.im≠0 →
        Tendsto (fun F => (‖(g : H)‖^2)⁻¹ • inner ℂ (g : H) (finiteResolvent F z (g : H)))
          (sourceFilter : Filter Index) (𝓝 (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂(ν : Measure ℝ))) := by
  obtain ⟨ν,hν⟩ := actual_probability_limit g hg
  refine ⟨ν,hν,fun z hz => ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν (stieltjesTest z hz)
  have he (F : Index) : (∫ a : ℝ,stieltjesTest z hz a ∂(sourceProbability F (g : H) hg : Measure ℝ))=
      (‖(g : H)‖^2)⁻¹ • inner ℂ (g : H) (finiteResolvent F z (g : H)) := by
    change (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂((ENNReal.ofReal (‖(g : H)‖^2))⁻¹ • sourceMeasure F (g : H)))=_
    rw [integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofReal (sq_nonneg _),actual_stieltjes F (g : H) z hz]
  simp_rw [he] at h
  exact h

/-- The generated measure has the original source mass and reads the unnormalized response, including the zero input. -/
theorem actual_source_spectral_measure (g : diagonal.domain) :
    ∃ ν : Measure ℝ,IsFiniteMeasure ν ∧ ν Set.univ=ENNReal.ofReal (‖(g : H)‖^2) ∧
      ∀ (z : ℂ),z.im≠0 →
        Tendsto (fun F => inner ℂ (g : H) (finiteResolvent F z (g : H)))
          (sourceFilter : Filter Index) (𝓝 (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂ν)) := by
  by_cases hg : (g : H)=0
  · refine ⟨0,inferInstance,?_,fun z _ => ?_⟩
    · simp [hg]
    · simpa only [hg,map_zero,inner_zero_left,integral_zero_measure] using
        (tendsto_const_nhds : Tendsto (fun _ : Index => (0 : ℂ)) (sourceFilter : Filter Index) (𝓝 0))
  obtain ⟨ν,_,hν⟩ := actual_stieltjes_limit g hg
  let c : ℝ := ‖(g : H)‖^2
  have hc : 0<c := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hg)
  let μ : Measure ℝ := ENNReal.ofReal c • (ν : Measure ℝ)
  have hfinite : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  refine ⟨μ,hfinite,?_,fun z hz => ?_⟩
  · simp only [μ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one,c]
  · have h := (hν z hz).const_smul c
    have he (F : Index) : c • ((‖(g : H)‖^2)⁻¹ • inner ℂ (g : H) (finiteResolvent F z (g : H)))=
        inner ℂ (g : H) (finiteResolvent F z (g : H)) := by
      rw [smul_smul]
      change (c*c⁻¹) • _=_
      rw [mul_inv_cancel₀ hc.ne',one_smul]
    simp_rw [he] at h
    have hi : (∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂μ)=c • ∫ a : ℝ,((a : ℂ)-z)⁻¹ ∂(ν : Measure ℝ) := by
      dsimp only [μ]
      rw [integral_smul_measure,ENNReal.toReal_ofReal hc.le]
    rw [hi]
    exact h

end LowEnergy.SourceHamiltonianSpectralMeasure
