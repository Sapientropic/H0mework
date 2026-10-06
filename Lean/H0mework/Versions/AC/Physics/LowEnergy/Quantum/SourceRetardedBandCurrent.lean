import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRelativePowerTail
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRelativeTailCurrent
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceParticularFrequency
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceEscapeSeedTail
import Mathlib.MeasureTheory.Group.LIntegral

/-! Actual finite-resolvent input, integrated before the unchanged source filter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRetardedBandCurrent
open Filter MeasureTheory GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter)
open SourceFamilyHilbert SourceFamilyOperator
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceParticularFrequency
open FullYSourceFiniteTimeIntegral FullYSourceTimeFamilyGraph SourceRelativePowerTail
open FullYSourceCutoffTimeGraph
open scoped Topology InnerProductSpace

variable (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : ℝ) (hμ : 0 < μ)
include hμ

omit [IsFiniteMeasure ν] in
theorem finite_frequency_continuous (F : Index) :
    Continuous (fun t : ℝ => finiteResolvent F (line μ t)) := by
  apply LipschitzWith.continuous (K := ⟨μ⁻¹*μ⁻¹,by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [dist_eq_norm,Real.dist_eq]
  change ‖finiteResolvent F (line μ t)-finiteResolvent F (line μ s)‖ ≤
    (μ⁻¹*μ⁻¹)*|t-s|
  exact line_resolvent_difference (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) μ hμ t s

omit [IsFiniteMeasure ν] in
theorem finite_input_bound (F : Index) (g : H) (t : ℝ) :
    ‖finiteResolvent F (line μ t) g‖ ≤ μ⁻¹*‖g‖ := by
  apply ((finiteResolvent F (line μ t)).le_opNorm g).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
  exact line_resolvent_norm (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) μ hμ t

theorem finite_input_memLp (F : Index) (g : H) :
    MemLp (fun t : ℝ => finiteResolvent F (line μ t) g) 2 ν :=
  MemLp.of_bound
    (((finite_frequency_continuous μ hμ F).clm_apply continuous_const).aestronglyMeasurable)
    (μ⁻¹*‖g‖) (Eventually.of_forall (finite_input_bound μ hμ F g))

def finiteInput (F : Index) (g : H) : Lp H 2 ν :=
  (finite_input_memLp ν μ hμ F g).toLp (fun t => finiteResolvent F (line μ t) g)

theorem finite_input_l2_bound (F : Index) (g : H) :
    ‖finiteInput ν μ hμ F g‖ ≤
      (measureUnivNNReal ν : ℝ)^((2 : ℝ)⁻¹)*(μ⁻¹*‖g‖) := by
  have hb := Lp.norm_le_of_ae_bound (f := finiteInput ν μ hμ F g)
    (by positivity : 0 ≤ μ⁻¹*‖g‖) (by
    filter_upwards [(finite_input_memLp ν μ hμ F g).coeFn_toLp] with t ht
    change ‖((finite_input_memLp ν μ hμ F g).toLp _) t‖ ≤ _
    rw [ht]
    exact finite_input_bound μ hμ F g t)
  simpa using hb

def actualInputFamily (g : H) : Family (Lp H 2 ν) sourceFilter where
  val F := finiteInput ν μ hμ F g
  property := ⟨(measureUnivNNReal ν : ℝ)^((2 : ℝ)⁻¹)*(μ⁻¹*‖g‖),
    by positivity,fun F => finite_input_l2_bound ν μ hμ F g⟩

def actualInput (g : H) : TimeSpace ν := (actualInputFamily ν μ hμ g : TimeSpace ν)

/-- The input is the actual R_F(z)g family, with its L² cost generated above. -/
theorem actual_retarded_relative_tail (g : H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖familyReader ν (relativeTail m ell) (actualInput ν μ hμ g)‖ < ε :=
  time_space_relative_tail ν (actualInput ν μ hμ g)

def currentValue (F : Index) (m ell : ℕ) (g : H) (t : ℝ) : H :=
  SourceMinimalGraphParticular.sourceParticular (star (line μ t))
      (relativeTail m ell (finiteResolvent F (line μ t) g))-
    (finiteResolvent F (line μ t)).adjoint
      (relativeTail m ell (finiteResolvent F (line μ t) g))

omit [IsFiniteMeasure ν] in
theorem current_value_bound (F : Index) (m ell : ℕ) (g : H) (t : ℝ) :
    ‖currentValue μ F m ell g t‖ ≤
      (2/μ)*‖relativeTail m ell (finiteResolvent F (line μ t) g)‖ := by
  simpa only [currentValue,line_im,abs_of_pos hμ] using
    SourceRelativeTailCurrent.finite_current_bound F (line μ t)
      (by simpa only [line_im] using ne_of_gt hμ)
      (relativeTail m ell (finiteResolvent F (line μ t) g))

omit [IsFiniteMeasure ν] in
theorem current_value_continuous (F : Index) (m ell : ℕ) (g : H) :
    Continuous (currentValue μ F m ell g) := by
  have hi := (finite_frequency_continuous μ hμ F).clm_apply (continuous_const (y := g))
  have ht := (relativeTail m ell).continuous.comp hi
  exact (((original_particular_frequency_lipschitz μ hμ).continuous.clm_apply ht).sub
    ((ContinuousLinearMap.adjoint.continuous.comp
      (finite_frequency_continuous μ hμ F)).clm_apply ht))

theorem current_memLp (F : Index) (m ell : ℕ) (g : H) :
    MemLp (currentValue μ F m ell g) 2 ν := by
  apply MemLp.of_bound (current_value_continuous μ hμ F m ell g).aestronglyMeasurable
    ((2/μ)*(‖relativeTail m ell‖*(μ⁻¹*‖g‖)))
  apply Eventually.of_forall
  intro t
  apply (current_value_bound μ hμ F m ell g t).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/μ)
  exact ((relativeTail m ell).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (finite_input_bound μ hμ F g t) (norm_nonneg _))

def finiteCurrent (F : Index) (m ell : ℕ) (g : H) : Lp H 2 ν :=
  (current_memLp ν μ hμ F m ell g).toLp (currentValue μ F m ell g)

theorem finite_current_l2_bound (F : Index) (m ell : ℕ) (g : H) :
    ‖finiteCurrent ν μ hμ F m ell g‖ ≤
      (2/μ)*‖(relativeTail m ell).compLpL 2 ν (finiteInput ν μ hμ F g)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(current_memLp ν μ hμ F m ell g).coeFn_toLp,
    (relativeTail m ell).coeFn_compLpL (finiteInput ν μ hμ F g),
    (finite_input_memLp ν μ hμ F g).coeFn_toLp] with t hc ht hi
  change ‖((current_memLp ν μ hμ F m ell g).toLp _) t‖ ≤ _
  rw [hc,ht]
  change ‖currentValue μ F m ell g t‖ ≤
    (2/μ)*‖relativeTail m ell (((finite_input_memLp ν μ hμ F g).toLp _) t)‖
  rw [hi]
  exact current_value_bound μ hμ F m ell g t

def actualCurrentFamily (m ell : ℕ) (g : H) : Family (Lp H 2 ν) sourceFilter where
  val F := finiteCurrent ν μ hμ F m ell g
  property := ⟨(2/μ)*‖(relativeTail m ell).compLpL 2 ν‖*
    ((measureUnivNNReal ν : ℝ)^((2 : ℝ)⁻¹)*(μ⁻¹*‖g‖)),by positivity,fun F => by
      apply (finite_current_l2_bound ν μ hμ F m ell g).trans
      have hb := ((relativeTail m ell).compLpL 2 ν).le_opNorm (finiteInput ν μ hμ F g)
      have hr := hb.trans (mul_le_mul_of_nonneg_left
        (finite_input_l2_bound ν μ hμ F g) (norm_nonneg _))
      exact (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2/μ)).trans_eq (by ring)⟩

def actualCurrent (m ell : ℕ) (g : H) : TimeSpace ν :=
  (actualCurrentFamily ν μ hμ m ell g : TimeSpace ν)

theorem actual_current_norm (m ell : ℕ) (g : H) :
    ‖actualCurrent ν μ hμ m ell g‖ ≤
      (2/μ)*‖familyReader ν (relativeTail m ell) (actualInput ν μ hμ g)‖ := by
  change ‖((actualCurrentFamily ν μ hμ m ell g) : TimeSpace ν)‖ ≤
    (2/μ)*‖lift sourceFilter (SourceFamilyOperator.constant ((relativeTail m ell).compLpL 2 ν))
      ((actualInputFamily ν μ hμ g) : TimeSpace ν)‖
  rw [lift_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (norm_tendsto sourceFilter _)
    ((norm_tendsto sourceFilter _).const_mul (2/μ))
  exact Eventually.of_forall (fun F => finite_current_l2_bound ν μ hμ F m ell g)

/-- This is the actual two-resolvent current, not a supplied body or fixed surrogate seed. -/
theorem actual_retarded_current_tail (g : H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖actualCurrent ν μ hμ m ell g‖ < ε := by
  intro ε hε
  have hC : 0 < 2/μ := by positivity
  obtain ⟨N,hN⟩ := actual_retarded_relative_tail ν μ hμ g (ε/(2/μ)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell => ?_⟩
  apply (actual_current_norm ν μ hμ m ell g).trans_lt
  have h := mul_lt_mul_of_pos_left (hN m hm ell hell) hC
  simpa only [mul_div_cancel₀ ε (ne_of_gt hC)] using h

omit [IsFiniteMeasure ν] hμ in
theorem relative_tail_contraction (m ell : ℕ) (hle : m ≤ ell) (x : H) :
    ‖relativeTail m ell x‖ ≤ ‖x‖ := by
  have hpower := positive_power_distance sourceComplement
    source_complement_nonnegative source_complement_le_one x (Nat.zero_le (m+1))
  simp only [pow_zero,one_apply_eq_self] at hpower
  have htail := positive_power_distance sourceComplement
    source_complement_nonnegative source_complement_le_one x
    (show m+1 ≤ ell+1 by omega)
  rw [norm_sub_rev] at htail
  change ‖(sourceComplement^(m+1)) x-(sourceComplement^(ell+1)) x‖ ≤ ‖x‖
  nlinarith [norm_nonneg ((sourceComplement^(m+1)) x-(sourceComplement^(ell+1)) x),
    norm_nonneg x,sq_nonneg ‖(sourceComplement^(ell+1)) x‖,
    sq_nonneg ‖(sourceComplement^(m+1)) x-x‖]

omit [IsFiniteMeasure ν] in
theorem source_retarded_high_frequency (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ t : ℝ, t ≠ 0 →
      ‖finiteResolvent F (line μ t) (g : H)‖ ≤
        |t|⁻¹*(μ⁻¹*‖diagonal g‖+‖(g : H)‖) := by
  filter_upwards [GaussGradedCompression.eventually_exact g] with F hF
  intro t ht
  have hz : (line μ t).im ≠ 0 := by simpa only [line_im] using ne_of_gt hμ
  have hz0 : line μ t ≠ 0 := by intro h; exact hz (h ▸ rfl)
  have hr := congrArg (fun T : H →L[ℂ] H => T (g : H))
    (resolvent_compression (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) (line μ t) hz)
  change finiteResolvent F (line μ t) (GaussGradedCompression.compression F (g : H))=
    (g : H)+(line μ t) • finiteResolvent F (line μ t) (g : H) at hr
  rw [hF] at hr
  have identity : finiteResolvent F (line μ t) (g : H)=
      (line μ t)⁻¹ • (finiteResolvent F (line μ t) (diagonal g)-(g : H)) := by
    rw [hr,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hz0,one_smul]
  rw [identity,norm_smul,norm_inv]
  have hn : |t| ≤ ‖line μ t‖ := by
    simpa [line] using Complex.abs_re_le_norm (line μ t)
  have hi := inv_anti₀ (abs_pos.mpr ht) hn
  have hb : ‖finiteResolvent F (line μ t) (diagonal g)-(g : H)‖ ≤
      μ⁻¹*‖diagonal g‖+‖(g : H)‖ := by
    have h := finite_input_bound μ hμ F (diagonal g) t
    have hs := norm_sub_le (finiteResolvent F (line μ t) (diagonal g)) (g : H)
    linarith
  exact mul_le_mul hi hb (norm_nonneg _) (by positivity)

omit [IsFiniteMeasure ν] in
theorem actual_current_spectral_tail (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ m ell : ℕ, m ≤ ell →
      ∀ t : ℝ, t ≠ 0 → ‖currentValue μ F m ell (g : H) t‖ ≤
        |t|⁻¹*((2/μ)*(μ⁻¹*‖diagonal g‖+‖(g : H)‖)) := by
  filter_upwards [source_retarded_high_frequency μ hμ g] with F hF
  intro m ell hle t ht
  have hb := (current_value_bound μ hμ F m ell (g : H) t).trans
    (mul_le_mul_of_nonneg_left
      ((relative_tail_contraction m ell hle _).trans (hF t ht)) (by positivity : 0 ≤ 2/μ))
  exact hb.trans_eq (by ring)

omit [IsFiniteMeasure ν] hμ in
theorem inverse_square_lintegral_bound (f : ℝ → H) (Λ C : ℝ) (hΛ : 0 < Λ)
    (bound : ∀ l : ℝ, Λ < l → ‖f l‖ ≤ l⁻¹*C) :
    (∫⁻ l in Set.Ioi Λ, ENNReal.ofReal (‖f l‖^2)) ≤ ENNReal.ofReal (C^2/Λ) := by
  have he : (-2 : ℝ) < -1 := by norm_num
  have hi := (integrableOn_Ioi_rpow_of_lt he hΛ).const_mul (C^2)
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi Λ)] (fun l : ℝ => C^2*l^(-2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (hΛ.trans hl).le _)
  have integral : (∫ l : ℝ in Set.Ioi Λ, C^2*l^(-2 : ℝ))=C^2/Λ := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt he hΛ]
    norm_num [Real.rpow_neg_one,div_eq_mul_inv]
  rw [←integral,ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  apply ENNReal.ofReal_le_ofReal
  have hb := pow_le_pow_left₀ (norm_nonneg (f l)) (bound l hl) 2
  have power : (l⁻¹*C)^2=C^2*l^(-2 : ℝ) := by
    rw [Real.rpow_neg (hΛ.trans hl).le,Real.rpow_two]
    ring
  exact hb.trans_eq power

omit [IsFiniteMeasure ν] in
/-- One source-generated cofinal set precedes every cutoff pair and both frequency half-lines. -/
theorem actual_current_high_frequency (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ m ell : ℕ, m ≤ ell →
      ∀ (negative : Bool) (Λ : ℝ), 0 < Λ →
      (∫⁻ l in Set.Ioi Λ, ENNReal.ofReal
        (‖currentValue μ F m ell (g : H) (if negative then -l else l)‖^2)) ≤
      ENNReal.ofReal (((2/μ)*(μ⁻¹*‖diagonal g‖+‖(g : H)‖))^2/Λ) := by
  filter_upwards [actual_current_spectral_tail μ hμ g] with F hF
  intro m ell hle negative Λ hΛ
  apply inverse_square_lintegral_bound _ Λ _ hΛ
  intro l hl
  have hlpos := hΛ.trans hl
  have habs : |(if negative then -l else l : ℝ)|=l := by
    cases negative <;> simp [abs_of_pos hlpos]
  have ht : (if negative then -l else l : ℝ) ≠ 0 := by
    apply abs_pos.mp
    rw [habs]
    exact hlpos
  have h := hF m ell hle (if negative then -l else l) ht
  rwa [habs] at h

theorem finite_current_integral (F : Index) (m ell : ℕ) (g : H) :
    (∫⁻ t, ENNReal.ofReal (‖currentValue μ F m ell g t‖^2) ∂ν)=
      ENNReal.ofReal (‖finiteCurrent ν μ hμ F m ell g‖^2) := by
  have he : (fun t => ‖currentValue μ F m ell g t‖^2) =ᵐ[ν]
      (fun t => ‖(finiteCurrent ν μ hμ F m ell g) t‖^2) := by
    filter_upwards [(current_memLp ν μ hμ F m ell g).coeFn_toLp] with t ht
    change _=‖((current_memLp ν μ hμ F m ell g).toLp _) t‖^2
    rw [ht]
  have hi := (square_integrable ν (finiteCurrent ν μ hμ F m ell g)).congr he.symm
  have hn : 0 ≤ᵐ[ν] (fun t => ‖currentValue μ F m ell g t‖^2) :=
    Eventually.of_forall (fun _ => sq_nonneg _)
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn,integral_congr_ae he,
    ←square_integral]

omit [IsFiniteMeasure ν] hμ in
theorem full_frequency_split_le (f : ℝ → ENNReal) (Λ : ℝ) :
    (∫⁻ t, f t) ≤ (∫⁻ t in Set.Icc (-Λ) Λ, f t)+
      (∫⁻ t in Set.Ioi Λ, f t)+(∫⁻ t in Set.Ioi Λ, f (-t)) := by
  have negative : (∫⁻ t in Set.Iio (-Λ), f t)=(∫⁻ t in Set.Ioi Λ, f (-t)) := by
    have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ)) ((Set.Iio (-Λ)).indicator f)
    have hi : (fun t => (Set.Iio (-Λ)).indicator f (-t))=
        (Set.Ioi Λ).indicator (fun t => f (-t)) := by
      funext t
      simp only [Set.indicator,Set.mem_Iio,Set.mem_Ioi,neg_lt_neg_iff]
    rw [hi,lintegral_indicator measurableSet_Ioi,lintegral_indicator measurableSet_Iio] at h
    exact h.symm
  have cover : (Set.univ : Set ℝ)=(Set.Icc (-Λ) Λ ∪ Set.Ioi Λ) ∪ Set.Iio (-Λ) := by
    ext t
    simp only [Set.mem_univ,Set.mem_union,Set.mem_Icc,Set.mem_Ioi,Set.mem_Iio,true_iff]
    by_cases hright : t ≤ Λ
    · by_cases hleft : -Λ ≤ t
      · exact Or.inl (Or.inl ⟨hleft,hright⟩)
      · exact Or.inr (lt_of_not_ge hleft)
    · exact Or.inl (Or.inr (lt_of_not_ge hright))
  calc
    _ = ∫⁻ t in (Set.Icc (-Λ) Λ ∪ Set.Ioi Λ) ∪ Set.Iio (-Λ), f t := by
      rw [←cover,Measure.restrict_univ]
    _ ≤ (∫⁻ t in Set.Icc (-Λ) Λ ∪ Set.Ioi Λ, f t)+(∫⁻ t in Set.Iio (-Λ), f t) :=
      lintegral_union_le _ _ _
    _ ≤ ((∫⁻ t in Set.Icc (-Λ) Λ, f t)+(∫⁻ t in Set.Ioi Λ, f t))+
        (∫⁻ t in Set.Iio (-Λ), f t) := by
      gcongr
      exact lintegral_union_le _ _ _
    _ = _ := by rw [negative]

omit [IsFiniteMeasure ν] in
/-- Every actual finite F is integrated over all frequencies before the original filter. -/
theorem actual_current_full_frequency_tail (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal (‖currentValue μ F m ell (g : H) t‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let C := (2/μ)*(μ⁻¹*‖diagonal g‖+‖(g : H)‖)
  let Λ := 1+4*C^2/ε
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  have hsmall : C^2/Λ ≤ ε/4 := by
    apply (div_le_iff₀ hΛ).mpr
    dsimp [Λ]
    field_simp
    nlinarith [sq_nonneg C]
  let νΛ : Measure ℝ := volume.restrict (Set.Icc (-Λ) Λ)
  let : IsFiniteMeasure νΛ := inferInstance
  have heps : 0 < Real.sqrt (ε/4) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨N,hN⟩ := actual_retarded_current_tail νΛ μ hμ (g : H) _ heps
  refine ⟨N,fun m hm ell hell => ?_⟩
  have hn := hN m hm ell hell
  have hsqrt : (Real.sqrt (ε/4))^2=ε/4 := Real.sq_sqrt (by positivity)
  have hnorm : ‖actualCurrent νΛ μ hμ m ell (g : H)‖^2 < ε/2 := by
    nlinarith [norm_nonneg (actualCurrent νΛ μ hμ m ell (g : H))]
  have ht := square_tendsto sourceFilter (actualCurrentFamily νΛ μ hμ m ell (g : H))
  have htarget : ‖actualCurrentFamily νΛ μ hμ m ell (g : H)‖^2 < ε/2 := by
    simpa only [actualCurrent,UniformSpace.Completion.norm_coe] using hnorm
  have hb := ht.eventually (gt_mem_nhds htarget)
  filter_upwards [hb,actual_current_high_frequency μ hμ g] with F hF htail
  have band : (∫⁻ t in Set.Icc (-Λ) Λ,
      ENNReal.ofReal (‖currentValue μ F m ell (g : H) t‖^2)) ≤ ENNReal.ofReal (ε/2) := by
    change (∫⁻ t, ENNReal.ofReal (‖currentValue μ F m ell (g : H) t‖^2) ∂νΛ) ≤ _
    rw [finite_current_integral νΛ μ hμ F m ell (g : H)]
    exact ENNReal.ofReal_le_ofReal hF.le
  have tails (negative : Bool) :
      (∫⁻ t in Set.Ioi Λ, ENNReal.ofReal
        (‖currentValue μ F m ell (g : H) (if negative then -t else t)‖^2)) ≤
        ENNReal.ofReal (ε/4) :=
    (htail m ell hell negative Λ hΛ).trans (ENNReal.ofReal_le_ofReal hsmall)
  apply (full_frequency_split_le (fun t => ENNReal.ofReal
    (‖currentValue μ F m ell (g : H) t‖^2)) Λ).trans
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) := by
      have hp := tails false
      have hn := tails true
      simp only [Bool.false_eq_true,if_false,if_true] at hp hn
      exact add_le_add (add_le_add band hp) hn
    _ = _ := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2+ε/4) (by positivity : 0 ≤ ε/4)]
      congr 1
      ring

#print axioms finite_input_memLp
#print axioms actual_retarded_relative_tail
#print axioms actual_current_norm
#print axioms actual_retarded_current_tail
#print axioms actual_current_spectral_tail
#print axioms actual_current_high_frequency
#print axioms actual_current_full_frequency_tail
end LowEnergy.SourceRetardedBandCurrent
