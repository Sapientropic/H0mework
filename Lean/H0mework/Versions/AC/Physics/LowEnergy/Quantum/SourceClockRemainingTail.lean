import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockSourceTail
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockSourceFixedReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockRemainingTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory GaussAdjointHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourcePhysicalKineticSquare
open SourceClockAcceleration SourceClockReflectedForm SourceClockWindowTime SourceClockSourceTail
open SourceRadiusHalfWindow SourceRadiusHalfSourceBudget SourceResolventBandLimit
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology

private theorem lapse_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem radius_le_price (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    2*(sourceTime 0)^2*radiusForm (halfAction m ell (state F z hz g))  ≤
      sourcePrice F m ell z hz g := by
  rw [actual_clock_source_price]
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction (halfAction m ell (state F z hz g)))
  have hs : 0  ≤  scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g))) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc' := mul_nonneg (show 0  ≤  (sourceTime 0)^2/4 by positivity) hc
  have hs' := mul_nonneg (show 0  ≤  (sourceTime 0)^2/2 by positivity) hs
  linarith only [hc',hs']

def prefixNormPrice (τ : ℝ) (m : ℕ) : ℝ :=
  (2/25:ℝ)*((2/25:ℝ)+2*τ*(sourceTime 0)^2)/(8*τ*(sourceTime 0)^2*(m+2:ℝ))

/-- The fixed H0 source is absorbed with a freely chosen next-source coefficient;
the residue contains only its original unweighted resolvent norm. -/
theorem actual_fixed_prefix_absorption (τ : ℝ) (hτ : 0<τ) (F : Index) (m ell : ℕ)
    (hml : m ≤ ell) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (2/25:ℝ)*‖embed (halfAction m ell (state F z hz (iterate 1 g)))‖^2  ≤
      τ*sourcePrice F m ell z hz (iterate 1 g)+
        prefixNormPrice τ m*‖embed (state F z hz (iterate 1 g))‖^2 := by
  have hn := lapse_pos
  have h := original_half_radius_absorption (2/25:ℝ) (2*τ*(sourceTime 0)^2)
    (by norm_num) (by positivity) m ell hml (state F z hz (iterate 1 g))
  have hp := mul_le_mul_of_nonneg_left (radius_le_price F m ell z hz (iterate 1 g)) hτ.le
  have he : (2/25:ℝ)*((2/25:ℝ)+2*τ*(sourceTime 0)^2)/
      (4*(2*τ*(sourceTime 0)^2)*(m+2:ℝ))=prefixNormPrice τ m := by
    unfold prefixNormPrice
    ring
  rw [he] at h
  nlinarith only [h,hp]

def prefixError (τ : ℝ) (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  prefixNormPrice τ m*‖embed (state F z hz (iterate 1 g))‖^2+
    4*dampingError z.im m ell (state F z hz g)

/-- One source-filter event generates the recursive source-price inequality before
the cutoff, frequency, causal orientation, and contraction factor are selected. -/
theorem actual_source_price_prefix_step (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ m ell : ℕ,m ≤ ell →
      ∀ z : ℂ,∀ hz : z.im≠0,∀ τ : ℝ,0<τ →
        sourcePrice F m ell z hz g  ≤
          4*undampedRemainder F m ell z hz g+
          τ*sourcePrice F m ell z hz (iterate 1 g)+prefixError τ F m ell z hz g := by
  filter_upwards [actual_source_price_joint_upper g] with F hF m ell hml z hz τ hτ
  have h := hF m ell z hz
  have hp := actual_fixed_prefix_absorption τ hτ F m ell hml z hz g
  unfold prefixError
  linarith only [h,hp]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem causal_norm (advanced : Bool) (F : Index) (ν w : ℝ) (hν : 0<ν)
    (g : diagonal.domain) :
    ‖embed (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g)‖=
      ‖finiteResolvent F (line ν w) (g:H)‖ := by
  rw [state_embed]
  cases advanced
  · rfl
  · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line ν w)
      (by simpa only [line_im] using hν.ne') (g:H)

private theorem damping_causal (advanced : Bool) (ν w : ℝ) (m ell : ℕ) (q : QuantumTest) :
    dampingError (causalPoint advanced ν w).im m ell q=dampingError ν m ell q := by
  cases advanced <;> simp [causalPoint,line_im,dampingError]

private theorem prefix_norm_price_nonneg (τ : ℝ) (hτ : 0<τ) (m : ℕ) :
    0 ≤ prefixNormPrice τ m := by
  unfold prefixNormPrice
  positivity

/-- The freely-small successor price costs only an explicit original source norm
plus the already-paid damping remainder, on both independent causal legs. -/
theorem actual_prefix_error_full_frequency (τ : ℝ) (hτ : 0<τ) (ν : ℝ) (hν : 0<ν)
    (advanced : Bool) (F : Index) (m ell : ℕ) (hml : m ≤ ell) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (prefixError τ F m ell (causalPoint advanced ν w)
      (causal_nonreal advanced ν w hν) g))  ≤
      ENNReal.ofReal (prefixNormPrice τ m*(Real.pi/ν*‖(iterate 1 g:H)‖^2))+
        4*ENNReal.ofReal ((6*ν^2*(6*ν^2+(sourceTime 0)^2)/
          (4*(sourceTime 0)^2*(m+2:ℝ)))*(Real.pi/ν*‖(g:H)‖^2)) := by
  have hp := prefix_norm_price_nonneg τ hτ m
  have hi : Integrable (fun w : ℝ => ‖finiteResolvent F (line ν w) (iterate 1 g:H)‖^2) := by
    simpa only [line,mul_comm] using SourceActualResolventEnergy.actual_square_integrable F ν hν (iterate 1 g:H)
  have hi' : AEMeasurable (fun w : ℝ => ENNReal.ofReal (prefixNormPrice τ m*
      ‖finiteResolvent F (line ν w) (iterate 1 g:H)‖^2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hi.const_mul _).aestronglyMeasurable.aemeasurable
  have hsplit (w : ℝ) : ENNReal.ofReal (prefixError τ F m ell (causalPoint advanced ν w)
      (causal_nonreal advanced ν w hν) g)=
      ENNReal.ofReal (prefixNormPrice τ m*‖finiteResolvent F (line ν w) (iterate 1 g:H)‖^2)+
        ENNReal.ofReal (4:ℝ)*ENNReal.ofReal (dampingError ν m ell
          (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g)) := by
    unfold prefixError
    rw [damping_causal,causal_norm advanced F ν w hν (iterate 1 g)]
    have hd : 0 ≤ dampingError ν m ell
        (state F (causalPoint advanced ν w) (causal_nonreal advanced ν w hν) g) := by
      unfold dampingError
      exact le_max_left _ _
    rw [ENNReal.ofReal_add (mul_nonneg hp (sq_nonneg _))
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hd),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  simp_rw [hsplit]
  rw [lintegral_add_left' hi']
  simp_rw [ENNReal.ofReal_mul hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line ν w) (iterate 1 g:H)‖^2))=
      ENNReal.ofReal (Real.pi/ν*‖(iterate 1 g:H)‖^2) := by
    simpa only [line,mul_comm] using SourceActualResolventEnergy.actual_square_lintegral F ν hν (iterate 1 g:H)
  rw [he,←ENNReal.ofReal_mul hp]
  norm_num only [ENNReal.ofReal_ofNat]
  exact add_le_add (le_refl _) (mul_le_mul (le_refl _)
    (actual_damping_error_full_frequency advanced m ell hml F ν hν g) bot_le bot_le)

/-- One source-owned cutoff pays the entire prefix residue for every F, both
causal orientations, and all later upper windows; no weighted-domain input is used. -/
theorem actual_prefix_error_common_tail (τ : ℝ) (hτ : 0<τ) (ν : ℝ) (hν : 0<ν)
    (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N  ≤  m → ∀ ell, m  ≤  ell → ∀ F : Index,∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (prefixError τ F m ell (causalPoint advanced ν w)
        (causal_nonreal advanced ν w hν) g))  ≤  ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ((2/25:ℝ)*((2/25:ℝ)+2*τ*(sourceTime 0)^2)/(8*τ*(sourceTime 0)^2))*
      (Real.pi/ν*‖(iterate 1 g:H)‖^2)+
    4*(6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2))*(Real.pi/ν*‖(g:H)‖^2)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F advanced => ?_⟩
  have hn : (N:ℝ) ≤ m := by exact_mod_cast hm
  have hC : C<(N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  have hb : C/(m+2:ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hn,hC,hε]
  have ha : 0 ≤ prefixNormPrice τ m*(Real.pi/ν*‖(iterate 1 g:H)‖^2) := by
    exact mul_nonneg (prefix_norm_price_nonneg τ hτ m) (by positivity)
  have hd : 0 ≤ (6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*
      (Real.pi/ν*‖(g:H)‖^2) := by positivity
  have he : prefixNormPrice τ m*(Real.pi/ν*‖(iterate 1 g:H)‖^2)+
      4*((6*ν^2*(6*ν^2+(sourceTime 0)^2)/(4*(sourceTime 0)^2*(m+2:ℝ)))*
      (Real.pi/ν*‖(g:H)‖^2))=C/(m+2:ℝ) := by
    unfold prefixNormPrice C
    field_simp
  apply (actual_prefix_error_full_frequency τ hτ ν hν advanced F m ell hml g).trans
  rw [show (4:ENNReal)=ENNReal.ofReal (4:ℝ) by norm_num,
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),←ENNReal.ofReal_add ha (mul_nonneg (by norm_num) hd),he]
  exact ENNReal.ofReal_le_ofReal hb

private theorem iterate_one (r : ℕ) (g : diagonal.domain) :
    iterate 1 (iterate r g)=iterate (r+1) g := by
  simp only [iterate,pow_succ',Module.End.mul_apply,pow_zero,Module.End.one_apply]

/-- The original fixed-source prefix produces the complete finite recursive
budget. Every signed source department is kept, and the last source is explicit. -/
theorem actual_source_price_prefix (r : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ m ell : ℕ,m  ≤  ell →
      ∀ z : ℂ,∀ hz : z.im≠0,∀ τ : ℝ,0<τ →
        sourcePrice F m ell z hz g  ≤
          (∑ j∈Finset.range r,τ^j*(4*undampedRemainder F m ell z hz (iterate j g)+
            prefixError τ F m ell z hz (iterate j g)))+
          τ^r*sourcePrice F m ell z hz (iterate r g) := by
  induction r with
  | zero =>
    filter_upwards [] with F m ell hml z hz τ hτ
    simp only [Finset.sum_range_zero,pow_zero,iterate,Module.End.one_apply,one_mul,zero_add,le_refl]
  | succ r ih =>
    filter_upwards [ih,actual_source_price_prefix_step (iterate r g)] with F hi hs m ell hml z hz τ hτ
    have h := hi m ell hml z hz τ hτ
    have hs' := hs m ell hml z hz τ hτ
    rw [iterate_one] at hs'
    have hp := mul_le_mul_of_nonneg_left hs' (pow_nonneg hτ.le r)
    rw [Finset.sum_range_succ,pow_succ]
    nlinarith only [h,hp]

end LowEnergy.SourceClockRemainingTail
