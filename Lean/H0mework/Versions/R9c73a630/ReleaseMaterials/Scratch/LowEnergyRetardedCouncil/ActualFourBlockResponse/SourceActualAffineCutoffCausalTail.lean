import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineCutoffTail
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualAffineCutoffCausalTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussRadialDomain GaussYukawaCoefficient GaussUnitaryHistory SourceNativeCutoffContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarAffineCutoffTail SourceMixedNativeReturn SourceRelativePowerTail ActualVectorJointCost
open SourceLocalizedInverseFormPayment GaussNativeForm GaussNativeMatter GaussLiveMomentum
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace ContDiff Topology
open Lean Meta Elab Term

elab "paid_affine_cutoff%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineCutoffTail 0) "LowEnergy")
    "SourceScalarAffineCutoffTail"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

elab "paid_gauge_cutoff%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarGaugeScale 0) "LowEnergy") "SourceScalarGaugeScale") "theta_invariant")

private theorem causal_nonreal (advanced : Bool) (μ w : ℝ) (hμ : 0 < μ) :
    (causalFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem causal_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (causalFrequency advanced μ w)) := by
  have he (w : ℝ) : causalFrequency advanced μ w = actualFrequency advanced μ w := by
    cases advanced
    · rfl
    · apply Complex.ext <;> simp [causalFrequency,actualFrequency,line]
  simp_rw [he]
  exact (paid_clock_tail% frequency_continuous) advanced μ hμ F

/-- The actual affine jet acts on the same core lift of the original resolvent. -/
theorem actual_affine_source_read (F : Index) (g : diagonal.domain) (m ell : ℕ)
    (z : ℂ) (hz : z.im ≠ 0) :
    sourceRead F g (SourceScalarVirialBulk.deltaPhi (SourceNativeCutoffContact.thetaAction m ell))
      (finiteResolvent F z (g : H)) =
    embed (SourceScalarVirialBulk.deltaPhi (SourceNativeCutoffContact.thetaAction m ell)
      (coreEquiv.symm (SourceEscapeCurrent.sourceCore F z hz g))) :=
  source_read_resolvent F g _ z hz

/-- Gauge dilation leaves the original scalar-only cutoff fixed. -/
theorem actual_gauge_cutoff_zero (m ell : ℕ) :
    SourceScalarGaugeScale.deltaGauge (SourceNativeCutoffContact.thetaAction m ell) = 0 := by
  have h := (paid_gauge_cutoff%) m ell
  have he : SourceNativeCutoffContact.thetaAction m ell = SourceMixedNativeReturn.thetaAction m ell := by
    rw [SourceNativeCutoffContact.theta_action_polynomial]
    rfl
  rw [he]
  exact sub_eq_zero.mpr h.eq


theorem actual_euler_causal_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ∀ advanced : Bool, (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (eulerAction m ell)
          (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2))  ≤  ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_bounded_theta_causal_tail μ hμ (ContinuousLinearMap.id ℂ H) (g : H) (ε/36) (by positivity)
  refine ⟨2*N+2,fun m hm ell hell => ?_⟩
  have hm0 : 1 ≤ m := by omega
  have hmN : N ≤ m/2 := by omega
  have heN : N ≤ ell/2 := by omega
  filter_upwards [hN (m/2) hmN m (Nat.div_le_self m 2),
    hN (ell/2) heN ell (Nat.div_le_self ell 2)] with F hA hB
  intro advanced
  have hA := hA advanced
  have hB := hB advanced
  simp only [ContinuousLinearMap.id_apply] at hA hB
  have hb (w : ℝ) : ‖sourceRead F g (eulerAction m ell) (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2 ≤
      18*(‖relativeTail (m/2) m (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2+
          ‖relativeTail (ell/2) ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2) := by
    have hz := causal_nonreal advanced μ w hμ
    rw [source_read_resolvent F g (eulerAction m ell) (causalFrequency advanced μ w) hz]
    have h := actual_euler_norm_domination m ell hm0 hell (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (causalFrequency advanced μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (causalFrequency advanced μ w) hz g))=
        finiteResolvent F (causalFrequency advanced μ w) (g : H) :=
      congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simpa only [hv] using! h
  have hmA : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖relativeTail (m/2) m (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) :=
    ((((relativeTail (m/2) m).continuous.comp
      ((causal_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _  ≤  ∫⁻ w : ℝ, ENNReal.ofReal 18*(ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)+
        ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      exact (paid_affine_cutoff% point_energy) _ _ _ (sq_nonneg _) (sq_nonneg _) (hb w)
    _ = ENNReal.ofReal 18*((∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (m/2) m (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal (‖relativeTail (ell/2) ell (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hmA]
    _  ≤  ENNReal.ofReal 18*(ENNReal.ofReal (ε/36)+ENNReal.ofReal (ε/36)) := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
      congr 1
      ring

theorem actual_contact_causal_energy (v : Ambient) (m ell : ℕ) (hle : m≤ell)
    (F : Index) (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) :
    (∫⁻ w : ℝ, ENNReal.ofReal
      (‖boundedContact v m ell hle (finiteResolvent F (causalFrequency advanced μ w) g)‖^2))≤
      ENNReal.ofReal ((2*‖v.1‖/(m+2 : ℝ))^2*(Real.pi/μ)*‖g‖^2) := by
  let C := 2*‖v.1‖/(m+2 : ℝ)
  have hb (w : ℝ) : ‖boundedContact v m ell hle (finiteResolvent F (causalFrequency advanced μ w) g)‖^2≤
      C^2*‖finiteResolvent F (causalFrequency advanced μ w) g‖^2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (bounded_contact_bound v m ell hle _) 2).trans_eq
      (mul_pow C _ 2)
  have he : (∫⁻ w : ℝ, ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w) g‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖g‖^2) := by
    have hn (w : ℝ) : ‖finiteResolvent F (causalFrequency advanced μ w) g‖ =
        ‖finiteResolvent F (line μ w) g‖ := by
      have he : causalFrequency advanced μ w = actualFrequency advanced μ w := by
        cases advanced
        · rfl
        · apply Complex.ext <;> simp [causalFrequency,actualFrequency,line]
      rw [he]
      exact (paid_clock_tail% frequency_norm) advanced μ hμ F g w
    simp_rw [hn]
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_lintegral F μ hμ g
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (C^2)*
        ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg C)]
      exact ENNReal.ofReal_le_ofReal (hb w)
    _ = ENNReal.ofReal (C^2)*∫⁻ w : ℝ,
        ENNReal.ofReal (‖finiteResolvent F (causalFrequency advanced μ w) g‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [he,←ENNReal.ofReal_mul (sq_nonneg C)]; congr 1; dsimp [C]; ring

private theorem vacuum_causal_contact_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, ∀ hell : m ≤ ell, ∀ F : Index, ∀ advanced : Bool,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖boundedContact ((vacuum : Scalar),0) m ell hell
        (finiteResolvent F (causalFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (2*‖vacuum‖)^2*(Real.pi/μ)*‖g‖^2
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hell F advanced => (actual_contact_causal_energy ((vacuum : Scalar),0) m ell hell F advanced μ hμ g).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hmR : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hd : 0<(m+2 : ℝ) := by positivity
  have hdiv : C/ε<(m+2 : ℝ) := by linarith
  have hc : C<ε*(m+2 : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  have hs : (m+2 : ℝ) ≤ (m+2 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : C/(m+2 : ℝ)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    (hc.le.trans (mul_le_mul_of_nonneg_left hs hε.le))
  convert hb using 1
  dsimp [C]
  field_simp

/-- The true affine cutoff derivative pays both radial and vacuum terms on the actual varying source resolvent. -/
theorem actual_affine_cutoff_causal_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ∀ advanced : Bool, (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceRead F g (affineCutoff m ell)
          (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := actual_euler_causal_tail μ hμ g (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := vacuum_causal_contact_tail μ hμ (g : H) (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell] with F hE
  intro advanced
  have hE := hE advanced
  have hV := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell F advanced
  have he (w : ℝ) : sourceRead F g (affineCutoff m ell) (finiteResolvent F (causalFrequency advanced μ w) (g : H))=
      sourceRead F g (eulerAction m ell) (finiteResolvent F (causalFrequency advanced μ w) (g : H))+
        Complex.I • boundedContact ((vacuum : Scalar),0) m ell hell
          (finiteResolvent F (causalFrequency advanced μ w) (g : H)) := by
    have hz := causal_nonreal advanced μ w hμ
    have h := congrArg (fun A : SourceScalarGaugeScale.End => sourceRead F g A (finiteResolvent F (causalFrequency advanced μ w) (g : H)))
      (actual_affine_cutoff_return m ell)
    simp only [map_add,map_smul] at h
    have hc := source_read_resolvent F g (contactAction ((vacuum : Scalar),0) m ell) (causalFrequency advanced μ w) hz
    have hb := bounded_contact_core ((vacuum : Scalar),0) m ell hell
      (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (causalFrequency advanced μ w) hz g))
    have hv : embed (coreEquiv.symm (SourceEscapeCurrent.sourceCore F (causalFrequency advanced μ w) hz g))=
        finiteResolvent F (causalFrequency advanced μ w) (g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    rw [hv] at hb
    exact h.trans (congrArg (fun v : H =>
      sourceRead F g (eulerAction m ell) (finiteResolvent F (causalFrequency advanced μ w) (g : H))+Complex.I • v) (hc.trans hb.symm))
  have hmE : Measurable (fun w : ℝ => ENNReal.ofReal (‖sourceRead F g (eulerAction m ell)
      (finiteResolvent F (causalFrequency advanced μ w) (g : H))‖^2)) :=
    ((((sourceRead F g (eulerAction m ell)).continuous.comp
      ((causal_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal)
  simp_rw [he]
  have hs := (paid_affine_cutoff% two_energy)
    (fun w => sourceRead F g (eulerAction m ell) (finiteResolvent F (causalFrequency advanced μ w) (g : H)))
    (fun w => Complex.I • boundedContact ((vacuum : Scalar),0) m ell hell
      (finiteResolvent F (causalFrequency advanced μ w) (g : H))) hmE
  simp only [norm_smul,Complex.norm_I,one_mul] at hs
  apply hs.trans
  calc
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) :=
      mul_le_mul_of_nonneg_left (add_le_add hE hV) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
      congr 1
      ring


/-- The same actual core input is retained before applying the source affine derivative. -/
def causalCore (F : Index) (g : diagonal.domain) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) : QuantumTest :=
  coreEquiv.symm (SourceEscapeCurrent.sourceCore F (causalFrequency advanced μ w)
    (causal_nonreal advanced μ w hμ) g)

theorem actual_causal_core_embed (F : Index) (g : diagonal.domain) (advanced : Bool)
    (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    embed (causalCore F g advanced μ hμ w) =
      finiteResolvent F (causalFrequency advanced μ w) (g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- Both causal lines pay the actual core delta-Phi cutoff, including the vacuum contact. -/
theorem actual_affine_core_causal_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced : Bool,
        (∫⁻ w : ℝ, ENNReal.ofReal (‖embed
          (SourceScalarVirialBulk.deltaPhi (SourceNativeCutoffContact.thetaAction m ell)
            (causalCore F g advanced μ hμ w))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_affine_cutoff_causal_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  intro advanced
  have he (w : ℝ) : sourceRead F g (affineCutoff m ell)
      (finiteResolvent F (causalFrequency advanced μ w) (g : H)) =
      embed (SourceScalarVirialBulk.deltaPhi (SourceNativeCutoffContact.thetaAction m ell)
        (causalCore F g advanced μ hμ w)) :=
    actual_affine_source_read F g m ell _ (causal_nonreal advanced μ w hμ)
  have h := hF advanced
  simp_rw [he] at h
  exact h

end LowEnergy.ActualAffineCutoffCausalTail
