import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCubicCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaMixedEndpoint
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussDiagonalHistory
open GaussUnitaryHistory GaussHistoryHilbert SourceQuantumConfigurationHilbert
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceScalarPairedTransport
open SourceClockYukawaCubicCurrent SourceRelativePowerTail SourceRetardedForcingTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] state fullAction resolventCore thetaAction

private theorem starNonreal (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  change embed (state F z hz (coreEquiv f))=_
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem finite_adjoint (F : Index) (z : ℂ) :
    (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
  change star (finiteResolvent F z)=_
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←Ring.inverse_star,star_sub,star_smul,star_one,
    (GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem core_pair (F : Index) (z : ℂ) (hz : z.im≠0) (p q : QuantumTest) :
    sourcePair p (resolventCore F z hz q)=
      sourcePair (resolventCore F (star z) (starNonreal z hz) p) q := by
  simp only [sourcePair,core_embed]
  rw [←finite_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

private theorem full_pair (s : Bool) (p q : QuantumTest) :
    sourcePair p (fullAction s q)=sourcePair (fullAction (!s) p) q := by
  unfold SourceMixedNativeReturn.fullAction
  cases s
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

private theorem theta_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (thetaAction m ell q)=sourcePair (thetaAction m ell p) q := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact GaussNativeForm.multiply_pair _ _ _ _

def thetaGram (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  resolventCore F (star z) (starNonreal z hz)*(thetaAction m ell*thetaAction m ell)*resolventCore F z hz

def mixedEndpoint (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  sourceDerivative (!sharp) (sourceDerivative sharp (thetaGram m ell F z hz))

def thetaProfile (m ell : ℕ) (F : Index) (z : ℂ) (g : QuantumTest) : H :=
  relativeTail m ell (finiteResolvent F z (embed g))

def thetaPair (m ell : ℕ) (F : Index) (z : ℂ) (g h : QuantumTest) : ℂ :=
  inner ℂ (thetaProfile m ell F z g) (thetaProfile m ell F z h)

/-- Both legs of the positive original theta Gram are actual retarded source profiles. -/
theorem original_theta_gram_pair (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g h : QuantumTest) :
    sourcePair g (thetaGram m ell F z hz h)=thetaPair m ell F z g h := by
  change sourcePair g (resolventCore F (star z) (starNonreal z hz)
    (thetaAction m ell (thetaAction m ell (resolventCore F z hz h))))=_
  rw [core_pair]
  simp only [star_star]
  rw [theta_pair]
  change inner ℂ (embed (thetaAction m ell (resolventCore F z hz g)))
    (embed (thetaAction m ell (resolventCore F z hz h)))=_
  rw [←theta_core,←theta_core,core_embed,core_embed]
  rfl

private theorem pair_sub_right (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]

/-- Mixed derivatives keep both noncommuting Y orders and return only fixed source jets. -/
theorem original_mixed_endpoint_fixed_sources (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    sourcePair g (mixedEndpoint sharp m ell F z hz g)=
      thetaPair m ell F z g (fullAction sharp (fullAction (!sharp) g))-
      thetaPair m ell F z (fullAction (!sharp) g) (fullAction (!sharp) g)-
      thetaPair m ell F z (fullAction sharp g) (fullAction sharp g)+
      thetaPair m ell F z (fullAction (!sharp) (fullAction sharp g)) g := by
  simp only [mixedEndpoint,sourceDerivative,bracket,LinearMap.sub_apply,Module.End.mul_apply,
    map_sub,pair_sub_right,full_pair,Bool.not_not,original_theta_gram_pair]
  ring

private theorem inner_square_upper (p q : H) : ‖inner ℂ p q‖ ≤ ‖p‖^2+‖q‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) p q
  nlinarith only [h,sq_nonneg (‖p‖-‖q‖),sq_nonneg ‖p‖,sq_nonneg ‖q‖]

private theorem four_norm (a b c d : ℂ) : ‖a-b-c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  linarith only [norm_add_le (a-b-c) d,norm_sub_le (a-b) c,norm_sub_le a b]

private def profileEnergy (m ell : ℕ) (F : Index) (μ : ℝ) (g : QuantumTest) (w : ℝ) : ℝ :=
  ‖thetaProfile m ell F (line μ w) g‖^2

private theorem profile_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) :
    Measurable (fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g w)) := by
  have hc := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hp : Continuous (fun w : ℝ => thetaProfile m ell F (line μ w) g) :=
    (relativeTail m ell).continuous.comp (hc.clm_apply continuous_const)
  simpa only [profileEnergy,Pi.pow_apply] using ((hp.norm.pow 2).measurable.ennreal_ofReal)

private theorem profile_common_tail (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (profileEnergy m ell F μ g w)) ≤ ENNReal.ofReal ε := by
  have hg : (coreEquiv g:H)=embed g := rfl
  simpa only [profileEnergy,thetaProfile,hg] using actual_theta_full_frequency_tail μ hμ (coreEquiv g)

private theorem ofReal_five (a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    ENNReal.ofReal (2*(a+b+c+d+e))=
      2*(ENNReal.ofReal a+ENNReal.ofReal b+ENNReal.ofReal c+ENNReal.ofReal d+ENNReal.ofReal e) := by
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg ha hb) hc) hd) he,
    ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) hc) hd,
    ENNReal.ofReal_add (add_nonneg ha hb) hc,ENNReal.ofReal_add ha hb,
    ENNReal.ofReal_ofNat]

private theorem endpoint_profile_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) (w : ℝ) :
    ‖sourcePair g (mixedEndpoint sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖ ≤
      2*(profileEnergy m ell F μ g w+
        profileEnergy m ell F μ (fullAction (!sharp) g) w+
        profileEnergy m ell F μ (fullAction sharp g) w+
        profileEnergy m ell F μ (fullAction sharp (fullAction (!sharp) g)) w+
        profileEnergy m ell F μ (fullAction (!sharp) (fullAction sharp g)) w) := by
  rw [original_mixed_endpoint_fixed_sources]
  apply (four_norm _ _ _ _).trans
  have h0 := inner_square_upper (thetaProfile m ell F (line μ w) g)
    (thetaProfile m ell F (line μ w) (fullAction sharp (fullAction (!sharp) g)))
  have h1 := inner_square_upper (thetaProfile m ell F (line μ w) (fullAction (!sharp) g))
    (thetaProfile m ell F (line μ w) (fullAction (!sharp) g))
  have h2 := inner_square_upper (thetaProfile m ell F (line μ w) (fullAction sharp g))
    (thetaProfile m ell F (line μ w) (fullAction sharp g))
  have h3 := inner_square_upper
    (thetaProfile m ell F (line μ w) (fullAction (!sharp) (fullAction sharp g)))
    (thetaProfile m ell F (line μ w) g)
  change ‖inner ℂ _ _‖+‖inner ℂ _ _‖+‖inner ℂ _ _‖+‖inner ℂ _ _‖ ≤ _
  dsimp only [profileEnergy]
  nlinarith only [h0,h1,h2,h3,
    sq_nonneg ‖thetaProfile m ell F (line μ w) (fullAction sharp (fullAction (!sharp) g))‖,
    sq_nonneg ‖thetaProfile m ell F (line μ w) (fullAction (!sharp) (fullAction sharp g))‖]

/-- The complete mixed endpoint has a source-paid absolute L1 tail on a common
cutoff; both mixed fixed-Y orders and the original cofinal F remain intact. -/
theorem actual_mixed_endpoint_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖sourcePair g
          (mixedEndpoint sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)‖)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let g1 := fullAction (!sharp) g
  let g2 := fullAction sharp g
  let g3 := fullAction sharp g1
  let g4 := fullAction (!sharp) g2
  obtain ⟨N0,h0⟩ := profile_common_tail μ hμ g (ε/10) (by positivity)
  obtain ⟨N1,h1⟩ := profile_common_tail μ hμ g1 (ε/10) (by positivity)
  obtain ⟨N2,h2⟩ := profile_common_tail μ hμ g2 (ε/10) (by positivity)
  obtain ⟨N3,h3⟩ := profile_common_tail μ hμ g3 (ε/10) (by positivity)
  obtain ⟨N4,h4⟩ := profile_common_tail μ hμ g4 (ε/10) (by positivity)
  refine ⟨max (max N0 N1) (max N2 (max N3 N4)),fun m hm ell hell => ?_⟩
  filter_upwards [h0 m (by omega) ell hell,h1 m (by omega) ell hell,h2 m (by omega) ell hell,
    h3 m (by omega) ell hell,h4 m (by omega) ell hell] with F hF0 hF1 hF2 hF3 hF4
  let p0 := fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g w)
  let p1 := fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g1 w)
  let p2 := fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g2 w)
  let p3 := fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g3 w)
  let p4 := fun w : ℝ => ENNReal.ofReal (profileEnergy m ell F μ g4 w)
  have hm0 : Measurable p0 := profile_measurable m ell F μ hμ g
  have hm1 : Measurable p1 := profile_measurable m ell F μ hμ g1
  have hm2 : Measurable p2 := profile_measurable m ell F μ hμ g2
  have hm3 : Measurable p3 := profile_measurable m ell F μ hμ g3
  have hint : (∫⁻ w : ℝ,2*(p0 w+p1 w+p2 w+p3 w+p4 w))=
      2*((∫⁻ w : ℝ,p0 w)+(∫⁻ w : ℝ,p1 w)+(∫⁻ w : ℝ,p2 w)+
        (∫⁻ w : ℝ,p3 w)+(∫⁻ w : ℝ,p4 w)) := by
    have hm01 : Measurable (fun w : ℝ => p0 w+p1 w) := hm0.add hm1
    have hm012 : Measurable (fun w : ℝ => p0 w+p1 w+p2 w) := hm01.add hm2
    have hm0123 : Measurable (fun w : ℝ => p0 w+p1 w+p2 w+p3 w) := hm012.add hm3
    rw [lintegral_const_mul' 2 _ (by norm_num),lintegral_add_left hm0123 p4,
      lintegral_add_left hm012 p3,lintegral_add_left hm01 p2,lintegral_add_left hm0 p1]
  calc
    _ ≤ ∫⁻ w : ℝ,2*(p0 w+p1 w+p2 w+p3 w+p4 w) := by
      apply lintegral_mono
      intro w
      dsimp only
      have hn0 : 0 ≤ profileEnergy m ell F μ g w := sq_nonneg _
      have hn1 : 0 ≤ profileEnergy m ell F μ (fullAction (!sharp) g) w := sq_nonneg _
      have hn2 : 0 ≤ profileEnergy m ell F μ (fullAction sharp g) w := sq_nonneg _
      have hn3 : 0 ≤ profileEnergy m ell F μ (fullAction sharp (fullAction (!sharp) g)) w := sq_nonneg _
      have hn4 : 0 ≤ profileEnergy m ell F μ (fullAction (!sharp) (fullAction sharp g)) w := sq_nonneg _
      have h := ENNReal.ofReal_le_ofReal (endpoint_profile_upper sharp m ell F μ hμ g w)
      rw [ofReal_five _ _ _ _ _ hn0 hn1 hn2 hn3 hn4] at h
      simpa only [p0,p1,p2,p3,p4,g1,g2,g3,g4] using h
    _ = _ := hint
    _ ≤ 2*(ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10)+
        ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10)) :=
      mul_le_mul (le_refl _) (add_le_add (add_le_add (add_le_add (add_le_add hF0 hF1) hF2) hF3) hF4) bot_le bot_le
    _ = ENNReal.ofReal ε := by
      have h : (2:ENNReal)*(ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10)+
          ENNReal.ofReal (ε/10)+ENNReal.ofReal (ε/10))=10*ENNReal.ofReal (ε/10) := by ring
      rw [h,←ENNReal.ofReal_ofNat (n := 10),←ENNReal.ofReal_mul (by norm_num : 0 ≤ (10:ℝ))]
      congr 1
      ring

end LowEnergy.SourceClockYukawaMixedEndpoint
