import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaCubicCurrent
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceBoundedInsertionTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaCubicBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceClockYukawaCubicCurrent SourceClockYukawaHamiltonianCurrent SourceScalarPositiveBulkWard
open SourceScalarPairedTransport GaussNativePotential
open SourceBoundedInsertionResponse SourceBoundedInsertionTail SourceRelativePowerTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRetardedBandCurrent MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] state fullAction compressionCore defectAction thetaAction resolventCore correctedCurrent correctedCurvature

def firstResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz;
  -(R*correctedCurrent sharp F*R)

def secondResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz;
  let D := correctedCurrent sharp F
  2*(R*D*R*D*R)-R*correctedCurvature sharp F*R

def thirdResponse (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz;
  let D := correctedCurrent sharp F
  let E := correctedCurvature sharp F;
  -6*(R*D*R*D*R*D*R)+3*(R*E*R*D*R)+3*(R*D*R*E*R)+R*defectThird sharp F*R

/-- The complete cubic current/curvature/defect word at the original theta insertion. -/
def cubicInsertion (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  let R := resolventCore F z hz;
  let T := thetaAction m ell
  thirdResponse sharp F z hz*T*R+3*(secondResponse sharp F z hz*T*firstResponse sharp F z hz)+
    3*(firstResponse sharp F z hz*T*secondResponse sharp F z hz)+R*T*thirdResponse sharp F z hz

private theorem derivative_mul (s : Bool) (A B : End) :
    sourceDerivative s (A*B)=sourceDerivative s A*B+A*sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring
private theorem derivative_add (s : Bool) (A B : End) :
    sourceDerivative s (A+B)=sourceDerivative s A+sourceDerivative s B := by
  unfold sourceDerivative bracket
  noncomm_ring
private theorem derivative_neg (s : Bool) (A : End) :
    sourceDerivative s (-A)= -sourceDerivative s A := by
  unfold sourceDerivative bracket
  noncomm_ring
private theorem derivative_zero (s : Bool) : sourceDerivative s (0:End)=0 := by
  simp only [sourceDerivative,bracket,zero_mul,mul_zero,sub_self]

private theorem derivative_theta (s : Bool) (m ell : ℕ) : sourceDerivative s (thetaAction m ell)=0 := by
  apply sub_eq_zero.mpr
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases s
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z))
      (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)).symm

private theorem actual_second (s : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) :
    sourceDerivative s (sourceDerivative s (resolventCore F z hz))=secondResponse s F z hz := by
  rw [actual_resolvent_first_source]
  simp only [derivative_neg,derivative_mul,actual_resolvent_first_source]
  unfold secondResponse correctedCurvature
  noncomm_ring

private theorem actual_third (s : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) :
    sourceDerivative s (sourceDerivative s (sourceDerivative s (resolventCore F z hz)))=
      thirdResponse s F z hz := actual_resolvent_third_source s F z hz

private theorem sandwich_third (s : Bool) (R T : End) (hT : sourceDerivative s T=0) :
    sourceDerivative s (sourceDerivative s (sourceDerivative s (R*T*R)))=
      sourceDerivative s (sourceDerivative s (sourceDerivative s R))*T*R+
      3*(sourceDerivative s (sourceDerivative s R)*T*sourceDerivative s R)+
      3*(sourceDerivative s R*T*sourceDerivative s (sourceDerivative s R))+
      R*T*sourceDerivative s (sourceDerivative s (sourceDerivative s R)) := by
  simp only [derivative_mul,derivative_add,hT,mul_zero,add_zero]
  noncomm_ring

/-- The literal cubic source closure is consumed at the original two-resolvent theta word. -/
theorem actual_cubic_insertion (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) :
    cubicInsertion sharp m ell F z hz=
      sourceDerivative sharp (sourceDerivative sharp (sourceDerivative sharp
        (resolventCore F z hz*thetaAction m ell*resolventCore F z hz))) := by
  rw [sandwich_third sharp _ _ (derivative_theta sharp m ell)]
  simp only [actual_third]
  simp only [actual_second]
  simp only [actual_resolvent_first_source,cubicInsertion,firstResponse]

private theorem full_pair (s : Bool) (p q : QuantumTest) :
    sourcePair p (fullAction s q)=sourcePair (fullAction (!s) p) q := by
  unfold SourceMixedNativeReturn.fullAction
  cases s
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

private theorem pair_sub_right (p q r : QuantumTest) :
    sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem cubic_pair (s : Bool) (A : End) (p q : QuantumTest) :
    sourcePair p (sourceDerivative s (sourceDerivative s (sourceDerivative s A)) q)=
      sourcePair p (A (fullAction s (fullAction s (fullAction s q))))-
      3*sourcePair (fullAction (!s) p) (A (fullAction s (fullAction s q)))+
      3*sourcePair (fullAction (!s) (fullAction (!s) p)) (A (fullAction s q))-
      sourcePair (fullAction (!s) (fullAction (!s) (fullAction (!s) p))) (A q) := by
  simp only [sourceDerivative,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,
    pair_sub_right,full_pair]
  ring

private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  change embed (state F z hz (coreEquiv f))=_
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

def seedAmplitude (m ell : ℕ) (F : Index) (μ : ℝ) (g k : QuantumTest) (w : ℝ) : ℂ :=
  amplitude F μ (relativeTail m ell) (embed g) (embed k) w

def cubicAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) (w : ℝ) : ℂ :=
  sourcePair k (cubicInsertion sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)

private theorem sandwich_pair (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) (w : ℝ) :
    sourcePair k ((resolventCore F (line μ w) (by simpa only [line_im] using hμ.ne')*
      thetaAction m ell*resolventCore F (line μ w) (by simpa only [line_im] using hμ.ne')) g)=
      seedAmplitude m ell F μ g k w := by
  simp only [sourcePair,Module.End.mul_apply,core_embed,←theta_core,seedAmplitude,amplitude]

/-- All four endpoint jets are fixed original sources, and the internal response
retains the whole cubic native/curvature/compression word. -/
theorem actual_cubic_fixed_sources (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) (w : ℝ) :
    cubicAmplitude sharp m ell F μ hμ g k w=
      seedAmplitude m ell F μ (fullAction sharp (fullAction sharp (fullAction sharp g))) k w-
      3*seedAmplitude m ell F μ (fullAction sharp (fullAction sharp g)) (fullAction (!sharp) k) w+
      3*seedAmplitude m ell F μ (fullAction sharp g) (fullAction (!sharp) (fullAction (!sharp) k)) w-
      seedAmplitude m ell F μ g (fullAction (!sharp) (fullAction (!sharp) (fullAction (!sharp) k))) w := by
  rw [cubicAmplitude,actual_cubic_insertion,cubic_pair]
  simp only [sandwich_pair m ell F μ hμ]

private theorem seed_continuous (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) : Continuous (seedAmplitude m ell F μ g k) := by
  have hc := finite_frequency_continuous μ hμ F
  exact continuous_const.inner (hc.clm_apply
    ((relativeTail m ell).continuous.comp (hc.clm_apply continuous_const)))

private theorem seed_energy_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) : Measurable (fun w : ℝ => ENNReal.ofReal (‖seedAmplitude m ell F μ g k w‖^2)) :=
  ((seed_continuous m ell F μ hμ g k).norm.pow 2).measurable.ennreal_ofReal

private theorem seed_square_bound (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : QuantumTest) (w : ℝ) :
    ‖seedAmplitude m ell F μ g k w‖^2 ≤ ((1/μ)*‖embed k‖)^2*
      ‖relativeTail m ell (finiteResolvent F (line μ w) (embed g))‖^2 := by
  have hr (v : H) : ‖finiteResolvent F (line μ w) v‖ ≤ (1/μ)*‖v‖ := by
    apply ((finiteResolvent F _).le_opNorm v).trans
    have hb := finite_resolvent_norm F (line μ w) (by simpa only [line_im] using hμ.ne')
    rw [line_im,abs_of_pos hμ] at hb
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h := (norm_inner_le_norm (𝕜 := ℂ) (embed k)
    (finiteResolvent F (line μ w) (relativeTail m ell (finiteResolvent F (line μ w) (embed g))))).trans
      (mul_le_mul_of_nonneg_left (hr _) (norm_nonneg _))
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc
    _ ≤ (‖embed k‖*((1/μ)*‖relativeTail m ell (finiteResolvent F (line μ w) (embed g))‖))^2 := hh
    _ = _ := by ring

private theorem seed_tail (μ : ℝ) (hμ : 0<μ) (g k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖seedAmplitude m ell F μ g k w‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ((1/μ)*‖embed k‖)^2
  have hC : 0 ≤ C := sq_nonneg _
  obtain ⟨N,hN⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ (coreEquiv g)
    (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (embed g))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (seed_square_bound m ell F μ hμ g k w)
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,
        ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (embed g))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := mul_le_mul (le_refl _) hF bot_le bot_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hp : 0<C+1 := by positivity
      exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) (div_pos hε hp).le).trans_eq
        (mul_div_cancel₀ ε hp.ne')

private theorem four_square (a b c d : ℂ) :
    ‖a-3*b+3*c-d‖^2 ≤ 4*‖a‖^2+36*‖b‖^2+36*‖c‖^2+4*‖d‖^2 := by
  have hn := (norm_sub_le (a-3*b+3*c) d).trans
    (add_le_add ((norm_add_le (a-3*b) (3*c)).trans
      (add_le_add (norm_sub_le a (3*b)) (le_refl _))) (le_refl _))
  norm_num [norm_mul] at hn
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [hh,sq_nonneg (‖a‖-3*‖b‖),sq_nonneg (‖a‖-3*‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (3*‖b‖-3*‖c‖),sq_nonneg (3*‖b‖-‖d‖),sq_nonneg (3*‖c‖-‖d‖)]

/-- The complete cubic response has an internally paid common-cutoff, full-frequency source tail. -/
theorem actual_cubic_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖cubicAmplitude sharp m ell F μ hμ g k w‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let g1 := fullAction sharp g
  let g2 := fullAction sharp g1
  let g3 := fullAction sharp g2
  let k1 := fullAction (!sharp) k
  let k2 := fullAction (!sharp) k1
  let k3 := fullAction (!sharp) k2
  obtain ⟨N0,h0⟩ := seed_tail μ hμ g3 k (ε/80) (by positivity)
  obtain ⟨N1,h1⟩ := seed_tail μ hμ g2 k1 (ε/80) (by positivity)
  obtain ⟨N2,h2⟩ := seed_tail μ hμ g1 k2 (ε/80) (by positivity)
  obtain ⟨N3,h3⟩ := seed_tail μ hμ g k3 (ε/80) (by positivity)
  refine ⟨max (max N0 N1) (max N2 N3),fun m hm ell hell => ?_⟩
  filter_upwards [h0 m (by omega) ell hell,h1 m (by omega) ell hell,
    h2 m (by omega) ell hell,h3 m (by omega) ell hell] with F hF0 hF1 hF2 hF3
  let p0 := fun w : ℝ => ENNReal.ofReal (‖seedAmplitude m ell F μ g3 k w‖^2)
  let p1 := fun w : ℝ => ENNReal.ofReal (‖seedAmplitude m ell F μ g2 k1 w‖^2)
  let p2 := fun w : ℝ => ENNReal.ofReal (‖seedAmplitude m ell F μ g1 k2 w‖^2)
  let p3 := fun w : ℝ => ENNReal.ofReal (‖seedAmplitude m ell F μ g k3 w‖^2)
  have hm0 : Measurable p0 := seed_energy_measurable m ell F μ hμ g3 k
  have hm1 : Measurable p1 := seed_energy_measurable m ell F μ hμ g2 k1
  have hm2 : Measurable p2 := seed_energy_measurable m ell F μ hμ g1 k2
  have hint : (∫⁻ w : ℝ,4*p0 w+36*p1 w+36*p2 w+4*p3 w)=
      4*(∫⁻ w : ℝ,p0 w)+36*(∫⁻ w : ℝ,p1 w)+36*(∫⁻ w : ℝ,p2 w)+4*(∫⁻ w : ℝ,p3 w) := by
    have hm01 : Measurable (fun w : ℝ => 4*p0 w+36*p1 w) :=
      (measurable_const.mul hm0).add (measurable_const.mul hm1)
    have hm012 : Measurable (fun w : ℝ => 4*p0 w+36*p1 w+36*p2 w) :=
      hm01.add (measurable_const.mul hm2)
    have hm00 : Measurable (fun w : ℝ => 4*p0 w) := measurable_const.mul hm0
    rw [lintegral_add_left hm012 (fun w => 4*p3 w),lintegral_add_left hm01 (fun w => 36*p2 w),
      lintegral_add_left hm00 (fun w => 36*p1 w)]
    rw [lintegral_const_mul' 4 p0 (by norm_num),lintegral_const_mul' 36 p1 (by norm_num),
      lintegral_const_mul' 36 p2 (by norm_num),lintegral_const_mul' 4 p3 (by norm_num)]
  calc
    _ ≤ ∫⁻ w : ℝ,4*p0 w+36*p1 w+36*p2 w+4*p3 w := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [actual_cubic_fixed_sources]
      have h := ENNReal.ofReal_le_ofReal (four_square
        (seedAmplitude m ell F μ g3 k w) (seedAmplitude m ell F μ g2 k1 w)
        (seedAmplitude m ell F μ g1 k2 w) (seedAmplitude m ell F μ g k3 w))
      rw [ENNReal.ofReal_add (by positivity : 0 ≤ 4*‖seedAmplitude m ell F μ g3 k w‖^2+
        36*‖seedAmplitude m ell F μ g2 k1 w‖^2+36*‖seedAmplitude m ell F μ g1 k2 w‖^2) (by positivity),
        ENNReal.ofReal_add (by positivity : 0 ≤ 4*‖seedAmplitude m ell F μ g3 k w‖^2+
          36*‖seedAmplitude m ell F μ g2 k1 w‖^2) (by positivity),
        ENNReal.ofReal_add (by positivity : 0 ≤ 4*‖seedAmplitude m ell F μ g3 k w‖^2) (by positivity),
        ENNReal.ofReal_mul (by norm_num : 0 ≤ (4:ℝ)),ENNReal.ofReal_mul (by norm_num : 0 ≤ (36:ℝ)),
        ENNReal.ofReal_mul (by norm_num : 0 ≤ (4:ℝ)),ENNReal.ofReal_mul (by norm_num : 0 ≤ (36:ℝ)),
        ENNReal.ofReal_ofNat,ENNReal.ofReal_ofNat] at h
      simpa only [p0,p1,p2,p3,g1,g2,g3,k1,k2,k3] using h
    _ = _ := hint
    _ ≤ 4*ENNReal.ofReal (ε/80)+36*ENNReal.ofReal (ε/80)+36*ENNReal.ofReal (ε/80)+4*ENNReal.ofReal (ε/80) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul (le_refl _) hF0 bot_le bot_le) (mul_le_mul (le_refl _) hF1 bot_le bot_le))
        (mul_le_mul (le_refl _) hF2 bot_le bot_le)) (mul_le_mul (le_refl _) hF3 bot_le bot_le)
    _ = ENNReal.ofReal ε := by
      have h : (4:ENNReal)*ENNReal.ofReal (ε/80)+36*ENNReal.ofReal (ε/80)+
          36*ENNReal.ofReal (ε/80)+4*ENNReal.ofReal (ε/80)=80*ENNReal.ofReal (ε/80) := by ring
      rw [h,←ENNReal.ofReal_ofNat (n := 80),←ENNReal.ofReal_mul (by norm_num : 0 ≤ (80:ℝ))]
      congr 1
      ring

end LowEnergy.SourceClockYukawaCubicBudget
