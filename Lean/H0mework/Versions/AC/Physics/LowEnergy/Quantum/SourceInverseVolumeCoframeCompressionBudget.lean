import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeNeutralBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCoframeCompressionBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular SourceEscapeCurrent
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseProjectionCurrentRemainder SourceInverseGaugeSingleDefectJoin
open SourceInverseCompressionGaugeBudget SourceInverseHamiltonianForceReduction
open SourceHamiltonianScaleJet SourceInverseCoframeNeutralBudget
open SourceScalarGaugeScale MeasureTheory Filter SourceResolventBandLimit
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead state sourcePair defectAction compressionCore
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent singleDefect projectionCurrent doubleProjectionFlux deltaGauge
  matterInsertion matterHamiltonianCurrent readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  wholeCurrent wholeResponse firstRetardedCurrent

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem map_sandwich {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a : R) : e r*(e a*e r)=e (r*a*r) := by
  simp only [map_mul,mul_assoc]

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (s : ℝ) :
    sandwichJet F g z A 0 0 s 0=(mixedHilbert s 0).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 s 0*(readOrbitJet F g A 0 0 s 0*resolventJet F z 0 0 s 0)=_
  exact (congrArg₂ (fun r a : Op => r*(a*r))
    (actual_mixed_resolvent F z hz s 0) (actual_read_orbit F g A s 0)).trans
      (map_sandwich _ _ _)

private theorem inverse_flow_core (s : ℝ) (f : QuantumTest) :
    (mixedHilbert s 0).symm (embed f)=embed (coframeFlow (-s) f) := by
  apply (mixedHilbert s 0).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,
    SourceGaugeScaleTransport.hilbertFlow_zero,SourceCoframeScaleTransport.hilbertFlow_on_core,
    coframeFlow]
  rw [SourceCoframeScaleTransport.coreFlow_add]
  have he : (3/2 : ℝ)*s+(3/2 : ℝ)*(-s)=0 := by ring
  rw [he,SourceCoframeScaleTransport.coreFlow_zero]

private theorem orbit_pair (B : Op) (s : ℝ) (g k : QuantumTest) :
    inner ℂ (embed k) ((mixedHilbert s 0).conjStarAlgEquiv B (embed g))=
      inner ℂ (embed (coframeFlow (-s) k)) (B (embed (coframeFlow (-s) g))) := by
  have h := (mixedHilbert s 0).inner_map_map ((mixedHilbert s 0).symm (embed k))
    (B ((mixedHilbert s 0).symm (embed g)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℂ (embed k) ((mixedHilbert s 0).conjStarAlgEquiv B (embed g))=_ at h
  simpa only [inverse_flow_core] using h

private theorem negative_flow (f : QuantumTest) (s : ℝ) :
    HasDerivAt (fun r : ℝ => embed (coframeFlow (-r) f))
      (-embed (coframeFlow (-s) (K f))) s := by
  have h := test_coframe_derivative 0 0 f (-s) 0
  have he : (fun r => testJet 0 0 f r 0)=(fun r => embed (coframeFlow r f)) := by
    funext r
    simp only [testJet,sourceTest,pow_zero,Module.End.one_apply,
      SourceGaugeScaleTransport.hilbertFlow_zero]
  rw [he] at h
  have hd : testJet (0+1) 0 f (-s) 0=embed (coframeFlow (-s) (K f)) := by
    simp only [testJet,sourceTest,pow_zero,pow_one,Module.End.one_apply,Nat.zero_add,
      SourceGaugeScaleTransport.hilbertFlow_zero]
  rw [hd] at h
  simpa only [neg_smul,one_smul] using! h.scomp s ((hasDerivAt_id s).neg)

private theorem pullback_derivative (B : Op) (g k : QuantumTest) (s : ℝ) :
    HasDerivAt (fun r : ℝ => inner ℂ (embed (coframeFlow (-r) k))
      (B (embed (coframeFlow (-r) g))))
      (-inner ℂ (embed (coframeFlow (-s) k)) (B (embed (coframeFlow (-s) (K g))))-
      inner ℂ (embed (coframeFlow (-s) (K k))) (B (embed (coframeFlow (-s) g)))) s := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (negative_flow g s)
  have h := (negative_flow k s).inner ℂ hg
  simp only [map_neg,inner_neg_left,inner_neg_right] at h
  exact h.congr_deriv (by abel)

private def weakJet (J : ℕ → ℝ → Op) (g k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (J n t (embed g))

set_option backward.isDefEq.respectTransparency.types false in
private theorem weak_derivative (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t) (g k : QuantumTest) (n : ℕ) (t : ℝ) :
    HasDerivAt (weakJet J g k n) (weakJet J g k (n+1) t) t := by
  have hA : HasDerivAt (fun s => J n s (embed g)) (J (n+1) t (embed g)) t :=
    ((ContinuousLinearMap.apply ℂ H (embed g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hJ n t)
  have h := (hasDerivAt_const t (embed k)).inner ℂ hA
  simpa only [inner_zero_left,zero_add,add_zero,weakJet] using! h

private theorem weak_first (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0))
    (g k : QuantumTest) (t : ℝ) :
    weakJet J g k 1 t= -weakJet J (K g) k 0 t-weakJet J g (K k) 0 t := by
  have ho (f h : QuantumTest) (s : ℝ) : weakJet J f h 0 s=
      inner ℂ (embed (coframeFlow (-s) h))
        (J 0 0 (embed (coframeFlow (-s) f))) := by
    rw [weakJet,hO]
    exact orbit_pair _ s f h
  have h := (pullback_derivative (J 0 0) g k t).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (ho g k))
  have hu := (weak_derivative J hJ g k 0 t).unique h
  rw [ho (K g) k,ho g (K k)]
  exact hu

private theorem weak_next (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0))
    (n : ℕ) (g k : QuantumTest) (t : ℝ) :
    weakJet J g k (n+1) t= -weakJet J (K g) k n t-weakJet J g (K k) n t := by
  induction n generalizing g k t with
  | zero => exact weak_first J hJ hO g k t
  | succ n ih =>
    have hd := (weak_derivative J hJ (K g) k n t).neg.sub (weak_derivative J hJ g (K k) n t)
    exact (weak_derivative J hJ g k (n+1) t).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (ih g k)))

def coframeProfile (F : Index) (seed : diagonal.domain) (z : ℂ) (A : End)
    (f k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (sandwichJet F seed z A n 0 t 0 (embed f))

private theorem profile_next (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End)
    (f k : QuantumTest) (n : ℕ) (t : ℝ) :
    coframeProfile F seed z A f k (n+1) t=
      -coframeProfile F seed z A (K f) k n t-coframeProfile F seed z A f (K k) n t := by
  let J := fun n t => sandwichJet F seed z A n 0 t 0
  have hO (t : ℝ) : J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0) := by
    have ho := (sandwich_orbit F seed z hz A 0).trans (origin_conjugate _)
    exact (sandwich_orbit F seed z hz A t).trans (congrArg (mixedHilbert t 0).conjStarAlgEquiv ho.symm)
  exact weak_next J (fun n t => sandwich_coframe_derivative F seed z A n 0 t 0) hO n f k t

private theorem profile_origin (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A : End) (f k : QuantumTest) :
    coframeProfile F seed z A f k 0 0=
      inner ℂ (embed k) ((finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) (embed f)) :=
  congrArg (fun B : Op => inner ℂ (embed k) (B (embed f)))
    ((sandwich_orbit F seed z hz A 0).trans (origin_conjugate _))

private theorem profile_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => coframeProfile F seed (line μ w) A f k n 0) := by
  induction n generalizing f k with
  | zero =>
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    have hc : Continuous (fun w : ℝ => inner ℂ (embed k)
        (finiteResolvent F (line μ w) (sourceRead F seed A (finiteResolvent F (line μ w) (embed f))))) :=
      continuous_const.inner (hr.clm_apply ((sourceRead F seed A).continuous.comp (hr.clm_apply continuous_const)))
    exact hc.congr (fun w => (profile_origin F seed (line μ w)
      (by simpa only [line_im] using hμ.ne') A f k).symm)
  | succ n ih =>
    exact ((ih (K f) k).neg.sub (ih f (K k))).congr (fun w =>
      (profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne') A f k n 0).symm)

private def Tail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))≤ENNReal.ofReal ε

private theorem tail_neg (f : ℕ → ℕ → Index → ℝ → ℂ) (hf : Tail f) :
    Tail (fun m ell F w => -f m ell F w) := by simpa only [Tail,norm_neg] using hf

private theorem tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : Tail f) (hg : Tail g) :
    Tail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell] with F hl hr
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem tail_congr (f h : ℕ → ℕ → Index → ℝ → ℂ)
    (he : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),∀ w,f m ell F w=h m ell F w)
    (hh : Tail h) : Tail f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,he m ell] with F hF hEq
  simpa only [hEq] using hF

private theorem all_coframe_tails (A : ℕ → ℕ → Index → End) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (hbase : ∀ f k : QuantumTest,Tail (fun m ell F w => coframeProfile F seed (line μ w) (A m ell F) f k 0 0))
    (n : ℕ) (f k : QuantumTest) :
    Tail (fun m ell F w => coframeProfile F seed (line μ w) (A m ell F) f k n 0) := by
  induction n generalizing f k with
  | zero => exact hbase f k
  | succ n ih =>
    have htail := tail_add _ _
      (fun m ell F => (profile_continuous F seed (A m ell F) μ hμ n (K f) k).neg)
      (tail_neg _ (ih (K f) k)) (tail_neg _ (ih f (K k)))
    apply tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => ?_)) htail
    rw [profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne')]
    simp only [Pi.neg_apply,sub_eq_add_neg]

/-- Fixed finite coframe jets retain the original double-current payer and source filter. -/
theorem actual_first_compression_coframe_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeProfile F seed (line μ w)
          (compressionFirst sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε := by
  apply all_coframe_tails (compressionFirst sharp) seed μ hμ _ n f k
  intro f k
  exact actual_first_compression_gauge_tail sharp seed μ hμ 0 f k

/-- The already generated whole first-current payer supplies every fixed finite coframe jet. -/
theorem actual_matter_compression_coframe_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeProfile F seed (line μ w)
          (compressionMatter sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε := by
  apply all_coframe_tails (compressionMatter sharp) seed μ hμ _ n f k
  intro f k
  exact actual_matter_compression_gauge_tail sharp seed μ hμ 0 f k

def compressionNeutral (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (compressionCore F) (neutralCurrent sharp m ell)

attribute [local irreducible] compressionNeutral neutralCurrent

private theorem neutral_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    compressionNeutral sharp m ell F=compressionFirst sharp m ell F-compressionMatter sharp m ell F := by
  unfold compressionNeutral neutralCurrent compressionFirst compressionMatter bracket
  noncomm_ring

private theorem sandwich_sub (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A B : End) (n : ℕ) (s : ℝ) :
    sandwichJet F seed z (A-B) n 0 s 0=sandwichJet F seed z A n 0 s 0-sandwichJet F seed z B n 0 s 0 := by
  induction n generalizing s with
  | zero =>
    have hr := sandwich_orbit F seed z hz (A-B) s
    have hm : sourceRead F seed (A-B)=sourceRead F seed A-sourceRead F seed B := map_sub (sourceRead F seed) A B
    have he := congrArg (fun a : Op => (mixedHilbert s 0).conjStarAlgEquiv
      (finiteResolvent F z*a*finiteResolvent F z)) hm
    have ho := congrArg₂ (fun a b : Op => a-b) (sandwich_orbit F seed z hz A s) (sandwich_orbit F seed z hz B s)
    have hh : (mixedHilbert s 0).conjStarAlgEquiv
        (finiteResolvent F z*(sourceRead F seed A-sourceRead F seed B)*finiteResolvent F z)=
      (mixedHilbert s 0).conjStarAlgEquiv (finiteResolvent F z*sourceRead F seed A*finiteResolvent F z)-
      (mixedHilbert s 0).conjStarAlgEquiv (finiteResolvent F z*sourceRead F seed B*finiteResolvent F z) := by
      simp only [mul_sub,sub_mul,map_sub]
    exact hr.trans (he.trans (hh.trans ho.symm))
  | succ n ih =>
    have hd := (sandwich_coframe_derivative F seed z A n 0 s 0).sub
      (sandwich_coframe_derivative F seed z B n 0 s 0)
    exact (sandwich_coframe_derivative F seed z (A-B) n 0 s 0).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih))

private theorem neutral_profile_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (n : ℕ) (s : ℝ) (f k : QuantumTest) :
    coframeProfile F seed z (compressionNeutral sharp m ell F) f k n s=
      coframeProfile F seed z (compressionFirst sharp m ell F) f k n s-
      coframeProfile F seed z (compressionMatter sharp m ell F) f k n s := by
  rw [coframeProfile,neutral_split,sandwich_sub F seed z hz]
  simp only [sub_apply,inner_sub_right,coframeProfile]

/-- The full neutral current Q=B−W inherits every finite coframe jet from the two actual payers. -/
theorem actual_neutral_compression_coframe_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeProfile F seed (line μ w)
          (compressionNeutral sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε := by
  have ht := tail_add _ _
    (fun m ell F => profile_continuous F seed (compressionFirst sharp m ell F) μ hμ n f k)
    (actual_first_compression_coframe_tail sharp seed μ hμ n f k)
    (tail_neg _ (actual_matter_compression_coframe_tail sharp seed μ hμ n f k))
  apply tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => ?_)) ht
  rw [neutral_profile_split sharp m ell F seed (line μ w) (by simpa only [line_im] using hμ.ne')]
  simp only [sub_eq_add_neg]

/-- Complete coframe correction dictated by the actual −3 weight of Q. -/
def correctedCoframeCompressionJet (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (n : ℕ) (s : ℝ) : Op :=
  sandwichJet F seed z (compressionNeutral sharp m ell F) (n+1) 0 s 0+
    (3 : ℂ) • sandwichJet F seed z (compressionNeutral sharp m ell F) n 0 s 0

private theorem corrected_profile (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (n : ℕ) (s : ℝ) (f k : QuantumTest) :
    inner ℂ (embed k) (correctedCoframeCompressionJet sharp m ell F seed z n s (embed f))=
      coframeProfile F seed z (compressionNeutral sharp m ell F) f k (n+1) s+
      coframeProfile F seed z (compressionNeutral sharp m ell F) ((3 : ℂ) • f) k n s := by
  simp only [correctedCoframeCompressionJet,coframeProfile,add_apply,smul_apply,
    inner_add_right,inner_smul_right,map_smul]

/-- Every fixed coframe jet of the complete correction has the original common full-frequency tail. -/
theorem actual_corrected_coframe_compression_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (correctedCoframeCompressionJet sharp m ell F seed (line μ w) n 0 (embed f))‖^2))≤ENNReal.ofReal ε := by
  have ht := tail_add _ _
    (fun m ell F => profile_continuous F seed (compressionNeutral sharp m ell F) μ hμ (n+1) f k)
    (actual_neutral_compression_coframe_tail sharp seed μ hμ (n+1) f k)
    (actual_neutral_compression_coframe_tail sharp seed μ hμ n ((3 : ℂ) • f) k)
  exact tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w =>
    corrected_profile sharp m ell F seed (line μ w) n 0 f k)) ht

/-- The actual CF force uses the same scaleDerivative coordinate as the source neutral weight. -/
def compressionCoframeForce (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (scaleDerivative (compressionCore F)) (neutralCurrent sharp m ell)

attribute [local irreducible] scaleDerivative compressionCoframeForce

private theorem source_compression_coframe (sharp : Bool) (m ell : ℕ) (F : Index) :
    scaleDerivative (compressionNeutral sharp m ell F)=
      compressionCoframeForce sharp m ell F-(3 : ℂ) • compressionNeutral sharp m ell F := by
  have hb (A B : End) : scaleDerivative (bracket A B)=
      bracket (scaleDerivative A) B+bracket A (scaleDerivative B) := by
    rw [←K_commutator,←K_commutator,←K_commutator]
    unfold bracket
    noncomm_ring
  unfold compressionNeutral compressionCoframeForce
  rw [hb,original_neutral_coframe]
  simp only [bracket,smul_mul_assoc,mul_smul_comm,←smul_sub]
  module

private theorem inverse_cross_one (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) :
    inverseCross F seed z A 1 0=sandwichJet F seed z A 1 0 0 0-
      finiteResolvent F z*readOrbitJet F seed A 1 0 0 0*finiteResolvent F z := by
  simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet]
  rfl

/-- Literal complete corrected-CF origin: source force, both inverse legs and moving input remain one paid object. -/
theorem actual_corrected_coframe_compression_origin (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    correctedCoframeCompressionJet sharp m ell F seed z 0 0=
      finiteResolvent F z*sourceRead F seed (compressionCoframeForce sharp m ell F)*finiteResolvent F z+
      inverseCross F seed z (compressionNeutral sharp m ell F) 1 0+
      finiteResolvent F z*inputFlux F seed (compressionNeutral sharp m ell F) 1 0*finiteResolvent F z := by
  let A := compressionNeutral sharp m ell F
  have hi := inverse_cross_one F seed z hz A
  have hm := (sandwich_orbit F seed z hz A 0).trans (origin_conjugate _)
  have hg := congrArg (sourceRead F seed) (source_compression_coframe sharp m ell F)
  simp only [map_sub,map_smul] at hg
  have hf : inputFlux F seed A 1 0=readOrbitJet F seed A 1 0 0 0-sourceRead F seed (scaleDerivative A) := by
    simp only [inputFlux,coreJet,pow_zero,pow_one,Module.End.one_apply]
  have hfr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hf
  have hgr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hg
  simp only [mul_sub,sub_mul] at hfr
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at hgr
  unfold correctedCoframeCompressionJet
  dsimp only [A] at hi hm hfr ⊢
  linear_combination (norm := module) -hi+(3 : ℂ) • hm-hfr+hgr

end LowEnergy.SourceInverseCoframeCompressionBudget
