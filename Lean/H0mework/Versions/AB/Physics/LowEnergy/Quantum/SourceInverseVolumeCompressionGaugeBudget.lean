import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeGaugeSingleDefectJoin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCompressionGaugeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular SourceEscapeCurrent
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseProjectionCurrentRemainder SourceInverseGaugeSingleDefectJoin
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

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (t : ℝ) :
    sandwichJet F g z A 0 0 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 0 t*(readOrbitJet F g A 0 0 0 t*resolventJet F z 0 0 0 t)=_
  exact (congrArg₂ (fun r a : Op => r*(a*r))
    (actual_mixed_resolvent F z hz 0 t) (actual_read_orbit F g A 0 t)).trans
      (map_sandwich _ _ _)

private theorem inverse_flow_core (t : ℝ) (f : QuantumTest) :
    (mixedHilbert 0 t).symm (embed f)=embed (SourceGaugeScaleTransport.coreFlow (-t) f) := by
  apply (mixedHilbert 0 t).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
    SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_on_core]
  rw [SourceGaugeScaleTransport.coreFlow_add,add_neg_cancel,SourceGaugeScaleTransport.coreFlow_zero]

private theorem orbit_pair (B : Op) (t : ℝ) (g k : QuantumTest) :
    inner ℂ (embed k) ((mixedHilbert 0 t).conjStarAlgEquiv B (embed g))=
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) g))) := by
  have h := (mixedHilbert 0 t).inner_map_map ((mixedHilbert 0 t).symm (embed k))
    (B ((mixedHilbert 0 t).symm (embed g)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℂ (embed k) ((mixedHilbert 0 t).conjStarAlgEquiv B (embed g))=_ at h
  simpa only [inverse_flow_core] using h

private theorem negative_flow (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => embed (SourceGaugeScaleTransport.coreFlow (-s) f))
      (-embed (SourceGaugeScaleTransport.coreFlow (-t) (G f))) t := by
  simpa only [neg_smul,one_smul] using!
    (SourceGaugeScaleTransport.strong_core_derivative f (-t)).scomp t ((hasDerivAt_id t).neg)

private theorem pullback_derivative (B : Op) (g k : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-s) k))
      (B (embed (SourceGaugeScaleTransport.coreFlow (-s) g))))
      (-inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) (G g))))-
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) (G k)))
        (B (embed (SourceGaugeScaleTransport.coreFlow (-t) g)))) t := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (negative_flow g t)
  have h := (negative_flow k t).inner ℂ hg
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
    (hO : ∀ t,J 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (J 0 0))
    (g k : QuantumTest) (t : ℝ) :
    weakJet J g k 1 t= -weakJet J (G g) k 0 t-weakJet J g (G k) 0 t := by
  have ho (f h : QuantumTest) (s : ℝ) : weakJet J f h 0 s=
      inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-s) h))
        (J 0 0 (embed (SourceGaugeScaleTransport.coreFlow (-s) f))) := by
    rw [weakJet,hO]
    exact orbit_pair _ s f h
  have h := (pullback_derivative (J 0 0) g k t).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (ho g k))
  have hu := (weak_derivative J hJ g k 0 t).unique h
  rw [ho (G g) k,ho g (G k)]
  exact hu

private theorem weak_next (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (J 0 0))
    (n : ℕ) (g k : QuantumTest) (t : ℝ) :
    weakJet J g k (n+1) t= -weakJet J (G g) k n t-weakJet J g (G k) n t := by
  induction n generalizing g k t with
  | zero => exact weak_first J hJ hO g k t
  | succ n ih =>
    have hd := (weak_derivative J hJ (G g) k n t).neg.sub (weak_derivative J hJ g (G k) n t)
    exact (weak_derivative J hJ g k (n+1) t).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (ih g k)))

def gaugeProfile (F : Index) (seed : diagonal.domain) (z : ℂ) (A : End)
    (f k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (sandwichJet F seed z A 0 n 0 t (embed f))

private theorem profile_next (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End)
    (f k : QuantumTest) (n : ℕ) (t : ℝ) :
    gaugeProfile F seed z A f k (n+1) t=
      -gaugeProfile F seed z A (G f) k n t-gaugeProfile F seed z A f (G k) n t := by
  let J := fun n t => sandwichJet F seed z A 0 n 0 t
  have hO (t : ℝ) : J 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (J 0 0) := by
    have ho := (sandwich_orbit F seed z hz A 0).trans (origin_conjugate _)
    exact (sandwich_orbit F seed z hz A t).trans (congrArg (mixedHilbert 0 t).conjStarAlgEquiv ho.symm)
  exact weak_next J (fun n t => sandwich_gauge_derivative F seed z A 0 n 0 t) hO n f k t

private theorem profile_origin (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A : End) (f k : QuantumTest) :
    gaugeProfile F seed z A f k 0 0=
      inner ℂ (embed k) ((finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) (embed f)) :=
  congrArg (fun B : Op => inner ℂ (embed k) (B (embed f)))
    ((sandwich_orbit F seed z hz A 0).trans (origin_conjugate _))

theorem gauge_profile_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => gaugeProfile F seed (line μ w) A f k n 0) := by
  induction n generalizing f k with
  | zero =>
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    have hc : Continuous (fun w : ℝ => inner ℂ (embed k)
        (finiteResolvent F (line μ w) (sourceRead F seed A (finiteResolvent F (line μ w) (embed f))))) :=
      continuous_const.inner (hr.clm_apply ((sourceRead F seed A).continuous.comp (hr.clm_apply continuous_const)))
    exact hc.congr (fun w => (profile_origin F seed (line μ w)
      (by simpa only [line_im] using hμ.ne') A f k).symm)
  | succ n ih =>
    exact ((ih (G f) k).neg.sub (ih f (G k))).congr (fun w =>
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

private theorem read_same_support (F : Index) (seed seed' : diagonal.domain) (A : End) (x : H)
    (hx : x∈supportSpan F) : sourceRead F seed A x=sourceRead F seed' A x := by
  have hp := (inputSpan F seed).orthogonalProjectionOnto_mem_subspace_eq_self ⟨x,Submodule.mem_sup_left hx⟩
  have hp' := (inputSpan F seed').orthogonalProjectionOnto_mem_subspace_eq_self ⟨x,Submodule.mem_sup_left hx⟩
  let a := Submodule.inclusion (input_span_core F seed) ((inputSpan F seed).orthogonalProjectionOnto x)
  let b := Submodule.inclusion (input_span_core F seed') ((inputSpan F seed').orthogonalProjectionOnto x)
  have ha : (a : H)=x := congrArg Subtype.val hp
  have hb : (b : H)=x := congrArg Subtype.val hp'
  have he : a=b := Subtype.ext (ha.trans hb.symm)
  unfold sourceRead coreRead
  exact congrArg (fun q : diagonal.domain => embed (A (coreEquiv.symm q))) he

private theorem source_seed_independent (seed : diagonal.domain) (f k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (z : ℂ),z.im≠0 → ∀ A : End,
      gaugeProfile F seed z A f k 0 0=gaugeProfile F (coreEquiv f) z A f k 0 0 := by
  filter_upwards [source_eventually_mem_support (coreEquiv f)] with F hF
  intro z hz A
  have hx : finiteResolvent F z (embed f)∈supportSpan F := resolvent_mem_support F z hz _ hF
  have he := congrArg (fun v : H => inner ℂ (embed k) (finiteResolvent F z v))
    (read_same_support F seed (coreEquiv f) A (finiteResolvent F z (embed f)) hx)
  exact (profile_origin F seed z hz A f k).trans
    (he.trans (profile_origin F (coreEquiv f) z hz A f k).symm)

/-- Original compression currents for the first H-current and its exact source gauge derivative. -/
def compressionFirst (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (compressionCore F) (firstHamiltonianCurrent sharp m ell)
def compressionMatter (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (compressionCore F) (matterInsertion sharp m ell)

def compressionGaugeForce (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (deltaGauge (compressionCore F)) (firstHamiltonianCurrent sharp m ell)

attribute [local irreducible] compressionFirst compressionMatter compressionGaugeForce

private theorem compression_first_split (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) :
    sourceRead F seed (compressionFirst sharp m ell F)=
      SourceScalarForceBudget.doubleResponse sharp m ell F seed+doubleProjectionFlux sharp m ell F seed-
        sourceRead F seed (singleDefect sharp m ell F) := by
  have he : compressionFirst sharp m ell F=
      bracket diagonalAction (bracket diagonalAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell))-
        singleDefect sharp m ell F := by
    unfold compressionFirst firstHamiltonianCurrent singleDefect defectAction bracket
    noncomm_ring
  have hr := congrArg (sourceRead F seed) he
  simp only [map_sub] at hr
  have hp := actual_double_projection_flux sharp m ell F seed
  change doubleProjectionFlux sharp m ell F seed=_-SourceScalarForceBudget.doubleResponse sharp m ell F seed at hp
  linear_combination (norm := module) hr-hp

private theorem pair_sandwich_add_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r a b c : E →L[ℂ] E) (x y : E) :
    inner ℂ y ((r*(a+b-c)*r) x)=inner ℂ y ((r*a*r) x)+inner ℂ y ((r*b*r) x)-inner ℂ y ((r*c*r) x) := by
  simp only [mul_add,add_mul,mul_sub,sub_mul,add_apply,sub_apply,inner_add_right,inner_sub_right]

/-- Each fixed cutoff window uses its original cofinal event; the actual first compression current equals the already paid double current. -/
theorem actual_first_current_double (m ell : ℕ) (seed : diagonal.domain) (f k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      gaugeProfile F seed z (compressionFirst sharp m ell F) f k 0 0=
        SourceScalarDoubleEndpoint.doubleResponse sharp m ell F (coreEquiv f) (coreEquiv k) z := by
  filter_upwards [source_seed_independent seed f k,
    actual_projection_single_defect m ell (coreEquiv f) (coreEquiv k)] with F hseed hD
  intro sharp z hz
  have he := congrArg (fun A : Op => inner ℂ (embed k) ((finiteResolvent F z*A*finiteResolvent F z) (embed f)))
    (compression_first_split sharp m ell F (coreEquiv f))
  have hlin := pair_sandwich_add_sub (finiteResolvent F z)
    (SourceScalarForceBudget.doubleResponse sharp m ell F (coreEquiv f))
    (doubleProjectionFlux sharp m ell F (coreEquiv f))
    (sourceRead F (coreEquiv f) (singleDefect sharp m ell F)) (embed f) (embed k)
  have hd := hD sharp z hz
  change inner ℂ (embed k) ((finiteResolvent F z*doubleProjectionFlux sharp m ell F (coreEquiv f)*finiteResolvent F z) (embed f))=
    inner ℂ (embed k) ((finiteResolvent F z*sourceRead F (coreEquiv f) (singleDefect sharp m ell F)*finiteResolvent F z) (embed f)) at hd
  have hc : inner ℂ (embed k) ((finiteResolvent F z*SourceScalarForceBudget.doubleResponse sharp m ell F (coreEquiv f)*
      finiteResolvent F z) (embed f))=SourceScalarDoubleEndpoint.doubleResponse sharp m ell F (coreEquiv f) (coreEquiv k) z := by
    unfold SourceScalarForceBudget.doubleResponse SourceScalarDoubleEndpoint.doubleResponse
      SourceScalarDoubleCurrent.fullInsertion SourceScalarDoubleEndpoint.fullInsertion
    rfl
  exact (hseed z hz _).trans ((profile_origin F (coreEquiv f) z hz _ f k).trans
    (he.trans (hlin.trans (by rw [hd,add_sub_cancel_right,hc]))))

private theorem whole_current_core (sharp : Bool) (m ell : ℕ) (F : Index) (q : QuantumTest) :
    wholeCurrent sharp m ell F (embed q)=embed (compressionMatter sharp m ell F q) := by
  have h : ∀ p : QuantumTest,inner ℂ (embed p) (wholeCurrent sharp m ell F (embed q))=
      inner ℂ (embed p) (embed (compressionMatter sharp m ell F q)) := by
    intro p
    simpa only [compressionMatter,sourcePair] using! original_whole_current_pair sharp m ell F p q
  apply ext_inner_left ℂ
  intro x
  exact SourceCoframeScaleTransport.embed_dense.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) h

private theorem actual_matter_whole (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (f k : QuantumTest) :
    gaugeProfile F (coreEquiv f) z (compressionMatter sharp m ell F) f k 0 0=
      firstRetardedCurrent sharp m ell F z hz (coreEquiv f) (coreEquiv k) := by
  let q := coreEquiv.symm (sourceCore F z hz (coreEquiv f))
  have hq : embed q=finiteResolvent F z (embed f) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hs := source_read_resolvent F (coreEquiv f) (compressionMatter sharp m ell F) z hz
  have hw := whole_current_core sharp m ell F q
  rw [hq] at hw
  have he : sourceRead F (coreEquiv f) (compressionMatter sharp m ell F) (finiteResolvent F z (embed f))=
      wholeCurrent sharp m ell F (finiteResolvent F z (embed f)) := hs.trans hw.symm
  have hp := congrArg (fun v : H => inner ℂ (embed k) (finiteResolvent F z v)) he
  have ha := actual_whole_response sharp m ell F z hz (coreEquiv f) (coreEquiv k)
  unfold wholeResponse at ha
  exact (profile_origin F (coreEquiv f) z hz _ f k).trans (hp.trans ha)

private theorem first_base_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) : Tail (fun m ell F w => gaugeProfile F seed (line μ w)
      (compressionFirst sharp m ell F) f k 0 0) := by
  apply tail_congr _ (fun m ell F w => SourceScalarDoubleEndpoint.doubleResponse sharp m ell F (coreEquiv f) (coreEquiv k) (line μ w))
  · intro m ell
    filter_upwards [actual_first_current_double m ell seed f k] with F hF
    intro w
    exact hF sharp (line μ w) (by simpa only [line_im] using hμ.ne')
  · exact SourceScalarDoubleEndpoint.actual_double_tail sharp (coreEquiv f) (coreEquiv k) μ hμ

private theorem matter_base_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) : Tail (fun m ell F w => gaugeProfile F seed (line μ w)
      (compressionMatter sharp m ell F) f k 0 0) := by
  apply tail_congr _ (fun m ell F w => firstRetardedCurrent sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') (coreEquiv f) (coreEquiv k))
  · intro m ell
    filter_upwards [source_seed_independent seed f k] with F hF
    intro w
    exact (hF (line μ w) (by simpa only [line_im] using hμ.ne') _).trans
      (actual_matter_whole sharp m ell F _ (by simpa only [line_im] using hμ.ne') f k)
  · intro ε hε
    obtain ⟨N,hN⟩ := actual_first_retarded_tail sharp μ hμ (coreEquiv f) (coreEquiv k) ε hε
    exact ⟨N,fun m hm ell hell => Filter.Eventually.of_forall (hN m hm ell hell)⟩

private theorem all_gauge_tails (A : ℕ → ℕ → Index → End) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (hbase : ∀ f k : QuantumTest,Tail (fun m ell F w => gaugeProfile F seed (line μ w) (A m ell F) f k 0 0))
    (n : ℕ) (f k : QuantumTest) :
    Tail (fun m ell F w => gaugeProfile F seed (line μ w) (A m ell F) f k n 0) := by
  induction n generalizing f k with
  | zero => exact hbase f k
  | succ n ih =>
    have htail := tail_add _ _
      (fun m ell F => (gauge_profile_continuous F seed (A m ell F) μ hμ n (G f) k).neg)
      (tail_neg _ (ih (G f) k)) (tail_neg _ (ih f (G k)))
    apply tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => ?_)) htail
    rw [profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne')]
    simp only [Pi.neg_apply,sub_eq_add_neg]

/-- Every fixed finite gauge order is paid by the original double-current endpoints; no uniform high-jet assumption appears. -/
theorem actual_first_compression_gauge_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖gaugeProfile F seed (line μ w)
          (compressionFirst sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε :=
  all_gauge_tails (compressionFirst sharp) seed μ hμ (first_base_tail sharp seed μ hμ) n f k

/-- The genuine first-current family supplies the other finite gauge jets in the same signed correction. -/
theorem actual_matter_compression_gauge_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖gaugeProfile F seed (line μ w)
          (compressionMatter sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε :=
  all_gauge_tails (compressionMatter sharp) seed μ hμ (matter_base_tail sharp seed μ hμ) n f k

/-- The complete compression-gauge force, including both inverse legs and input motion, is one actual response difference. -/
def correctedCompressionJet (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F seed z (compressionFirst sharp m ell F) 0 (n+1) 0 t-
    sandwichJet F seed z (compressionMatter sharp m ell F) 0 n 0 t

private theorem source_compression_gauge (sharp : Bool) (m ell : ℕ) (F : Index) :
    deltaGauge (compressionFirst sharp m ell F)=compressionGaugeForce sharp m ell F+compressionMatter sharp m ell F := by
  have h (A B : End) : deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
    unfold deltaGauge bracket
    change SourceGaugeRadialPair.gaugeEulerAction*(A*B-B*A)-(A*B-B*A)*SourceGaugeRadialPair.gaugeEulerAction=
      (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B-
        B*(SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)+
      (A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)-
        (SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)*A)
    noncomm_ring
  unfold compressionFirst compressionGaugeForce compressionMatter
  rw [h,original_first_current_gauge]

private theorem inverse_cross_one (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) :
    inverseCross F seed z A 0 1=sandwichJet F seed z A 0 1 0 0-
      finiteResolvent F z*readOrbitJet F seed A 0 1 0 0*finiteResolvent F z := by
  simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet]
  rfl

/-- Literal source identity: the uncorrected CF derivative is never mistaken for the paid joint force. -/
theorem actual_corrected_compression_origin (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    correctedCompressionJet sharp m ell F seed z 0 0=
      finiteResolvent F z*sourceRead F seed (compressionGaugeForce sharp m ell F)*finiteResolvent F z+
      inverseCross F seed z (compressionFirst sharp m ell F) 0 1+
      finiteResolvent F z*inputFlux F seed (compressionFirst sharp m ell F) 0 1*finiteResolvent F z := by
  let A := compressionFirst sharp m ell F
  have hi := inverse_cross_one F seed z hz A
  have hm := (sandwich_orbit F seed z hz (compressionMatter sharp m ell F) 0).trans (origin_conjugate _)
  have hg := congrArg (sourceRead F seed) (source_compression_gauge sharp m ell F)
  simp only [map_add] at hg
  have hf : inputFlux F seed A 0 1=readOrbitJet F seed A 0 1 0 0-sourceRead F seed (deltaGauge A) := by
    simp only [inputFlux,coreJet,pow_zero,pow_one,Module.End.one_apply]
  have hfr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hf
  have hgr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) hg
  simp only [mul_sub,sub_mul] at hfr
  simp only [mul_add,add_mul] at hgr
  unfold correctedCompressionJet
  dsimp only [A] at hi hfr ⊢
  linear_combination (norm := module) -hi-hm-hfr+hgr

/-- Each fixed finite jet of the complete signed compression correction has the original full-frequency common tail. -/
theorem actual_corrected_compression_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (correctedCompressionJet sharp m ell F seed (line μ w) n 0 (embed f))‖^2))≤ENNReal.ofReal ε := by
  have ht := tail_add _ _ (fun m ell F => gauge_profile_continuous F seed (compressionFirst sharp m ell F) μ hμ (n+1) f k)
    (actual_first_compression_gauge_tail sharp seed μ hμ (n+1) f k)
    (tail_neg _ (actual_matter_compression_gauge_tail sharp seed μ hμ n f k))
  simpa only [Tail,correctedCompressionJet,sub_apply,inner_sub_right,gaugeProfile,←sub_eq_add_neg] using! ht

end LowEnergy.SourceInverseCompressionGaugeBudget
