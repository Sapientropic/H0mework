import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeCoframeWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceScalarMixedEndpointBudget
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory
open SourceGaugeCoframeJets SourceResolventBandLimit FullYSourceResolventGraphSplice
open scoped InnerProductSpace

private def coframeSplit :
    ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ) → ℝ → ℝ → ℂ
  | 0,r,u,v,w,L,s,t => L r u v w s t
  | a+1,r,u,v,w,L,s,t =>
      -coframeSplit a (r+1) u v w L s t-coframeSplit a r u (v+1) w L s t

private def mixedSplit :
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ) → ℝ → ℝ → ℂ
  | a,0,r,u,v,w,L,s,t => coframeSplit a r u v w L s t
  | a,b+1,r,u,v,w,L,s,t =>
      -mixedSplit a b r (u+1) v w L s t-mixedSplit a b r u v (w+1) L s t

private theorem coframe_split_coframe
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ)
    (h : ∀ r u v w s t, HasDerivAt (fun x => L r u v w x t)
      (-L (r+1) u v w s t-L r u (v+1) w s t) s)
    (a r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => coframeSplit a r u v w L x t)
      (coframeSplit (a+1) r u v w L s t) s := by
  induction a generalizing r u v w with
  | zero => exact h r u v w s t
  | succ a ih => exact (ih (r+1) u v w).neg.sub (ih r u (v+1) w)

private theorem coframe_split_gauge
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ)
    (h : ∀ r u v w s t, HasDerivAt (L r u v w s)
      (-L r (u+1) v w s t-L r u v (w+1) s t) t)
    (a r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (coframeSplit a r u v w L s)
      (-coframeSplit a r (u+1) v w L s t-coframeSplit a r u v (w+1) L s t) t := by
  induction a generalizing r u v w with
  | zero => exact h r u v w s t
  | succ a ih =>
    apply ((ih (r+1) u v w).neg.sub (ih r u (v+1) w)).congr_deriv
    simp only [coframeSplit]
    abel

private theorem mixed_split_coframe
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ)
    (h : ∀ r u v w s t, HasDerivAt (fun x => L r u v w x t)
      (-L (r+1) u v w s t-L r u (v+1) w s t) s)
    (a b r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => mixedSplit a b r u v w L x t)
      (mixedSplit (a+1) b r u v w L s t) s := by
  induction b generalizing r u v w with
  | zero => exact coframe_split_coframe L h a r u v w s t
  | succ b ih => exact (ih r (u+1) v w).neg.sub (ih r u v (w+1))

private theorem mixed_split_gauge
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ)
    (h : ∀ r u v w s t, HasDerivAt (L r u v w s)
      (-L r (u+1) v w s t-L r u v (w+1) s t) t)
    (a b r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (mixedSplit a b r u v w L s)
      (mixedSplit a (b+1) r u v w L s t) t := by
  induction b generalizing r u v w with
  | zero => exact coframe_split_gauge L h a r u v w s t
  | succ b ih => exact (ih r (u+1) v w).neg.sub (ih r u v (w+1))

private def pairLeaf (B : Op) (g k : QuantumTest) (r u v w : ℕ) (s t : ℝ) : ℂ :=
  inner ℂ (testJet r u k (-s) (-t)) (B (testJet v w g (-s) (-t)))

private theorem negative_coframe (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    HasDerivAt (fun x => testJet a b f (-x) (-t)) (-testJet (a+1) b f (-s) (-t)) s := by
  simpa only [neg_smul,one_smul] using!
    (test_coframe_derivative a b f (-s) (-t)).scomp s ((hasDerivAt_id s).neg)

private theorem negative_gauge (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    HasDerivAt (fun x => testJet a b f (-s) (-x)) (-testJet a (b+1) f (-s) (-t)) t := by
  simpa only [neg_smul,one_smul] using!
    (test_gauge_derivative a b f (-s) (-t)).scomp t ((hasDerivAt_id t).neg)

private theorem pair_leaf_coframe (B : Op) (g k : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => pairLeaf B g k r u v w x t)
      (-pairLeaf B g k (r+1) u v w s t-pairLeaf B g k r u (v+1) w s t) s := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (negative_coframe v w g s t)
  change HasDerivAt (fun x => B (testJet v w g (-x) (-t)))
    (B (-testJet (v+1) w g (-s) (-t))) s at hg
  have h := (negative_coframe r u k s t).inner ℂ hg
  apply h.congr_deriv
  simp only [pairLeaf,map_neg,inner_neg_left,inner_neg_right]
  abel

private theorem pair_leaf_gauge (B : Op) (g k : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (pairLeaf B g k r u v w s)
      (-pairLeaf B g k r (u+1) v w s t-pairLeaf B g k r u v (w+1) s t) t := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (negative_gauge v w g s t)
  change HasDerivAt (fun x => B (testJet v w g (-s) (-x)))
    (B (-testJet v (w+1) g (-s) (-t))) t at hg
  have h := (negative_gauge r u k s t).inner ℂ hg
  apply h.congr_deriv
  simp only [pairLeaf,map_neg,inner_neg_left,inner_neg_right]
  abel

/-- Generated fixed source jets of the same moving double response. -/
def endpointJet (B : Op) (g k : QuantumTest) (a b : ℕ) (s t : ℝ) : ℂ :=
  mixedSplit a b 0 0 0 0 (pairLeaf B g k) s t

private theorem endpoint_coframe (B : Op) (g k : QuantumTest) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => endpointJet B g k a b x t) (endpointJet B g k (a+1) b s t) s :=
  mixed_split_coframe _ (pair_leaf_coframe B g k) a b 0 0 0 0 s t

private theorem endpoint_gauge (B : Op) (g k : QuantumTest) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (endpointJet B g k a b s) (endpointJet B g k a (b+1) s t) t :=
  mixed_split_gauge _ (pair_leaf_gauge B g k) a b 0 0 0 0 s t

private theorem mixed_inverse_core (s t : ℝ) (f : QuantumTest) :
    (mixedHilbert s t).symm (embed f)=testJet 0 0 f (-s) (-t) := by
  apply (mixedHilbert s t).injective
  rw [LinearIsometryEquiv.apply_symm_apply, test_jet_zero]
  change embed f=SourceGaugeScaleTransport.hilbertFlow t
    (coframeHilbert s (SourceGaugeScaleTransport.hilbertFlow (-t) (coframeHilbert (-s) (embed f))))
  rw [hilbert_flows_commute,SourceGaugeScaleTransport.hilbertFlow_add,add_neg_cancel,
    SourceGaugeScaleTransport.hilbertFlow_zero]
  change embed f=SourceCoframeScaleTransport.hilbertFlow ((3/2 : ℝ)*s)
    (SourceCoframeScaleTransport.hilbertFlow ((3/2 : ℝ)*(-s)) (embed f))
  rw [SourceCoframeScaleTransport.hilbertFlow_add,mul_neg,add_neg_cancel,
    SourceCoframeScaleTransport.hilbertFlow_zero]

private theorem fixed_pair_derivative {A : ℝ → Op} {A' : Op} {s : ℝ}
    (h : HasDerivAt A A' s) (g k : H) :
    HasDerivAt (fun x => inner ℂ k (A x g)) (inner ℂ k (A' g)) s := by
  exact (((innerSL ℂ k).comp (ContinuousLinearMap.apply ℂ H g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h

/-- Every actual mixed operator jet returns fixed original source jets, with all derivative signs. -/
theorem actual_mixed_endpoint_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g k : QuantumTest) (a b : ℕ) (s t : ℝ) :
    inner ℂ (embed k) (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F z a b s t (embed g))=
      endpointJet (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F z) g k a b s t := by
  have h0 (s t : ℝ) :
      inner ℂ (embed k) (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F z 0 0 s t (embed g))=
        endpointJet (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F z) g k 0 0 s t := by
    rw [SourceGaugeCoframeWard.actual_double_mixed_profile sharp m ell F z hz s t,
      mixed_inverse_core,mixed_inverse_core]
    rfl
  have hc (a : ℕ) (s t : ℝ) :
      inner ℂ (embed k) (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F z a 0 s t (embed g))=
        endpointJet (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F z) g k a 0 s t := by
    induction a generalizing s t with
    | zero => exact h0 s t
    | succ a ih =>
      have hd := fixed_pair_derivative
        (SourceGaugeCoframeWard.double_orbit_coframe_derivative sharp m ell F z a 0 s t) (embed g) (embed k)
      have he := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => (ih x t).symm))
      exact he.unique (endpoint_coframe _ g k a 0 s t)
  induction b generalizing s t with
  | zero => exact hc a s t
  | succ b ih =>
    have hd := fixed_pair_derivative
      (SourceGaugeCoframeWard.double_orbit_gauge_derivative sharp m ell F z a b s t) (embed g) (embed k)
    have he := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => (ih s x).symm))
    exact he.unique (endpoint_gauge _ g k a b s t)

private def CofinalTail (A : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ, ENNReal.ofReal (‖A m ell F w‖^2)) ≤ ENNReal.ofReal ε

private theorem two_square (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

private theorem two_energy (a b : ℝ → ℂ)
    (hm : Measurable (fun w => ENNReal.ofReal (‖a w‖^2))) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖a w+b w‖^2)) ≤
      ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖a w‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal (‖b w‖^2)) := by
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖a w‖^2)+ENNReal.ofReal (‖b w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (two_square _ _)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hm]

private theorem tail_add (A B : ℕ → ℕ → Index → ℝ → ℂ)
    (hm : ∀ m ell F, Measurable (fun w => ENNReal.ofReal (‖A m ell F w‖^2)))
    (hA : CofinalTail A) (hB : CofinalTail B) :
    CofinalTail (fun m ell F w => A m ell F w+B m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hA (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hB (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm' ell hell => ?_⟩
  filter_upwards [h₁ m (le_trans (Nat.le_max_left _ _) hm') ell hell,
    h₂ m (le_trans (Nat.le_max_right _ _) hm') ell hell] with F hX hY
  apply (two_energy _ _ (hm m ell F)).trans
  calc
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by positivity)
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem tail_neg (A : ℕ → ℕ → Index → ℝ → ℂ) (h : CofinalTail A) :
    CofinalTail (fun m ell F w => -A m ell F w) := by
  simpa only [CofinalTail,norm_neg] using h

private theorem whole_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : H) :
    Continuous (fun w : ℝ => inner ℂ k (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F (line μ w) g)) := by
  let C := GaussGradedCompression.compression F
  let B := SourceEscapeSeedTail.actualIncrement sharp m ell
  let A := C*(C*B-B*C)-(C*B-B*C)*C
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact continuous_const.inner ((((hr.mul (continuous_const : Continuous (fun _ : ℝ => A))).mul hr).clm_apply continuous_const))

private theorem whole_tail (sharp : Bool) (g k : QuantumTest) (μ : ℝ) (hμ : 0<μ) :
    CofinalTail (fun m ell F w => inner ℂ (embed k)
      (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F (line μ w) (embed g))) := by
  have h := SourceScalarDoubleEndpoint.actual_double_tail sharp (coreEquiv g) (coreEquiv k) μ hμ
  have he (m ell : ℕ) (F : Index) (w : ℝ) := SourceScalarGaugeEndpoint.actual_whole_return sharp m ell F
    (coreEquiv g) (coreEquiv k) (line μ w) (by simpa only [line_im] using hμ.ne')
  have hv (f : QuantumTest) : (coreEquiv f : H)=embed f := rfl
  simpa only [CofinalTail,he,hv] using! h

private theorem coframe_split_continuous
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℂ) (h : ∀ r u v w, Continuous (L r u v w))
    (a r u v w : ℕ) :
    Continuous (fun x => coframeSplit a r u v w (fun r u v w _ _ => L r u v w x) 0 0) := by
  induction a generalizing r u v w with
  | zero => exact h r u v w
  | succ a ih => exact (ih (r+1) u v w).neg.sub (ih r u (v+1) w)

private theorem mixed_split_continuous
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℂ) (h : ∀ r u v w, Continuous (L r u v w))
    (a b r u v w : ℕ) :
    Continuous (fun x => mixedSplit a b r u v w (fun r u v w _ _ => L r u v w x) 0 0) := by
  induction b generalizing r u v w with
  | zero => exact coframe_split_continuous L h a r u v w
  | succ b ih => exact (ih r (u+1) v w).neg.sub (ih r u v (w+1))

private theorem coframe_split_tail
    (L : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Index → ℝ → ℂ)
    (hm : ∀ r u v w m ell F, Continuous (L r u v w m ell F))
    (ht : ∀ r u v w, CofinalTail (L r u v w)) (a r u v w : ℕ) :
    CofinalTail (fun m ell F x => coframeSplit a r u v w
      (fun r u v w _ _ => L r u v w m ell F x) 0 0) := by
  induction a generalizing r u v w with
  | zero => exact ht r u v w
  | succ a ih =>
    simpa only [coframeSplit,sub_eq_add_neg] using!
      tail_add _ _
        (fun m ell F => (((coframe_split_continuous _ (fun r u v w => hm r u v w m ell F)
          a (r+1) u v w).neg.norm.pow 2).measurable.ennreal_ofReal))
        (tail_neg _ (ih (r+1) u v w)) (tail_neg _ (ih r u (v+1) w))

private theorem mixed_split_tail
    (L : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Index → ℝ → ℂ)
    (hm : ∀ r u v w m ell F, Continuous (L r u v w m ell F))
    (ht : ∀ r u v w, CofinalTail (L r u v w)) (a b r u v w : ℕ) :
    CofinalTail (fun m ell F x => mixedSplit a b r u v w
      (fun r u v w _ _ => L r u v w m ell F x) 0 0) := by
  induction b generalizing r u v w with
  | zero => exact coframe_split_tail L hm ht a r u v w
  | succ b ih =>
    simpa only [mixedSplit,sub_eq_add_neg] using!
      tail_add _ _
        (fun m ell F => (((mixed_split_continuous _ (fun r u v w => hm r u v w m ell F)
          a b r (u+1) v w).neg.norm.pow 2).measurable.ennreal_ofReal))
        (tail_neg _ (ih r (u+1) v w)) (tail_neg _ (ih r u v (w+1)))

private theorem coframe_split_congr
    (L L' : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ) (s t : ℝ)
    (h : ∀ r u v w, L r u v w s t=L' r u v w s t) (a r u v w : ℕ) :
    coframeSplit a r u v w L s t=coframeSplit a r u v w L' s t := by
  induction a generalizing r u v w with
  | zero => exact h r u v w
  | succ a ih => exact congrArg₂ (fun x y : ℂ => -x-y) (ih (r+1) u v w) (ih r u (v+1) w)

private theorem mixed_split_congr
    (L L' : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℂ) (s t : ℝ)
    (h : ∀ r u v w, L r u v w s t=L' r u v w s t) (a b r u v w : ℕ) :
    mixedSplit a b r u v w L s t=mixedSplit a b r u v w L' s t := by
  induction b generalizing r u v w with
  | zero => exact coframe_split_congr L L' s t h a r u v w
  | succ b ih => exact congrArg₂ (fun x y : ℂ => -x-y) (ih r (u+1) v w) (ih r u v (w+1))

private theorem endpoint_origin (B : Op) (g k : QuantumTest) (a b : ℕ) :
    endpointJet B g k a b 0 0=mixedSplit a b 0 0 0 0
      (fun r u v w _ _ => inner ℂ (embed (sourceTest r u k)) (B (embed (sourceTest v w g)))) 0 0 := by
  unfold endpointJet
  exact mixed_split_congr _ _ 0 0
    (fun r u v w => by simp only [pairLeaf,neg_zero,test_jet_origin]) a b 0 0 0 0

/-- The full-frequency common tail of every actual mixed double-current jet is source generated. -/
theorem actual_mixed_double_tail (sharp : Bool) (g k : QuantumTest) (μ : ℝ) (hμ : 0<μ)
    (a b : ℕ) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖inner ℂ (embed k)
          (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0 (embed g))‖^2)) ≤
          ENNReal.ofReal ε := by
  have ht := mixed_split_tail
    (fun r u v w m ell F x => inner ℂ (embed (sourceTest r u k))
      (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F (line μ x) (embed (sourceTest v w g))))
    (fun r u v w m ell F => whole_continuous sharp m ell F μ hμ _ _)
    (fun r u v w => whole_tail sharp (sourceTest v w g) (sourceTest r u k) μ hμ) a b 0 0 0 0
  have he (m ell : ℕ) (F : Index) (w : ℝ) := actual_mixed_endpoint_return sharp m ell F
    (line μ w) (by simpa only [line_im] using hμ.ne') g k a b 0 0
  simpa only [CofinalTail,he,endpoint_origin] using! ht

private def Good (A : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  (∀ m ell F, Continuous (A m ell F)) ∧ CofinalTail A

private theorem good_add {A B : ℕ → ℕ → Index → ℝ → ℂ} (hA : Good A) (hB : Good B) :
    Good (fun m ell F w => A m ell F w+B m ell F w) :=
  ⟨fun m ell F => (hA.1 m ell F).add (hB.1 m ell F),
    tail_add A B (fun m ell F => ((hA.1 m ell F).norm.pow 2).measurable.ennreal_ofReal) hA.2 hB.2⟩

private theorem good_smul {A : ℕ → ℕ → Index → ℝ → ℂ} (hA : Good A) (c : ℂ) :
    Good (fun m ell F w => c • A m ell F w) := by
  refine ⟨fun m ell F => (hA.1 m ell F).const_smul c,?_⟩
  intro ε hε
  have hd : 0 < ‖c‖^2+1 := by positivity
  obtain ⟨N,hN⟩ := hA.2 (ε/(‖c‖^2+1)) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have he : (∫⁻ w : ℝ, ENNReal.ofReal (‖c • A m ell F w‖^2))=
      ENNReal.ofReal (‖c‖^2)*(∫⁻ w : ℝ, ENNReal.ofReal (‖A m ell F w‖^2)) := by
    simp_rw [norm_smul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (‖c‖^2)*ENNReal.ofReal (ε/(‖c‖^2+1)) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ = ENNReal.ofReal (‖c‖^2*(ε/(‖c‖^2+1))) := (ENNReal.ofReal_mul (sq_nonneg ‖c‖)).symm
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (‖c‖^2+1)*(ε/(‖c‖^2+1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε := by field_simp

private theorem actual_mixed_good (sharp : Bool) (g k : QuantumTest) (μ : ℝ) (hμ : 0<μ)
    (a b : ℕ) : Good (fun m ell F w => inner ℂ (embed k)
      (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0 (embed g))) := by
  refine ⟨fun m ell F => ?_,actual_mixed_double_tail sharp g k μ hμ a b⟩
  have hc := mixed_split_continuous
    (fun r u v w x => inner ℂ (embed (sourceTest r u k))
      (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F (line μ x) (embed (sourceTest v w g))))
    (fun r u v w => whole_continuous sharp m ell F μ hμ _ _) a b 0 0 0 0
  apply hc.congr
  intro w
  exact ((actual_mixed_endpoint_return sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k a b 0 0).trans (endpoint_origin _ g k a b)).symm

private theorem map_select {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (A : ℕ → ℕ → V) :
    l (SourceGaugeCoframeWard.select A)=SourceGaugeCoframeWard.select (fun a b => l (A a b)) := by
  simp only [SourceGaugeCoframeWard.select,map_add,map_smul]

/-- The complete eight-term ordered Ward polynomial on the actual orbit has a common full-frequency tail. -/
theorem actual_mixed_polynomial_tail (sharp : Bool) (g k : QuantumTest) (μ : ℝ) (hμ : 0<μ) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖inner ℂ (embed k)
          (SourceGaugeCoframeWard.select (fun a b =>
            SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0) (embed g))‖^2)) ≤
          ENNReal.ofReal ε := by
  have hj (a b : ℕ) := actual_mixed_good sharp g k μ hμ a b
  have hp := good_add (good_add (good_add (good_add (good_add (good_add (good_add
    (hj 3 1) (good_smul (hj 2 1) 12)) (good_smul (hj 1 1) 44)) (good_smul (hj 0 1) 48))
      (hj 3 0)) (good_smul (hj 2 0) 12)) (good_smul (hj 1 0) 44)) (good_smul (hj 0 0) 48)
  have he (m ell : ℕ) (F : Index) (w : ℝ) :
      inner ℂ (embed k) (SourceGaugeCoframeWard.select (fun a b =>
        SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0) (embed g))=
      SourceGaugeCoframeWard.select (fun a b => inner ℂ (embed k)
        (SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0 (embed g))) :=
    map_select ((innerSL ℂ (embed k)).comp (ContinuousLinearMap.apply ℂ H (embed g))).toLinearMap
      (fun a b => SourceGaugeCoframeWard.doubleOrbitJet sharp m ell F (line μ w) a b 0 0)
  simp_rw [he]
  simpa only [CofinalTail,SourceGaugeCoframeWard.select] using! hp.2

end LowEnergy.SourceScalarMixedEndpointBudget
