import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentInputEscape
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentGaugeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentProjectionSource
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseFirstCurrentInputEscape SourceInverseFirstCurrentGaugeJets SourceInverseCompressionCurrent
open SourceGaugeCoframeJets SourceGaugeCoframeWard SourceScalarDoubleCurrent SourceJointScaleBudget
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceMixedNativeReturn FullYSourceResolventGraphSplice Filter
abbrev Op := H →L[ℂ] H
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourceRead matterInsertion matterHamiltonianCurrent
  firstProjectionCross firstSourceCorrections responseJet wholeResponse wholeCurrent defectAction
  sandwichJet readOrbitJet resolventJet

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


private def weak (A : ℕ → ℝ → Op) (g k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (A n t (embed g))

set_option backward.isDefEq.respectTransparency.types false in
private theorem weak_derivative (A : ℕ → ℝ → Op)
    (ha : ∀ n t,HasDerivAt (A n) (A (n+1) t) t) (g k : QuantumTest) (n : ℕ) (t : ℝ) :
    HasDerivAt (weak A g k n) (weak A g k (n+1) t) t := by
  have hA := ((ContinuousLinearMap.apply ℂ H (embed g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (ha n t)
  have h := (hasDerivAt_const t (embed k)).inner ℂ hA
  simpa only [inner_zero_left,zero_add,add_zero,weak] using! h

private theorem weak_base (A : ℕ → ℝ → Op) (B : Op)
    (ho : ∀ t,A 0 t=(mixedHilbert 0 t).conjStarAlgEquiv B) (g k : QuantumTest) (t : ℝ) :
    weak A g k 0 t=inner ℂ (embed (SourceGaugeScaleTransport.coreFlow (-t) k))
      (B (embed (SourceGaugeScaleTransport.coreFlow (-t) g))) := by
  rw [weak,ho,orbit_pair]

private theorem weak_first (A : ℕ → ℝ → Op) (B : Op)
    (ha : ∀ n t,HasDerivAt (A n) (A (n+1) t) t)
    (ho : ∀ t,A 0 t=(mixedHilbert 0 t).conjStarAlgEquiv B) (g k : QuantumTest) (t : ℝ) :
    weak A g k 1 t= -weak A (G g) k 0 t-weak A g (G k) 0 t := by
  have h := (pullback_derivative B g k t).congr_of_eventuallyEq
    (Eventually.of_forall (fun s => weak_base A B ho g k s))
  have he := (weak_derivative A ha g k 0 t).unique h
  rw [weak_base A B ho (G g) k t,weak_base A B ho g (G k) t]
  exact he

private theorem weak_second (A : ℕ → ℝ → Op) (B : Op)
    (ha : ∀ n t,HasDerivAt (A n) (A (n+1) t) t)
    (ho : ∀ t,A 0 t=(mixedHilbert 0 t).conjStarAlgEquiv B) (g k : QuantumTest) (t : ℝ) :
    weak A g k 2 t=weak A (G (G g)) k 0 t+2*weak A (G g) (G k) 0 t+weak A g (G (G k)) 0 t := by
  have hd := (weak_derivative A ha (G g) k 0 t).neg.sub (weak_derivative A ha g (G k) 0 t)
  have h := hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => weak_first A B ha ho g k s))
  have he := (weak_derivative A ha g k 1 t).unique h
  rw [weak_first A B ha ho (G g) k t,weak_first A B ha ho g (G k) t] at he
  exact he.trans (by ring)

private theorem weak_origin (A : ℕ → ℝ → Op) (B : Op)
    (ho : ∀ t,A 0 t=(mixedHilbert 0 t).conjStarAlgEquiv B) (g k : QuantumTest) :
    weak A g k 0 0=inner ℂ (embed k) (B (embed g)) := by
  rw [weak_base A B ho]
  simp only [neg_zero,SourceGaugeScaleTransport.coreFlow_zero]

private theorem origin_conjugate (B : Op) : (mixedHilbert 0 0).conjStarAlgEquiv B=B := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (B ((mixedHilbert 0 0).symm x))=B x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem sandwich_map (e : Op ≃⋆ₐ[ℂ] Op) (r a : Op) :
    e r*(e a*e r)=e (r*a*r) := by simp only [map_mul,mul_assoc]
private theorem sub_map (e : Op ≃⋆ₐ[ℂ] Op) (a b c : Op) :
    e a-e b-e c=e (a-b-c) := by simp only [map_sub]

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (t : ℝ) :
    sandwichJet F g z A 0 0 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 0 t*(readOrbitJet F g A 0 0 0 t*resolventJet F z 0 0 0 t)=_
  have hr := actual_mixed_resolvent F z hz 0 t
  have ha := actual_read_orbit F g A 0 t
  exact (congrArg₂ (fun x y : Op => x*y) hr
    (congrArg₂ (fun x y : Op => x*y) ha hr)).trans
      (sandwich_map (mixedHilbert 0 t).conjStarAlgEquiv (finiteResolvent F z) (sourceRead F g A))

private def projectionJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F g z (matterHamiltonianCurrent sharp m ell) 0 n 0 t-responseJet sharp m ell F z n t-
    sandwichJet F g z (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 t

private def baseDifference (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  finiteResolvent F z*sourceRead F g (matterHamiltonianCurrent sharp m ell)*finiteResolvent F z-
    wholeResponse sharp m ell F z-
    finiteResolvent F z*sourceRead F g (bracket (defectAction F) (matterInsertion sharp m ell))*finiteResolvent F z

private theorem projection_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (projectionJet sharp m ell F g z n) (projectionJet sharp m ell F g z (n+1) t) t :=
  ((sandwich_gauge_derivative F g z (matterHamiltonianCurrent sharp m ell) 0 n 0 t).sub
    (actual_response_gauge_derivative sharp m ell F z n t)).sub
      (sandwich_gauge_derivative F g z (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 t)

private theorem projection_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    projectionJet sharp m ell F g z 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (baseDifference sharp m ell F g z) := by
  have hJ := sandwich_orbit F g z hz (matterHamiltonianCurrent sharp m ell) t
  have hQ := actual_response_orbit sharp m ell F z hz t
  have hD := sandwich_orbit F g z hz (bracket (defectAction F) (matterInsertion sharp m ell)) t
  exact (congrArg₂ (fun x y : Op => x-y) (congrArg₂ (fun x y : Op => x-y) hJ hQ) hD).trans
    (sub_map (mixedHilbert 0 t).conjStarAlgEquiv _ _ _)

private theorem cancel_escape {R : Type*} [Ring R] (r d a p : R) :
    r*(d-a*p)*r-r*d*r= -(r*a*p*r) := by noncomm_ring

private theorem base_difference (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    baseDifference sharp m ell F g z=
      -(finiteResolvent F z*wholeCurrent sharp m ell F*(1-(inputSpan F g).starProjection)*finiteResolvent F z) := by
  have hJ := (sandwich_orbit F g z hz (matterHamiltonianCurrent sharp m ell) 0).trans (origin_conjugate _)
  have hQ := (actual_response_orbit sharp m ell F z hz 0).trans (origin_conjugate _)
  have hp := actual_first_projection_origin sharp m ell F g z hz
  have hret : firstProjectionCross sharp m ell F g z 0=
      finiteResolvent F z*sourceRead F g (matterHamiltonianCurrent sharp m ell)*finiteResolvent F z-wholeResponse sharp m ell F z := by
    unfold firstProjectionCross
    exact congrArg₂ (fun x y : Op => x-y) hJ hQ
  have hp0 := hret.symm.trans hp
  exact (congrArg (fun A : Op => A-finiteResolvent F z*
      sourceRead F g (bracket (defectAction F) (matterInsertion sharp m ell))*finiteResolvent F z) hp0).trans
    (cancel_escape _ _ _ _)

/-- Fixed right source support pays every escaped-input leaf of the actual zero/first/second gauge response.
    The genuine Hamiltonian defects remain as their own complete sandwich jets. -/
theorem actual_first_projection_weak_source (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp m ell,∀ z : ℂ,∀ _hz : z.im≠0,
      ∀ k : QuantumTest,∀ n : Fin 3,
      inner ℂ (embed k) (firstProjectionCross sharp m ell F g z n (g : H))=
        inner ℂ (embed k) (sandwichJet F g z
          (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 0 (g : H)) := by
  filter_upwards [actual_gauge_prefix_escape_zero g] with F hF sharp m ell z hz k n
  let A := projectionJet sharp m ell F g z
  let B := baseDifference sharp m ell F g z
  have ha := projection_derivative sharp m ell F g z
  have ho := projection_orbit sharp m ell F g z hz
  have hzero (l : QuantumTest) (j : Fin 3) :
      weak A ((G^j.val) (coreEquiv.symm g)) l 0 0=0 := by
    rw [weak_origin A B ho]
    dsimp only [B]
    rw [base_difference sharp m ell F g z hz,neg_apply,inner_neg_right]
    rw [hF z hz (wholeCurrent sharp m ell F) (embed l) j,neg_zero]
  have h0 (l : QuantumTest) : weak A (coreEquiv.symm g) l 0 0=0 := by simpa using hzero l 0
  have h1 (l : QuantumTest) : weak A (G (coreEquiv.symm g)) l 0 0=0 := by simpa using hzero l 1
  have h2 (l : QuantumTest) : weak A (G (G (coreEquiv.symm g))) l 0 0=0 := by
    have h := hzero l 2
    change weak A ((G^2) (coreEquiv.symm g)) l 0 0=0 at h
    simpa only [pow_two,Module.End.mul_apply] using h
  have hj : weak A (coreEquiv.symm g) k n.val 0=0 := by
    fin_cases n
    · exact h0 k
    · rw [weak_first A B ha ho,h1,h0,neg_zero,sub_self]
    · rw [weak_second A B ha ho,h2,h1,h0,mul_zero,add_zero,add_zero]
  have hcore : embed (coreEquiv.symm g)=(g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  simp only [weak,A,projectionJet,hcore,sub_apply,inner_sub_right] at hj
  rw [firstProjectionCross,sub_apply,inner_sub_right]
  exact sub_eq_zero.mp hj

/-- Density of the original source core upgrades the same cofinal identity to the actual Hilbert vector,
    so every later reader consumes the same returned state. -/
theorem actual_first_projection_source (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp m ell,∀ z : ℂ,∀ _hz : z.im≠0,∀ n : Fin 3,
      firstProjectionCross sharp m ell F g z n (g : H)=
        sandwichJet F g z (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 0 (g : H) := by
  filter_upwards [actual_first_projection_weak_source g] with F h sharp m ell z hz n
  apply ext_inner_left ℂ
  intro k
  exact SourceCoframeScaleTransport.embed_dense.induction_on k
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun l => h sharp m ell z hz l n)

end LowEnergy.SourceInverseFirstCurrentProjectionSource
