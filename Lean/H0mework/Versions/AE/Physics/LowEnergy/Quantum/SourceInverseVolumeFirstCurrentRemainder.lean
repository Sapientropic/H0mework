import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentGaugeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentRemainder
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open Filter
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] GaussDiagonalHistory.diagonalAction sourceRead
  matterInsertion matterHamiltonianCurrent state sourcePair defectAction compressionCore
  SourceScalarDoubleCurrent.fullInsertion SourceScalarDoubleCurrent.electricMatterCurrent
  SourceScalarGaugeScale.deltaGauge SourceHamiltonianScaleJet.scaleDerivative
  SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction cutoffEuler scaleDoubleRemainder constantAction
  SourceScalarForceBudget.solverOperator SourceScalarForceBudget.oscillatorMass
  SourceGaugeCoframeWard.wardOperator wholeCurrent wholeResponse responseJet readOrbitJet

/-- The linear commutator with the complete original graded compression defect. -/
def linearDefectJet (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F seed z (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 t

/-- A common-carrier difference, whose source origin is the escaped input of the whole current. -/
def inputShadowJet (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  linearDefectJet sharp m ell F seed z n t-
    sandwichJet F seed z (matterHamiltonianCurrent sharp m ell) 0 n 0 t+
      responseJet sharp m ell F z n t

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

private theorem sandwich_orbit (F : Index) (seed : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : End) (t : ℝ) :
    sandwichJet F seed z A 0 0 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) := by
  change resolventJet F z 0 0 0 t*(readOrbitJet F seed A 0 0 0 t*resolventJet F z 0 0 0 t)=_
  have h := congrArg₂ (fun r b : Op => r*(b*r))
    (actual_mixed_resolvent F z hz 0 t) (actual_read_orbit F seed A 0 t)
  exact h.trans (by simp only [map_mul,mul_assoc])

/-- The new shadow is exactly the escaped-input part of the original whole first current. -/
theorem actual_shadow_origin (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    inputShadowJet sharp m ell F seed z 0 0=
      finiteResolvent F z*wholeCurrent sharp m ell F*(1-(inputSpan F seed).starProjection)*
        finiteResolvent F z := by
  have ho := actual_first_projection_origin sharp m ell F seed z hz
  have hd := (sandwich_orbit F seed z hz
    (bracket (defectAction F) (matterInsertion sharp m ell)) 0).trans (origin_conjugate _)
  have hs : inputShadowJet sharp m ell F seed z 0 0=
      linearDefectJet sharp m ell F seed z 0 0-firstProjectionCross sharp m ell F seed z 0 := by
    simp only [inputShadowJet,firstProjectionCross]
    abel
  rw [hs,ho]
  unfold linearDefectJet
  rw [hd]
  simp only [mul_sub,sub_mul,mul_assoc]
  abel

private theorem shadow_derivative (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (inputShadowJet sharp m ell F seed z n)
      (inputShadowJet sharp m ell F seed z (n+1) t) t :=
  ((sandwich_gauge_derivative F seed z
    (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 t).sub
    (sandwich_gauge_derivative F seed z (matterHamiltonianCurrent sharp m ell) 0 n 0 t)).add
    (actual_response_gauge_derivative sharp m ell F z n t)

private theorem map_join {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (a b c : R) :
    e a-e b+e c=e (a-b+c) := by simp only [map_add,map_sub]

private theorem shadow_orbit (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    inputShadowJet sharp m ell F seed z 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (inputShadowJet sharp m ell F seed z 0 0) := by
  have h (s : ℝ) : inputShadowJet sharp m ell F seed z 0 s=
      (mixedHilbert 0 s).conjStarAlgEquiv
        (finiteResolvent F z*sourceRead F seed
          (bracket (defectAction F) (matterInsertion sharp m ell))*finiteResolvent F z-
          finiteResolvent F z*sourceRead F seed (matterHamiltonianCurrent sharp m ell)*finiteResolvent F z+
          wholeResponse sharp m ell F z) := by
    have hD := sandwich_orbit F seed z hz
      (bracket (defectAction F) (matterInsertion sharp m ell)) s
    have hH := sandwich_orbit F seed z hz (matterHamiltonianCurrent sharp m ell) s
    have hC := actual_response_orbit sharp m ell F z hz s
    exact (congrArg₂ (fun a b : Op => a+b)
      (congrArg₂ (fun a b : Op => a-b) hD hH) hC).trans
      (map_join (mixedHilbert 0 s).conjStarAlgEquiv _ _ _)
  exact (h t).trans (congrArg (mixedHilbert 0 t).conjStarAlgEquiv ((h 0).trans (origin_conjugate _)).symm)

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

private theorem weak_second (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert 0 t).conjStarAlgEquiv (J 0 0))
    (g k : QuantumTest) (t : ℝ) :
    weakJet J g k 2 t=weakJet J (G (G g)) k 0 t+
      2*weakJet J (G g) (G k) 0 t+weakJet J g (G (G k)) 0 t := by
  have hd := (weak_derivative J hJ (G g) k 0 t).neg.sub (weak_derivative J hJ g (G k) 0 t)
  have h := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (weak_first J hJ hO g k))
  have hu := (weak_derivative J hJ g k 1 t).unique h
  rw [weak_first J hJ hO (G g) k,weak_first J hJ hO g (G k)] at hu
  exact hu.trans (by ring)

private theorem filter_pair (J : ℕ → Op) (g k : QuantumTest) :
    inner ℂ (embed k) (gaugeFilter J (embed g))=
      gaugeFilter (fun n => inner ℂ (embed k) (J n (embed g))) := by
  let L : Op →L[ℂ] ℂ := (innerSL ℂ (embed k)).comp (ContinuousLinearMap.apply ℂ H (embed g))
  change L (gaugeFilter J)=gaugeFilter (fun n => L (J n))
  simp only [gaugeFilter,map_add,map_sub,map_smul]

private theorem shadow_on_support (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (f : QuantumTest)
    (hf : embed f∈supportSpan F) : inputShadowJet sharp m ell F seed z 0 0 (embed f)=0 := by
  have hp : (inputSpan F seed).starProjection (finiteResolvent F z (embed f))=
      finiteResolvent F z (embed f) :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_sup_left (resolvent_mem_support F z hz _ hf))
  rw [actual_shadow_origin sharp m ell F seed z hz]
  change finiteResolvent F z (wholeCurrent sharp m ell F
    (finiteResolvent F z (embed f)-(inputSpan F seed).starProjection (finiteResolvent F z (embed f))))=0
  rw [hp,sub_self,map_zero,map_zero]

/-- Three fixed original inputs eliminate every gauge-filtered first-current shadow on one cofinal set. -/
theorem actual_shadow_filter_zero (seed : diagonal.domain) (g k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (m ell : ℕ) (z : ℂ), z.im≠0 →
      inner ℂ (embed k) (gaugeFilter (fun n => inputShadowJet sharp m ell F seed z n 0) (embed g))=0 := by
  filter_upwards [source_eventually_mem_support (coreEquiv g),
    source_eventually_mem_support (coreEquiv (G g)),source_eventually_mem_support (coreEquiv (G (G g)))]
    with F h0 h1 h2
  intro sharp m ell z hz
  let J := inputShadowJet sharp m ell F seed z
  have hz0 (f h : QuantumTest) (hf : embed f∈supportSpan F) : weakJet J f h 0 0=0 := by
    unfold weakJet
    rw [shadow_on_support sharp m ell F seed z hz f hf,inner_zero_right]
  rw [filter_pair,gaugeFilter]
  change weakJet J g k 2 0-(3 : ℂ) • weakJet J g k 1 0+(2 : ℂ) • weakJet J g k 0 0=0
  rw [weak_second J (shadow_derivative sharp m ell F seed z) (shadow_orbit sharp m ell F seed z hz),
    weak_first J (shadow_derivative sharp m ell F seed z) (shadow_orbit sharp m ell F seed z hz)]
  rw [hz0 (G (G g)) k h2,hz0 (G g) (G k) h1,hz0 g (G (G k)) h0,
    hz0 (G g) k h1,hz0 g (G k) h0,hz0 g k h0]
  simp

/-- The joined original signed remainder after the escaped input has been eliminated. -/
def linearRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (gaugeFilter (fun n => linearDefectJet sharp m ell F seed z n 0)-
    gaugeFilter (fun n => inverseCross F seed z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F seed (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z)+finiteResolvent F z*remainingForces sharp m ell F seed*finiteResolvent F z

private theorem joint_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) :
    (1/6 : ℂ) • firstSourceCorrections sharp m ell F seed z+
      finiteResolvent F z*remainingForces sharp m ell F seed*finiteResolvent F z=
      linearRemainder sharp m ell F seed z-
        (1/6 : ℂ) • gaugeFilter (fun n => inputShadowJet sharp m ell F seed z n 0) := by
  simp only [firstSourceCorrections,linearRemainder,gaugeFilter,inputShadowJet,firstProjectionCross]
  module

/-- The whole original Ward response retains one signed source remainder; its new input-shadow is exactly gone. -/
theorem actual_ward_linear_remainder (seed : diagonal.domain) (g k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (sharp : Bool) (m ell : ℕ) (z : ℂ), z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F seed z (embed g))=
        (1/6 : ℂ)*filteredProfile sharp m ell F z g k+
          inner ℂ (embed k) (linearRemainder sharp m ell F seed z (embed g)) := by
  filter_upwards [actual_shadow_filter_zero seed g k] with F hF
  intro sharp m ell z hz
  have ho := actual_complete_ward_reduction sharp m ell F seed z hz
  have hs := joint_split sharp m ell F seed z
  let R := finiteResolvent F z
  have hj : wardOperator sharp m ell F seed z=
      (1/6 : ℂ) • gaugeFilter (fun n => responseJet sharp m ell F z n 0)+
      linearRemainder sharp m ell F seed z-
      (1/6 : ℂ) • gaugeFilter (fun n => inputShadowJet sharp m ell F seed z n 0) := by
    linear_combination (norm := module) ho+hs
  rw [hj]
  simp only [add_apply,sub_apply,smul_apply,inner_add_right,inner_sub_right,inner_smul_right,
    hF sharp m ell z hz,mul_zero,sub_zero]
  congr 1
  exact congrArg (fun a : ℂ => (1/6 : ℂ)*a) (filter_pair _ g k)

end LowEnergy.SourceInverseFirstCurrentRemainder
