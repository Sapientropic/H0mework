import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeNeutralSplice
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceInverseCoframeSpectralReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular SourceEscapeCurrent
open SourceGaugeCoframeWard SourceGaugeCoframeJets FullYSourceResolventGraphSplice
open SourceInverseCoframeCompressionBudget SourceJointResidualEnergy SourceResolventBandLimit
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
abbrev Coeff (F : Index) := Channel F × Channel F → ℂ
attribute [local irreducible] sourceRead sandwichJet readOrbitJet resolventJet diagonalAction

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


def coefficient (F : Index) (A : Op) (f k : H) : Coeff F :=
  fun ij => inner ℂ k (spectralLeg F A f ij)

def decode (F : Index) (μ w : ℝ) : Coeff F →ₗ[ℂ] ℂ where
  toFun c := ∑ ij,polePair μ (channelValue F ij.1) (channelValue F ij.2) w*c ij
  map_add' c d := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    ring

/-- The same two retarded poles carry each original bounded source insertion. -/
theorem actual_decode (F : Index) (μ : ℝ) (hμ : 0<μ) (w : ℝ) (A : Op) (f k : H) :
    inner ℂ k ((finiteResolvent F (line μ w)*A*finiteResolvent F (line μ w)) f)=decode F μ w (coefficient F A f k) := by
  change inner ℂ k (finiteResolvent F (line μ w) (A (finiteResolvent F (line μ w) f)))=_
  rw [actual_two_leg_spectral F μ hμ A f w]
  simp only [inner_sum,inner_smul_right,decode,coefficient,LinearMap.coe_mk,AddHom.coe_mk]

def coframeCoefficient (F : Index) (seed : diagonal.domain) (A : End) : QuantumTest → QuantumTest → ℕ → Coeff F
  | f,k,0 => coefficient F (sourceRead F seed A) (embed f) (embed k)
  | f,k,n+1 => -coframeCoefficient F seed A (K f) k n-coframeCoefficient F seed A f (K k) n

/-- Actual coframe response jets move to fixed source legs; their frequency pole order stays two. -/
theorem actual_coframe_decode (F : Index) (seed : diagonal.domain) (A : End) (μ : ℝ) (hμ : 0<μ)
    (w : ℝ) (n : ℕ) (f k : QuantumTest) :
    coframeProfile F seed (line μ w) A f k n 0=decode F μ w (coframeCoefficient F seed A f k n) := by
  induction n generalizing f k with
  | zero =>
    rw [profile_origin F seed (line μ w) (by simpa only [line_im] using hμ.ne')]
    exact actual_decode F μ hμ w _ _ _
  | succ n ih =>
    rw [profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne'),ih,ih]
    simp only [coframeCoefficient,map_sub,map_neg]

end LowEnergy.SourceInverseCoframeSpectralReturn
