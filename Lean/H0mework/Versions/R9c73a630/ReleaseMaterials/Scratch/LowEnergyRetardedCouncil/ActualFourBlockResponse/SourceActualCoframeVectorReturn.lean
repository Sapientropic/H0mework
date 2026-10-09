import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeCoframeNeutralSplice
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualCoframeVectorReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceGaugeCoframeJets SourceGaugeCoframeWard SourceInverseCoframeNeutralSplice
open SourceInverseCoframeCompressionBudget FullYSourceResolventGraphSplice
open SourceMixedNativeReturn
open SourceMinimalGraphParticular SourceEscapeCurrent
open SourceJointScaleBudget SourceResolventBandLimit MeasureTheory
open scoped InnerProductSpace ENNReal
abbrev Op := H →L[ℂ] H
attribute [local irreducible] sourceRead finiteResolvent

private theorem sandwich_orbit (F : Index) (seed : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : QuantumTest →ₗ[ℂ] QuantumTest) (s : ℝ) :
    sandwichJet F seed z A 0 0 s 0=(mixedHilbert s 0).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) := by
  change resolventJet F z 0 0 s 0*(readOrbitJet F seed A 0 0 s 0*resolventJet F z 0 0 s 0)=_
  have hr := actual_mixed_resolvent F z hz s 0
  have ha := actual_read_orbit F seed A s 0
  have h := congrArg₂ (fun r a : Op => r*(a*r)) hr ha
  exact h.trans (by simp only [map_mul,mul_assoc])

attribute [local irreducible] sandwichJet resolventJet readOrbitJet neutralDefect
  hamiltonianCoframeCorrection correctedCoframeCompressionJet

private theorem mixed_zero (x : H) : mixedHilbert 0 0 x=x := by
  simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
    SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]

private theorem sandwich_zero (F : Index) (seed : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : QuantumTest →ₗ[ℂ] QuantumTest) :
    sandwichJet F seed z A 0 0 0 0=finiteResolvent F z*sourceRead F seed A*finiteResolvent F z := by
  rw [sandwich_orbit F seed z hz]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 ((finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) ((mixedHilbert 0 0).symm x))=_
  rw [mixed_zero]
  congr 1
  apply (mixedHilbert 0 0).injective
  rw [LinearIsometryEquiv.apply_symm_apply,mixed_zero]

/-- The full actual force, inverse and input corrections remain in one vector. -/
def forceReturn (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (z : ℂ) (g : QuantumTest) : H :=
  (finiteResolvent F z*sourceRead F seed (neutralCoframeForce sharp m ell)*finiteResolvent F z+
    hamiltonianCoframeCorrection sharp m ell F seed z 1-
    correctedCoframeCompressionJet sharp m ell F seed z 0 0) (embed g)+
  (finiteResolvent F z*sourceRead F seed (neutralDefect sharp m ell F)*finiteResolvent F z) (embed (K g))

private theorem orbit_coercive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (a : ℝ) (hd : HasDerivAt f v 0) (hn : ∀ t,‖f t‖≤‖f 0‖) :
    a*‖f 0‖≤‖v+a • f 0‖ := by
  obtain ⟨l,hl,hx⟩ := exists_dual_vector'' ℝ (f 0)
  have hmax : IsLocalMax (fun t => l (f t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change l (f t)≤l (f 0)
    rw [hx]
    exact (le_abs_self _).trans ((l.le_opNorm _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hl).trans (hn t)))
  have hv := hmax.hasDerivAt_eq_zero (l.hasFDerivAt.comp_hasDerivAt 0 hd)
  have hb := (le_abs_self (l (v+a • f 0))).trans ((l.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hl))
  simpa [hv,hx] using hb

private theorem conjugate_norm_le (U : H ≃ₗᵢ[ℂ] H) (B : Op) :
    ‖U.conjStarAlgEquiv B‖≤‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using B.le_opNorm (U.symm x)

/-- No finite input jet is discarded: this is the full operator RHS of the original coframe equation. -/
def forceOperator (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  finiteResolvent F z*sourceRead F seed (neutralCoframeForce sharp m ell)*finiteResolvent F z+
    hamiltonianCoframeCorrection sharp m ell F seed z 1-
    correctedCoframeCompressionJet sharp m ell F seed z 0 0

/-- The gain comes from the original coframe orbit on the whole bounded source read. -/
theorem actual_sandwich_shift_price (F : Index) (seed : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : QuantumTest →ₗ[ℂ] QuantumTest) (n : ℕ) :
    (n:ℝ)*‖finiteResolvent F z*sourceRead F seed A*finiteResolvent F z‖≤
      ‖sandwichJet F seed z A 1 0 0 0+
        (n:ℂ) • (finiteResolvent F z*sourceRead F seed A*finiteResolvent F z)‖ := by
  have h := orbit_coercive (fun s=>sandwichJet F seed z A 0 0 s 0)
    (sandwichJet F seed z A 1 0 0 0) (n:ℝ)
    (sandwich_coframe_derivative F seed z A 0 0 0 0) (by
      intro s
      rw [sandwich_orbit F seed z hz,sandwich_zero F seed z hz]
      exact conjugate_norm_le _ _)
  have hreal (B:Op) : (n:ℝ) • B=(n:ℂ) • B :=
    (Nat.cast_smul_eq_nsmul ℝ n B).trans (Nat.cast_smul_eq_nsmul ℂ n B).symm
  simpa only [hreal,sandwich_zero F seed z hz] using h

/-- Actual source conjugation pays the positive factor three without a reader or a reindexed F. -/
theorem actual_neutral_operator_price (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    3*‖finiteResolvent F z*sourceRead F seed (neutralDefect sharp m ell F)*finiteResolvent F z‖≤
      ‖forceOperator sharp m ell F seed z‖ := by
  have h:=actual_sandwich_shift_price F seed z hz (neutralDefect sharp m ell F) 3
  have hf:=actual_neutral_corrected_coframe sharp m ell F seed z hz
  rw [sandwich_zero F seed z hz] at hf
  simpa only [Nat.cast_ofNat,hf,forceOperator] using h

private theorem vector_price (B Q : Op) (h : 3*‖B‖≤‖Q‖) (g : H) :
    9*‖B g‖^2≤‖Q‖^2*‖g‖^2 := by
  have hp:=B.le_opNorm g
  have hm:=mul_le_mul_of_nonneg_right h (norm_nonneg g)
  have hlin:3*‖B g‖≤‖Q‖*‖g‖ := by nlinarith only [hp,hm]
  have hs:=(sq_le_sq₀ (by positivity : 0≤3*‖B g‖) (by positivity : 0≤‖Q‖*‖g‖)).mpr hlin
  nlinarith only [hs]

/-- The same whole operator return controls every original Hilbert output simultaneously. -/
theorem actual_neutral_vector_price (sharp : Bool) (m ell : ℕ) (F : Index)
    (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (g : H) :
    9*‖(finiteResolvent F z*sourceRead F seed (neutralDefect sharp m ell F)*finiteResolvent F z) g‖^2≤
      ‖forceOperator sharp m ell F seed z‖^2*‖g‖^2 := by
  exact vector_price _ _ (actual_neutral_operator_price sharp m ell F seed z hz) g

end LowEnergy.ActualCoframeVectorReturn
