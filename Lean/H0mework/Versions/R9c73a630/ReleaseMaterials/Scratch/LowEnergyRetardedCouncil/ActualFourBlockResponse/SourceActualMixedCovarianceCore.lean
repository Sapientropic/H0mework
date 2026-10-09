import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceTail
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceGram
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedCovarianceTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceClockPhiSecondPressure SourceClockPhiSecondBulk SourceResolventBandLimit FullYSourceResolventGraphSplice
open SourceRelativePowerTail ActualVectorJointCost MeasureTheory Filter
open Lean Meta Elab Term
open scoped InnerProductSpace ENNReal

elab "paid_second_pressure%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure 0) "LowEnergy") "SourceClockPhiSecondPressure"
  let name := Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing original polarized source derivative"
  mkConstWithFreshMVarLevels name

private theorem star_nonreal (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

def coreCovariance (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  resolventCore F (star z) (star_nonreal z hz)*SourceNativeCutoffContact.thetaAction m ell*
    SourceNativeCutoffContact.thetaAction m ell*resolventCore F z hz

private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem window_core (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (SourceNativeCutoffContact.thetaAction m ell (resolventCore F z hz f))=window m ell F z f := by
  rw [SourceNativeCutoffContact.theta_core,core_embed]
  rfl

private theorem resolvent_pair (F : Index) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    sourcePair f (resolventCore F (star z) (star_nonreal z hz) g)=sourcePair (resolventCore F z hz f) g := by
  have h : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
    unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
    rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
    congr 1
    simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
  simp only [sourcePair,core_embed,h]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

/-- The window is the literal original θR core action and its actual formal adjoint. -/
theorem actual_core_covariance_pair (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (f g : QuantumTest) :
    sourcePair f (coreCovariance m ell F z hz g)=inner ℂ (window m ell F z f) (window m ell F z g) := by
  simp only [coreCovariance,Module.End.mul_apply]
  rw [resolvent_pair F z hz]
  have hθ (u v:QuantumTest) : sourcePair u (SourceNativeCutoffContact.thetaAction m ell v)=
      sourcePair (SourceNativeCutoffContact.thetaAction m ell u) v := by
    exact GaussNativeForm.multiply_pair _ _ u v
  rw [hθ]
  simp only [sourcePair,window_core]

/-- The paid mixed read is exactly secondJet on the original returned cutoff covariance. -/
theorem actual_core_covariance_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    (sourcePair g (secondJet (coreCovariance m ell F z hz) g)).re=mixedCovariance m ell F z g := by
  have h:=congrArg (fun P:PairMatrix=>P 1 1)
    ((paid_second_pressure% second_pair_source) g g (coreCovariance m ell F z hz))
  change sourcePair g (secondJet (coreCovariance m ell F z hz) g)=
    secondPair (fun A B=>sourcePair (A g) (coreCovariance m ell F z hz (B g))) 1 1 at h
  simp_rw [actual_core_covariance_pair] at h
  exact congrArg Complex.re h

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- The complete source second variation of R*θ²R has an internally paid absolute
whole-frequency common tail, before the two causal branches are selected. -/
theorem actual_core_covariance_causal_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal |(sourcePair g (secondJet
          (coreCovariance m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w)) g)).re|) ≤
            ENNReal.ofReal ε := by
  simpa only [actual_core_covariance_source] using actual_mixed_covariance_causal_tail μ hμ g

end LowEnergy.ActualMixedCovarianceTail
