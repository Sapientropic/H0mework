import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceKineticTranspose
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceRetardedForcingTail

/-! The fixed original source jet removes the spectral factor in the actual outer resolvent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceRetardedSourceJet
open Filter GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice

private theorem finite_source_jet (F : Index) (z : ℂ) (hz : z.im≠0)
    (A : H →L[ℂ] H) (g : H) :
    z • finiteResolvent F z (A (finiteResolvent F z g))=
      finiteResolvent F z (A (finiteResolvent F z (GaussGradedCompression.compression F g)))-
        finiteResolvent F z (A g) := by
  have h := congrArg (fun T : H →L[ℂ] H => T g)
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F g)=g+z • finiteResolvent F z g at h
  rw [h,map_add,map_smul,map_add,map_smul]
  abel

/-- The cofinal threshold depends only on the original input, not on the cutoff map or frequency. -/
theorem actual_source_jet (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ _hz : z.im≠0, ∀ A : H →L[ℂ] H,
      z • finiteResolvent F z (A (finiteResolvent F z (g : H)))=
        finiteResolvent F z (A (finiteResolvent F z (diagonal g)))-
          finiteResolvent F z (A (g : H)) := by
  filter_upwards [GaussGradedCompression.eventually_exact g] with F hF
  intro z hz A
  rw [←hF]
  exact finite_source_jet F z hz A (g : H)

/-- The weak equation remains explicit; the actual outer residual is retained in full. -/
theorem actual_weak_splice_jet (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      ∀ A : H →L[ℂ] H, ∀ f : H,
      (∀ x : diagonal.domain, inner ℂ (SourceKineticTranspose.kinetic x)
        (A (finiteResolvent F z (g : H)))=inner ℂ (x : H) f) →
      inner ℂ (k : H) (finiteResolvent F z f)=
        inner ℂ (k : H) (A (finiteResolvent F z (g : H))+
          (finiteResolvent F z (A (finiteResolvent F z (diagonal g)))-
            finiteResolvent F z (A (g : H))))+
        inner ℂ (SourceKineticTranspose.outerResidual F (star z)
          (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
          (A (finiteResolvent F z (g : H))) := by
  filter_upwards [actual_source_jet g] with F hF
  intro z hz A f hweak
  have h := SourceKineticTranspose.actual_weak_splice F z hz k f
    (A (finiteResolvent F z (g : H))) hweak
  rw [hF z hz A] at h
  exact h

end LowEnergy.SourceRetardedSourceJet
