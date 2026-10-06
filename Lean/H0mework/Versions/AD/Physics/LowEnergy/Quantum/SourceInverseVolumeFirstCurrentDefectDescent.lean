import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentProjectionReturn
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeSourceJetEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentDefectDescent
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarDoubleCurrent
open SourceInverseJetEnergy FullYSourceResolventGraphSplice Filter
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction compressionCore defectAction state
  GaussAdjointHistory.coreStep GaussAdjointHistory.iterate

private theorem fixed_defect (f : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),defectAction F f=0 := by
  filter_upwards [GaussGradedCompression.eventually_exact (coreEquiv f)] with F hF
  have hd : diagonal (coreEquiv f)=embed (diagonalAction f) := by
    change embed (diagonalAction (coreEquiv.symm (coreEquiv f)))=embed (diagonalAction f)
    rw [coreEquiv.symm_apply_apply]
  change GaussGradedCompression.compression F (embed f)=diagonal (coreEquiv f) at hF
  rw [hd] at hF
  have hc : embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
    unfold compressionCore
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  apply embed_injective
  rw [map_zero,defectAction,LinearMap.sub_apply,map_sub,hc,hF,sub_self]

/-- Both fixed source tests are paid by the same source-generated compression; the moving state is untouched. -/
theorem actual_fixed_commutator_zero (A : End) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),bracket (defectAction F) A (coreEquiv.symm g)=0 := by
  filter_upwards [fixed_defect (coreEquiv.symm g),fixed_defect (A (coreEquiv.symm g))] with F hg hAg
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,hg,hAg,map_zero,sub_self]

/-- The complete true-defect current on the actual retarded source has an exact frequency/source update. -/
theorem actual_retarded_defect_step (A : End) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ,∀ hz : z.im≠0,
      z • bracket (defectAction F) A (state F z hz g)=
        bracket (defectAction F) A (state F z hz (GaussAdjointHistory.coreStep g)) := by
  filter_upwards [actual_source_step g,actual_fixed_commutator_zero A g] with F hs hz0 z hz
  have h := congrArg (fun q : QuantumTest => bracket (R := End) (defectAction F) A q) (hs z hz)
  simpa only [map_smul,map_sub,hz0,sub_zero] using h

private theorem iterate_next (r : ℕ) (g : diagonal.domain) :
    GaussAdjointHistory.coreStep (GaussAdjointHistory.iterate r g)=GaussAdjointHistory.iterate (r+1) g := by
  simp only [GaussAdjointHistory.iterate,pow_succ',Module.End.mul_apply]

/-- At each finite depth one common F precedes every nonreal frequency; no terminal bound or analytic-jet growth is assumed. -/
theorem actual_retarded_defect_descent (A : End) (r : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ,∀ hz : z.im≠0,
      z^r • bracket (defectAction F) A (state F z hz g)=
        bracket (defectAction F) A (state F z hz (GaussAdjointHistory.iterate r g)) := by
  induction r with
  | zero =>
    filter_upwards [] with F z hz
    simp only [pow_zero,one_smul,GaussAdjointHistory.iterate,Module.End.one_apply]
  | succ r ih =>
    filter_upwards [ih,actual_retarded_defect_step A (GaussAdjointHistory.iterate r g)] with F hr hs z hz
    rw [pow_succ',mul_smul,hr z hz,hs z hz,iterate_next]
end LowEnergy.SourceInverseFirstCurrentDefectDescent
