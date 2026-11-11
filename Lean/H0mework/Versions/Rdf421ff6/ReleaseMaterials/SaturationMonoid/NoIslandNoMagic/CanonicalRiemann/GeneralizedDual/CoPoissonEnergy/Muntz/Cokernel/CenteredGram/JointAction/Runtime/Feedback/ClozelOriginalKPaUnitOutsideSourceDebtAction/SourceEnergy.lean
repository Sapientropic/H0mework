import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open Complex BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

theorem actual_split_source_read (shift : ℝ) :
 actualSplitSource observation nontrivial half depth ordinal h H N radius shift=
 splitProjection (burnolMultiplicativeDilation (-shift/2) (Energy.sourceR observation nontrivial half depth ordinal h H N)) := by
 change splitProjection (burnolMultiplicativeDilation (-shift/2)
  (sourceRRead (actualSourceMaterial observation nontrivial half depth ordinal h H N radius)))=_
 rw [actual_source_r_read]

theorem actual_Pa_norm_debit :
 HasDerivAt (fun t : ℝ => ‖(actualSplitSource observation nontrivial half depth ordinal h H N radius t).1.1‖^2)
  (-(2*(observation.coordinate/2-1/4).re*‖Energy.sourceRankCoefficient observation nontrivial half depth ordinal h H N • Energy.originalUnitRank observation nontrivial half‖^2)) 0 := by
 have action := source_Pa_norm_debit observation nontrivial half depth ordinal h H N
 have same : (fun t : ℝ => (actualSplitSource observation nontrivial half depth ordinal h H N radius t).1.1)=
  (fun t : ℝ => paProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))) := by
  funext t
  rw [actual_split_source_read]
  rfl
 simp_rw [show ∀ t, _ = _ from fun t => congrFun same t]
 exact action

theorem actual_unit_norm_credit :
 HasDerivAt (fun t : ℝ => ‖(actualSplitSource observation nontrivial half depth ordinal h H N radius t).1.2‖^2)
  (2*(observation.coordinate/2-1/4).re*‖Energy.sourceRankCoefficient observation nontrivial half depth ordinal h H N • Energy.originalUnitRank observation nontrivial half‖^2) 0 := by
 have action := source_unit_norm_credit observation nontrivial half depth ordinal h H N
 have same : (fun t : ℝ => (actualSplitSource observation nontrivial half depth ordinal h H N radius t).1.2)=
  (fun t : ℝ => unitProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))) := by
  funext t
  rw [actual_split_source_read]
  rfl
 simp_rw [show ∀ t, _ = _ from fun t => congrFun same t]
 exact action

theorem actual_outside_norm_zero_slope :
 HasDerivAt (fun t : ℝ => ‖(actualSplitSource observation nontrivial half depth ordinal h H N radius t).2.1‖^2) 0 0 := by
 have action := source_outside_norm_zero_slope observation nontrivial half depth ordinal h H N
 have same : (fun t : ℝ => (actualSplitSource observation nontrivial half depth ordinal h H N radius t).2.1)=
  (fun t : ℝ => outsideProjection (burnolMultiplicativeDilation (-t/2) (Energy.sourceR observation nontrivial half depth ordinal h H N))) := by
  funext t
  rw [actual_split_source_read]
  rfl
 simp_rw [show ∀ t, _ = _ from fun t => congrFun same t]
 exact action

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
