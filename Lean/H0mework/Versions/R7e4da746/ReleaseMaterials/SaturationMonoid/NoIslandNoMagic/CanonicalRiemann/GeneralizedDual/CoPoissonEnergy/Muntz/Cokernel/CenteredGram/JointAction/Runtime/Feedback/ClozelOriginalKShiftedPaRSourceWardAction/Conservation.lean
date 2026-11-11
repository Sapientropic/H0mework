import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKShiftedPaRSourceWardAction.FiniteDebt
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

theorem source_complete_density_zero (shift : ℝ) :
 projectedDebtDensity observation nontrivial half depth ordinal h H N Split.paProjection shift+
 projectedDebtDensity observation nontrivial half depth ordinal h H N Split.unitProjection shift+
 projectedDebtDensity observation nontrivial half depth ordinal h H N Split.outsideProjection shift=0 := by
 have pa := source_projected_norm_derivative observation nontrivial half depth ordinal h H N Split.paProjection shift
 have unit := source_projected_norm_derivative observation nontrivial half depth ordinal h H N Split.unitProjection shift
 have outside := source_projected_norm_derivative observation nontrivial half depth ordinal h H N Split.outsideProjection shift
 have full := (pa.add unit).add outside
 have law : (fun t : ℝ => ‖Split.paProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2+
   ‖Split.unitProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2+
   ‖Split.outsideProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2)=
  (fun _ : ℝ => ‖Energy.sourceR observation nontrivial half depth ordinal h H N‖^2) := by
  funext t
  exact shifted_full_source_budget observation nontrivial half depth ordinal h H N t
 change HasDerivAt (fun t : ℝ => ‖Split.paProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2+
   ‖Split.unitProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2+
   ‖Split.outsideProjection (shiftedR observation nontrivial half depth ordinal h H N t)‖^2)
  (projectedDebtDensity observation nontrivial half depth ordinal h H N Split.paProjection shift+
   projectedDebtDensity observation nontrivial half depth ordinal h H N Split.unitProjection shift+
   projectedDebtDensity observation nontrivial half depth ordinal h H N Split.outsideProjection shift) shift at full
 rw [law] at full
 exact full.unique (hasDerivAt_const shift _)

theorem finite_complete_debt_conservation (left right : ℝ) :
 (∫ t in left..right, projectedDebtDensity observation nontrivial half depth ordinal h H N Split.paProjection t)+
 (∫ t in left..right, projectedDebtDensity observation nontrivial half depth ordinal h H N Split.unitProjection t)+
 (∫ t in left..right, projectedDebtDensity observation nontrivial half depth ordinal h H N Split.outsideProjection t)=0 := by
 rw [← finite_projected_debt,← finite_projected_debt,← finite_projected_debt]
 have before := shifted_full_source_budget observation nontrivial half depth ordinal h H N left
 have after := shifted_full_source_budget observation nontrivial half depth ordinal h H N right
 change ‖Split.paProjection (shiftedR observation nontrivial half depth ordinal h H N left)‖^2+
  ‖Split.unitProjection (shiftedR observation nontrivial half depth ordinal h H N left)‖^2+
  ‖Split.outsideProjection (shiftedR observation nontrivial half depth ordinal h H N left)‖^2=_ at before
 change ‖Split.paProjection (shiftedR observation nontrivial half depth ordinal h H N right)‖^2+
  ‖Split.unitProjection (shiftedR observation nontrivial half depth ordinal h H N right)‖^2+
  ‖Split.outsideProjection (shiftedR observation nontrivial half depth ordinal h H N right)‖^2=_ at after
 linarith

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
