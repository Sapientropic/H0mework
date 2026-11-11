import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalPaUpdate.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCompressedRSourceKernel.Kernel

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance inverseComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Paid
export OriginalKPaCompressedRSourceKernel
 (PaSourceCarrier compressedR unitRankResponse source_original_unit_rank compressed_full_energy
  compressed_source_injective compressed_source_full_cost_bound)
end Paid
namespace Previous
export OriginalKDirectRCofinalDivision (sourceCoefficient sourceUnit)
end Previous
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def actualPaSource : Paid.PaSourceCarrier :=
 ⟨PA.actualPa observation nontrivial half depth ordinal,
  PA.actualPa_mem observation nontrivial half depth ordinal⟩

def forcedPaSource : BurnolPaAmbientCarrier :=
 PA.actualPa observation nontrivial half depth (ordinal+1)-
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))

/-- The original compression reads this source's actual next Pa after paying its own complete re-entry. -/
theorem actual_compressed_Pa_source :
 Paid.compressedR observation nontrivial half (actualPaSource observation nontrivial half depth ordinal)=
 forcedPaSource observation nontrivial half depth ordinal := by
 have generated:=OriginalKCombCofinalPaAction.actual_defect_value observation nontrivial half depth ordinal
 change PA.actualPa observation nontrivial half depth (ordinal+1)-
  Paid.compressedR observation nontrivial half (actualPaSource observation nontrivial half depth ordinal)=
  PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))) at generated
 apply eq_sub_iff_add_eq.mpr
 exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp generated).symm

theorem actual_forced_Pa_complete_source :
 forcedPaSource observation nontrivial half depth ordinal=
 sourceCorrection observation nontrivial half depth ordinal+
 Previous.sourceCoefficient observation nontrivial half depth ordinal •
  PA.E (sourceWholeUnit observation nontrivial half : BurnolL2) := by
 have generated:=congrArg (fun material : BurnolPaAmbientCarrier=>material-
  PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))))
  (actual_Pa_source_successor observation nontrivial half depth ordinal)
 simpa only [forcedPaSource,add_sub_cancel_right] using generated

theorem actual_original_unit_rank :
 Paid.unitRankResponse observation nontrivial half (actualPaSource observation nontrivial half depth ordinal)=
 Previous.sourceCoefficient observation nontrivial half depth ordinal • Previous.sourceUnit observation nontrivial half := by
 exact Paid.source_original_unit_rank observation nontrivial half (actualPaSource observation nontrivial half depth ordinal)

/-- The existing whole-Pa energy is consumed at the exact cofinal source; neither a Q margin nor positivity is supplied by the caller. -/
theorem actual_forced_Pa_full_energy :
 -(inner ℂ (forcedPaSource observation nontrivial half depth ordinal)
  (PA.actualPa observation nontrivial half depth ordinal)).re=
 (observation.coordinate/2-1/4).re *
  (‖forcedPaSource observation nontrivial half depth ordinal‖^2+
   ‖Previous.sourceCoefficient observation nontrivial half depth ordinal • Previous.sourceUnit observation nontrivial half‖^2) := by
 have generated:=Paid.compressed_full_energy observation nontrivial half
  (actualPaSource observation nontrivial half depth ordinal)
 rw [actual_compressed_Pa_source,actual_original_unit_rank] at generated
 exact generated

/-- This is a mathematical inverse fibre of the generated action, with no identification of runtime occurrences. -/
theorem actual_forced_Pa_inverse (candidate : Paid.PaSourceCarrier)
 (produces : Paid.compressedR observation nontrivial half candidate=forcedPaSource observation nontrivial half depth ordinal) :
 candidate=actualPaSource observation nontrivial half depth ordinal :=
 Paid.compressed_source_injective observation nontrivial half
  (produces.trans (actual_compressed_Pa_source observation nontrivial half depth ordinal).symm)

theorem actual_forced_Pa_full_cost_bound :
 (observation.coordinate/2-1/4).re *
  (‖forcedPaSource observation nontrivial half depth ordinal‖^2+
   ‖Previous.sourceCoefficient observation nontrivial half depth ordinal • Previous.sourceUnit observation nontrivial half‖^2)≤
 ‖forcedPaSource observation nontrivial half depth ordinal‖ * ‖PA.actualPa observation nontrivial half depth ordinal‖ := by
 have generated:=Paid.compressed_source_full_cost_bound observation nontrivial half
  (actualPaSource observation nontrivial half depth ordinal)
 rw [actual_compressed_Pa_source,actual_original_unit_rank] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
