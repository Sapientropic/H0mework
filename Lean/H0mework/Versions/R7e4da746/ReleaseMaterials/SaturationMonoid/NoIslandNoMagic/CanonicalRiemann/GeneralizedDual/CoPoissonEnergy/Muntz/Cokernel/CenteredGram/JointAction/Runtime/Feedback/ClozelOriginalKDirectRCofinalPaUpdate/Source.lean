import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.Price

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance sourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Parent
export OriginalKDirectRCofinalDivision
 (sourceResponse sourceCoefficient source_response_value actual_R_source_split)
end Parent
namespace PA
export OriginalKCombCofinalPaAction (actualPa actualPa_mem E invisible)
end PA
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def sourceWholeUnit : BurnolPaAmbientCarrier :=
 burnolZeroOwnedUnitTailState observation nontrivial half.down

def sourceCorrection : BurnolPaAmbientCarrier :=
 Parent.sourceResponse observation nontrivial half depth ordinal-
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
 sourceWholeUnit observation nontrivial half

/-- The original Division producer qualifies its complete correction, before either E or Q is read. -/
theorem source_correction_memPa :
 sourceCorrection observation nontrivial half depth ordinal∈burnolCompactCoPoissonClosedRange := by
 have belongs:=burnolPaResolvent_source_correction
  (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (PA.actualPa observation nontrivial half depth ordinal)
  (PA.actualPa_mem observation nontrivial half depth ordinal)
 have rawRead : (sourceCorrection observation nontrivial half depth ordinal : BurnolL2)=
  burnolDirectRightResolvent (observation.coordinate/2)
   (PA.actualPa observation nontrivial half depth ordinal : BurnolL2)-
  Parent.sourceCoefficient observation nontrivial half depth ordinal •
   burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation half.down) 4 := by
  unfold sourceCorrection
  simp only [Submodule.coe_sub,Submodule.coe_smul]
  rw [Parent.source_response_value,OriginalKCombCofinalRAction.original_R_direct]
  rfl
 have actual : (sourceCorrection observation nontrivial half depth ordinal : BurnolL2)∈burnolOriginalPaInL2 := by
  rw [rawRead]
  exact belongs
 obtain ⟨material,member,same⟩:=Submodule.mem_map.mp actual
 have identity : material=sourceCorrection observation nontrivial half depth ordinal:=Subtype.ext same
 exact identity ▸ member

theorem source_response_complete :
 Parent.sourceResponse observation nontrivial half depth ordinal=
 sourceCorrection observation nontrivial half depth ordinal+
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
 sourceWholeUnit observation nontrivial half := by
 unfold sourceCorrection
 abel

theorem source_correction_E :
 PA.E (sourceCorrection observation nontrivial half depth ordinal : BurnolL2)=
 sourceCorrection observation nontrivial half depth ordinal := by
 change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection (sourceCorrection observation nontrivial half depth ordinal : BurnolL2))=_
 have physical : burnolEvenAmbientProjection
  (sourceCorrection observation nontrivial half depth ordinal : BurnolL2)=
  sourceCorrection observation nontrivial half depth ordinal :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [physical]
 exact Submodule.starProjection_eq_self_iff.mpr (source_correction_memPa observation nontrivial half depth ordinal)

theorem actual_whole_source_successor :
 D.raw observation nontrivial half depth (ordinal+1)=
 (sourceCorrection observation nontrivial half depth ordinal : BurnolL2)+
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
  (sourceWholeUnit observation nontrivial half : BurnolL2)+
 P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)) := by
 have complete:=Parent.actual_R_source_split observation nontrivial half depth ordinal
 rw [source_response_complete] at complete
 simpa only [Submodule.coe_add,Submodule.coe_smul] using complete

/-- E keeps the whole unit's own Pa foot and the actual re-entry fee; the unit's pre-projection source zero is not borrowed here. -/
theorem actual_Pa_source_successor :
 PA.actualPa observation nontrivial half depth (ordinal+1)=
 sourceCorrection observation nontrivial half depth ordinal+
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
  PA.E (sourceWholeUnit observation nontrivial half : BurnolL2)+
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))) := by
 have generated:=congrArg PA.E (actual_whole_source_successor observation nontrivial half depth ordinal)
 simp only [map_add,map_smul] at generated
 rw [source_correction_E] at generated
 exact generated

theorem source_correction_finite_source :
 burnolMobiusSourceL2 (sourceCorrection observation nontrivial half depth ordinal)=
 burnolMobiusSourceL2 (Parent.sourceResponse observation nontrivial half depth ordinal) := by
 unfold sourceCorrection
 rw [map_sub,map_smul]
 have unitZero:=burnolZeroOwnedUnitTailState_finiteSource_zero observation nontrivial half.down
 change burnolMobiusSourceL2 (sourceWholeUnit observation nontrivial half)=0 at unitZero
 rw [unitZero,smul_zero,sub_zero]

/-- The complete next source is calculated in its original Mobius carrier, rather than retained only through one coefficient. -/
theorem actual_Mobius_source_successor :
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth (ordinal+1))=
 burnolMobiusSourceL2 (sourceCorrection observation nontrivial half depth ordinal)+
 Parent.sourceCoefficient observation nontrivial half depth ordinal •
  burnolMobiusSourceL2 (PA.E (sourceWholeUnit observation nontrivial half : BurnolL2))+
 burnolMobiusSourceL2
  (PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))) := by
 have generated:=congrArg burnolMobiusSourceL2
  (actual_Pa_source_successor observation nontrivial half depth ordinal)
 simpa only [map_add,map_smul] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalPaUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
