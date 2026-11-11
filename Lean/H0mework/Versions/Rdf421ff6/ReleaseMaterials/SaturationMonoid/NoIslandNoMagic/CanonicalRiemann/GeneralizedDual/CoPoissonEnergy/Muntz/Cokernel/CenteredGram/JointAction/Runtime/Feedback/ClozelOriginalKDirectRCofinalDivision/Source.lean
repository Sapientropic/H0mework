import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalPaAction.Source
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance divisionComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace D
export OriginalKCombFirstFullSourceDynamics (raw raw_successor)
end D
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace PA
export OriginalKCombCofinalPaAction (actualPa actualPa_mem invisible E Q)
end PA
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def sourceResponse : BurnolPaAmbientCarrier :=
 burnolPaResolventPhysicalResponse observation nontrivial half.down
  (PA.actualPa observation nontrivial half depth ordinal)
  (PA.actualPa_mem observation nontrivial half depth ordinal)

def sourceCoefficient : ℂ :=
 burnolPaResolventSourceCoefficient (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (PA.actualPa observation nontrivial half depth ordinal)

def sourceUnit : BurnolPaAmbientCarrier :=
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolZeroOwnedUnitTailState observation nontrivial half.down)

theorem source_response_value :
 (sourceResponse observation nontrivial half depth ordinal : BurnolL2)=
 P.R observation nontrivial half (PA.actualPa observation nontrivial half depth ordinal : BurnolL2) := by
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rfl

theorem source_response_positionGap :
 (sourceResponse observation nontrivial half depth ordinal : BurnolL2)∈
 locallyConstantFace burnolUnscaledCommonGapRadius :=
 (sourceResponse observation nontrivial half depth ordinal).property.1.1

theorem source_response_Q :
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (sourceResponse observation nontrivial half depth ordinal)=
 sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half :=
 burnolPaResolventPhysicalResponse_Q observation nontrivial half.down
  (PA.actualPa observation nontrivial half depth ordinal)
  (PA.actualPa_mem observation nontrivial half depth ordinal)

theorem source_R_Q :
 PA.Q (P.R observation nontrivial half (PA.actualPa observation nontrivial half depth ordinal : BurnolL2))=
 sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half := by
 rw [←source_response_value]
 change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolEvenAmbientProjection (sourceResponse observation nontrivial half depth ordinal : BurnolL2))=_
 have physical : burnolEvenAmbientProjection
  (sourceResponse observation nontrivial half depth ordinal : BurnolL2)=
  sourceResponse observation nontrivial half depth ordinal :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 exact (congrArg burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection physical).trans
  (source_response_Q observation nontrivial half depth ordinal)

theorem actual_R_source_split :
 D.raw observation nontrivial half depth (ordinal+1)=
 (sourceResponse observation nontrivial half depth ordinal : BurnolL2)+
 P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)) := by
 rw [D.raw_successor,source_response_value]
 unfold PA.invisible PA.actualPa
 rw [map_sub]
 abel

theorem actual_Q_successor :
 PA.Q (D.raw observation nontrivial half depth (ordinal+1))=
 sourceCoefficient observation nontrivial half depth ordinal • sourceUnit observation nontrivial half+
 PA.Q (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))) := by
 rw [actual_R_source_split,map_add]
 exact congrArg (fun value=>value+
  PA.Q (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))))
  ((congrArg PA.Q (source_response_value observation nontrivial half depth ordinal)).trans
   (source_R_Q observation nontrivial half depth ordinal))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
