import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Consumer

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaSourceDecoderComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction




open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift

/-- This source-only programme is executed before the emitter decoder is installed. -/
def sourceActorRaw (h nextShift : ℝ) (written : SourceBranches) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := SourceValue) (Var := SourceVar) (sort := ()) :=
  ⟨sourceCarrierEnvironment written, sourceCarrierCode observation nontrivial half h nextShift⟩

def sourceActorTrace (h nextShift : ℝ) (written : SourceBranches) :
    Trace (sourceActorRaw observation nontrivial half h nextShift written).environment
      (sourceActorRaw observation nontrivial half h nextShift written).expression
      (.const (sourceCarrierAction observation nontrivial half h nextShift written)) :=
  execution _ _

/-- This is the literal nextEnvironmentReadAt field decoder; its argument is the same emitter's inherited written value. -/
def sourceNextEnvironment (h nextShift : ℝ) (written : SourceBranches) : Env SourceValue SourceVar :=
  sourceCarrierEnvironment
    ((sourceActorRaw observation nontrivial half h nextShift written).expression.eval
      (sourceActorRaw observation nontrivial half h nextShift written).environment)

theorem source_next_environment_field (h nextShift : ℝ) (written : SourceBranches) :
    sourceNextEnvironment observation nontrivial half h nextShift written () () =
      sourceCarrierAction observation nontrivial half h nextShift written :=
  (sourceActorTrace observation nontrivial half h nextShift written).sound

/-- The decoder's complete source effect is generated from its AST; no completed target or installed-increment premise enters this construction. -/
theorem source_next_environment_increment (h nextShift : ℝ) (written : SourceBranches) :
    sourceNextEnvironment observation nontrivial half h nextShift written - sourceCarrierEnvironment written =
      sourceCarrierEnvironment (actualSourceDeltaBranches observation nontrivial half h nextShift) := by
  exact source_action_increment_environment observation nontrivial half h nextShift written

def sourceNextRRaw (h nextShift : ℝ) (written : SourceBranches) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue SourceValue) (Var := SourceVar) (sort := ()) :=
  ⟨pairEnvironment (sourceCarrierEnvironment written)
      (sourceNextEnvironment observation nontrivial half h nextShift written - sourceCarrierEnvironment written),
    liftExpr (OriginalKFullSourceRAction.sourceCode observation nontrivial half)⟩

theorem source_next_R_raw (h nextShift : ℝ) (written : SourceBranches) :
    sourceNextRRaw observation nontrivial half h nextShift written =
      sourceRUpdateRaw observation nontrivial half h nextShift written := rfl

/-- The old/effect four original R faces are calculated after the source decoder programme, before independent prices. -/
def sourceNextRTrace (h nextShift : ℝ) (written : SourceBranches) :
    Trace (sourceNextRRaw observation nontrivial half h nextShift written).environment
      (sourceNextRRaw observation nontrivial half h nextShift written).expression
      (.const (OriginalKFullSourceRAction.variableAction observation nontrivial half written,
        OriginalKFullSourceRAction.variableAction observation nontrivial half
          (actualSourceDeltaBranches observation nontrivial half h nextShift))) :=
  sourceRUpdateTrace observation nontrivial half h nextShift written

theorem source_next_R_first_effect (h nextShift : ℝ) (written : SourceBranches) :
    ((sourceNextRRaw observation nontrivial half h nextShift written).expression.eval
      (sourceNextRRaw observation nontrivial half h nextShift written).environment).2.1.1 =
      OriginalKFullSourceRResponse.Op.R observation nontrivial half
        (OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift) := by
  rw [(sourceNextRTrace observation nontrivial half h nextShift written).sound]
  exact source_action_original_R_first observation nontrivial half h nextShift

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
