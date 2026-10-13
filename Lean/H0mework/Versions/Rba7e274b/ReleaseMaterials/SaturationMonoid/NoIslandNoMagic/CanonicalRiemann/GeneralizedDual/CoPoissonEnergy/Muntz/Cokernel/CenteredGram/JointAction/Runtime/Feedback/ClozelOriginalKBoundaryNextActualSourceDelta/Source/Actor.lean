import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Update.Consumer

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
local instance wholePaNativeSpliceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction


open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
abbrev SourceBranches := OriginalKDefectAction.Branches
abbrev SourceValue := PairValue (PairValue OriginalKFullSourceRAction.C.Value)
abbrev SourceVar := OriginalKFullSourceRAction.C.Var

/-- The complete original source update is injected before any Pa, R or kernel read. -/
def actualSourceDeltaBranches (h nextShift : ℝ) : SourceBranches :=
  OriginalKDefectAction.actionFields
    (OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift)

def sourceCarrierAction (h nextShift : ℝ) (written : SourceBranches) : SourceBranches :=
  written + actualSourceDeltaBranches observation nontrivial half h nextShift

/-- This is an installation programme on the inherited variable carrier, rather than a target-price constant. -/
def sourceCarrierCode (h nextShift : ℝ) : Expr SourceValue SourceVar () :=
  .add (.var ()) (.const (actualSourceDeltaBranches observation nontrivial half h nextShift))

theorem source_carrier_code_read (h nextShift : ℝ) (environment : Env SourceValue SourceVar) :
    (sourceCarrierCode observation nontrivial half h nextShift).eval environment =
      sourceCarrierAction observation nontrivial half h nextShift (environment () ()) := rfl

/-- The source action produces its own additive change; H/N are source-actor parameters. -/
theorem source_carrier_action_effect (h nextShift : ℝ) (written : SourceBranches) :
    sourceCarrierAction observation nontrivial half h nextShift written - written =
      actualSourceDeltaBranches observation nontrivial half h nextShift := by
  exact add_sub_cancel_left _ _

def sourceDeltaProjection (h nextShift : ℝ) (written : SourceBranches) : BurnolL2 :=
  OriginalKFullSourceRAction.originalField
    (sourceCarrierAction observation nontrivial half h nextShift written - written)

theorem source_delta_projection (h nextShift : ℝ) (written : SourceBranches) :
    sourceDeltaProjection observation nontrivial half h nextShift written =
      OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift := by
  rw [sourceDeltaProjection, source_carrier_action_effect]
  rfl

/-- Pa/nonPa are dependent reads of this very source action, not identifications of a receiver sequence. -/
theorem source_action_dependent_Pa_nonPa (h nextShift : ℝ) (written : SourceBranches) :
    OriginalKCombCofinalPaAction.E (sourceDeltaProjection observation nontrivial half h nextShift written) =
      actualWholePaNativeSourceUpdate observation nontrivial half h nextShift ∧
    sourceDeltaProjection observation nontrivial half h nextShift written -
      (OriginalKCombCofinalPaAction.E (sourceDeltaProjection observation nontrivial half h nextShift written) : BurnolL2) =
      actualNonPaNativeSourceUpdate observation nontrivial half h nextShift := by
  rw [source_delta_projection]
  exact ⟨rfl, rfl⟩


/-- The original R programme acts on the same carrier change and generates its four inherited faces. -/
theorem source_action_original_R_effect (h nextShift : ℝ) (written : SourceBranches) :
    OriginalKFullSourceRAction.variableAction observation nontrivial half
      (sourceCarrierAction observation nontrivial half h nextShift written) -
    OriginalKFullSourceRAction.variableAction observation nontrivial half written =
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualSourceDeltaBranches observation nontrivial half h nextShift) := by
  unfold sourceCarrierAction
  rw [map_add, add_sub_cancel_left]

theorem source_action_original_R_first (h nextShift : ℝ) :
    (OriginalKFullSourceRAction.variableAction observation nontrivial half
      (actualSourceDeltaBranches observation nontrivial half h nextShift)).1.1 =
    OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift) := rfl


def sourceCarrierEnvironment (written : SourceBranches) : Env SourceValue SourceVar := fun _ _ => written

def sourceActionIncrementEnvironment (h nextShift : ℝ) (written : SourceBranches) : Env SourceValue SourceVar :=
  sourceCarrierEnvironment (sourceCarrierAction observation nontrivial half h nextShift written) -
    sourceCarrierEnvironment written

theorem source_action_increment_environment (h nextShift : ℝ) (written : SourceBranches) :
    sourceActionIncrementEnvironment observation nontrivial half h nextShift written =
      sourceCarrierEnvironment (actualSourceDeltaBranches observation nontrivial half h nextShift) := by
  funext target name
  exact source_carrier_action_effect observation nontrivial half h nextShift written

/-- Raw source material retains the inherited old field and the actor-generated fullS increment before the original R programme is executed. -/
def sourceRUpdateRaw (h nextShift : ℝ) (written : SourceBranches) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue SourceValue) (Var := SourceVar) (sort := ()) :=
  ⟨pairEnvironment (sourceCarrierEnvironment written)
      (sourceActionIncrementEnvironment observation nontrivial half h nextShift written),
    liftExpr (OriginalKFullSourceRAction.sourceCode observation nontrivial half)⟩

def sourceRUpdateTrace (h nextShift : ℝ) (written : SourceBranches) :
    Trace (sourceRUpdateRaw observation nontrivial half h nextShift written).environment
      (sourceRUpdateRaw observation nontrivial half h nextShift written).expression
      (.const ((OriginalKFullSourceRAction.variableAction observation nontrivial half written),
        OriginalKFullSourceRAction.variableAction observation nontrivial half
          (actualSourceDeltaBranches observation nontrivial half h nextShift))) := by
  unfold sourceRUpdateRaw
  rw [source_action_increment_environment]
  exact execution _ _

theorem source_R_update_material_pair (h nextShift : ℝ) (written : SourceBranches) :
    (sourceRUpdateRaw observation nontrivial half h nextShift written).expression.eval
      (sourceRUpdateRaw observation nontrivial half h nextShift written).environment =
    (OriginalKFullSourceRAction.variableAction observation nontrivial half written,
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualSourceDeltaBranches observation nontrivial half h nextShift)) :=
  (sourceRUpdateTrace observation nontrivial half h nextShift written).sound

/-- Only the source increment is assumed to have been installed. Its coefficient/R effect is then generated by the original readers. -/
theorem consume_written_source_increment (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift)
    (before after : SourceBranches)
    (sourceWritten : after = sourceCarrierAction observation nontrivial half h nextShift before) :
    OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField (after-before)) =
      OriginalKWholePaSourceRankAction.actualWholePaSource observation nontrivial half nextShift -
        OriginalKWholePaSourceRankAction.actualWholePaSource observation nontrivial half h ∧
    burnolPaResolventSourceCoefficient
        (OriginalKWholePaSourceRankAction.actualWholePaDivisionCoordinate observation nontrivial half)
        (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField (after-before))) =
      OriginalKWholePaSourceRankAction.actualWholePaSourceCoefficient observation nontrivial half nextShift -
        OriginalKWholePaSourceRankAction.actualWholePaSourceCoefficient observation nontrivial half h ∧
    OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKFullSourceRAction.originalField (after-before) -
        (OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField (after-before)) : BurnolL2)) =
      OriginalKWholePaSourceRankAction.actualNonPaR observation nontrivial half nextShift -
        OriginalKWholePaSourceRankAction.actualNonPaR observation nontrivial half h := by
  subst after
  have delta := source_delta_projection observation nontrivial half h nextShift before
  change OriginalKFullSourceRAction.originalField
    (sourceCarrierAction observation nontrivial half h nextShift before - before) = _ at delta
  rw [delta]
  have projections := actual_native_source_Pa_nonPa_update observation nontrivial half h nextShift nonnegative ordered
  have reads := actual_native_rank_R_source_update observation nontrivial half h nextShift nonnegative ordered
  exact ⟨projections.1.symm, reads.1.symm, reads.2.symm⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
