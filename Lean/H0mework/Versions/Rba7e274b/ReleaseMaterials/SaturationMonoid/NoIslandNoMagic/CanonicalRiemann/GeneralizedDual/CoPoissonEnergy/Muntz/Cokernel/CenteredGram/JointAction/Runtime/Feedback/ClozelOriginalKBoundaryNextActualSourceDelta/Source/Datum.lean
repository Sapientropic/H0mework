import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Decoder

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
local instance wholePaSourceDatumComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction





open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SourceFamily
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Packet)
end SourceFamily
namespace SourceL
export OriginalKFullSourceRAction.L (Value groups)
end SourceL
namespace SourceCF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (codeAt)
end SourceCF
namespace SourceAS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (write template stockCfg)
end SourceAS
namespace SourceA
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end SourceA
namespace SourceWB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (programme nativeAt oldPaid)
end SourceWB

local instance sourceDatumGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

/-- The original emitter's source-valued write is acted on by the graded source-only AST, before its dependent decoder is used. -/
def sourceActorWrite (h nextShift : ℝ)
    (value : PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) ()) :
    Env (PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade)) sourceCfg.LowVar := by
  let code : Expr (PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade)) sourceCfg.LowVar () :=
    language.symm ▸ SourceCF.codeAt (sourceCarrierCode observation nontrivial half h nextShift) grade
  exact fun target _ => by
    cases target
    exact code.eval (SourceAS.write factory grade data sourceCfg language value)

/-- The existing born source template and inventory callbacks are retained; only its next field decoder receives the literal acted source write. -/
def sourceEmitterNextBase (h nextShift : ℝ) :=
  { SourceAS.template factory grade data sourceCfg language with
    datum := fun frame =>
      { (SourceAS.template factory grade data sourceCfg language).datum frame with
        nextEnvironmentReadAt := ((SourceWB.programme data.1 sourceCfg
          (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift)).datum frame).nextEnvironmentReadAt } }

/-- This installs the source field decoder in the real SourceDatum slot without asserting that an occurrence has yet executed it. -/
theorem source_emitter_decoder_installed (h nextShift : ℝ)
    (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade))
      (Var := sourceCfg.LowVar) (sort := ())) :
    ((sourceEmitterNextBase observation nontrivial half factory grade data sourceCfg language h nextShift).datum frame).nextEnvironmentReadAt =
      some (fun {_sourceCurrent} supplied _queryPaid =>
        sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
          (SourceWB.oldPaid data.1 sourceCfg + SourceWB.nativeAt sourceCfg frame supplied)) := rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
