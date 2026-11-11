import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.UnitBalance
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalGammaActionQuery"
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxErrors 1
noncomputable section
universe uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaActionQuery
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction OriginalRSourceJointContact
open scoped InnerProductSpace
namespace A
export BornRCanonicalMethodRuntime
 (W X fixedRFactory nativeStock nativeGammaActionData nativeGammaActionScalar nativeGammaActionOccurrence fixedRFactory_extraScalar)
end A
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end Lower
namespace AS
export ActualCofinalSourceAction.AS (AdmissionPacket stockCfg scalar)
export ActualNativeRelationTransport.AS (stockScalar stockDecodedEnvironment)
end AS
namespace Cfa
export ActualCofinalSourceAction (nativePacket selected sourceBorn born_inventory paid_prefix_stocks bornStock)
end Cfa
namespace SourceAS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (scalar)
end SourceAS
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end T
namespace Feed
export SourceInventoryExecutionFeed (requests receipt receipt_cost)
export SourceInventoryExecutionFeed.AdmissionReceipt (GeneratorOccurrence generatorRequest generator_request_member)
end Feed
namespace Price
export BornRSourcePrice (SourcePriceMethodReceipt actual_source_price_method)
end Price
open private seedLeft preserveRight from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory
open private along from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.Occurrence
local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance levelGroups (n : Nat) : ∀ t, AddCommGroup (Lower.Value A.W n t) := Lower.groups A.W n
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
variable (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))

def sourceData := A.nativeGammaActionData observation nontrivial half packet.1 packet.2.1.1

def sourceExpression : Expr (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar slot :=
  packet.2.2.2.down.symm ▸ ActionSource.atGrade observation nontrivial half
    (sourceData observation nontrivial half packet) (packet.1+1)

/-- The generator comes directly from this frame's extraScalar, before any Feed execution. -/
def receiverOccurrence : Feed.GeneratorOccurrence
    (SourceAS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) := by
  rcases packet with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  let point := A.nativeGammaActionOccurrence observation nontrivial half n seed frame
  let cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
    (PhysicalValue := Lower.Value A.W n) (PhysicalVar := A.X) (sort := slot) := ⟨A.X,datum,scalar,pair⟩
  let block : ActualNativeRelationTransport.OccurrenceBlock
      (A.nativeGammaActionScalar observation nontrivial half n seed frame).trace
      (SourceAS.scalar factory n (frame,seed) cfg rfl).trace := by
    unfold SourceAS.scalar
    rw [A.fixedRFactory_extraScalar]
    exact preserveRight _ _ _ (preserveRight _ _ _
      (seedLeft _ _ _ ⟨[],[],by simp only [List.nil_append,List.append_nil]⟩))
  exact along point ⟨block.before,block.after,block.trace_eq⟩

theorem receiverOccurrence_expression :
    (receiverOccurrence observation nontrivial half packet).expression =
      sourceExpression observation nontrivial half packet := by
  rcases packet with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  rfl

/-- The unchanged original paid prefix retains the exact generated slot and its position. -/
def sourceOccurrence : Feed.GeneratorOccurrence
    (AS.stockScalar (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1) := by
  let point := receiverOccurrence observation nontrivial half packet
  have carried := (Cfa.paid_prefix_stocks factory packet (ActualCofinalSourceAction.receipt factory packet).1
    (Nat.le_refl _)).1
  let block : ActualNativeRelationTransport.OccurrenceBlock
      (SourceAS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).trace
      (AS.stockScalar (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1).trace := by
    unfold AS.stockScalar
    rw [carried]
    exact seedLeft _ _ _ ⟨[],[],by simp only [List.nil_append,List.append_nil]⟩
  exact along point ⟨block.before,block.after,block.trace_eq⟩

theorem sourceOccurrence_expression :
    (sourceOccurrence observation nontrivial half packet).expression =
      sourceExpression observation nontrivial half packet := receiverOccurrence_expression observation nontrivial half packet

def request := Feed.generatorRequest (sourceOccurrence observation nontrivial half packet)
theorem request_member : request observation nontrivial half packet ∈ Feed.requests
    (AS.stockScalar (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1) :=
  Feed.generator_request_member (sourceOccurrence observation nontrivial half packet)

def environment := AS.stockDecodedEnvironment
  (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1

def receipt := Feed.receipt (environment observation nontrivial half packet)
  (request observation nontrivial half packet)

theorem sourceExpression_cost : remaining (sourceExpression observation nontrivial half packet) = 13 := by
  rcases packet with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  exact ActionSource.atGrade_cost observation nontrivial half _ (n+1)

theorem receipt_cost : (receipt observation nontrivial half packet).length = 13 :=
  (Feed.receipt_cost (environment observation nontrivial half packet)
    (request observation nontrivial half packet)).trans
    ((congrArg remaining (sourceOccurrence_expression observation nontrivial half packet)).trans
      (sourceExpression_cost observation nontrivial half packet))

/-- Every primitive of THIS physical Gamma query enters the original born inventory. -/
theorem receipt_written : ∀ event ∈ (SourceOperationPaidRelations.exposure
    (receipt observation nontrivial half packet)).trace,
    event ∈ (Cfa.bornStock factory packet).trace :=
  ActualNativeRelationTransport.source_execution_written
    (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1
    (request observation nontrivial half packet) (request_member observation nontrivial half packet)

/-- The terminal is read only after executing the admitted source AST. -/
def result := BornRSealedMethodHistory.wholeProjection (packet.1+1)
  ((request observation nontrivial half packet).expression.eval (environment observation nontrivial half packet))

theorem sourceExpression_read
    (decoder : Env (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar) :
    BornRSealedMethodHistory.wholeProjection (packet.1+1)
      ((sourceExpression observation nontrivial half packet).eval decoder) =
    (((OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceStep c)
        (sourceData observation nontrivial half packet).cotest - (sourceData observation nontrivial half packet).cotest,
      burnolDirectRightResolventCLM c (sourceData observation nontrivial half packet).native.source.1.1 -
        (sourceData observation nontrivial half packet).native.source.1.1),
     ((sourceData observation nontrivial half packet).cotest,(sourceData observation nontrivial half packet).native.source.1.1)) := by
  rcases packet with ⟨n,⟨frame,seed⟩,⟨Y,datum,scalar,pair⟩,⟨language⟩⟩
  cases language
  exact ActionSource.atGrade_read observation nontrivial half _ (n+1) decoder

theorem result_source : result observation nontrivial half packet =
    (((sourceData observation nontrivial half packet).nextCotest - (sourceData observation nontrivial half packet).cotest,
      (sourceData observation nontrivial half packet).native.fullR.1.1 - (sourceData observation nontrivial half packet).native.source.1.1),
     ((sourceData observation nontrivial half packet).cotest,(sourceData observation nontrivial half packet).native.source.1.1)) := by
  have paid := congrArg (BornRSealedMethodHistory.wholeProjection (packet.1+1))
    (completed_trace_value (environment observation nontrivial half packet)
      (receipt observation nontrivial half packet))
  have literal := congrArg (fun term : Expr (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar slot =>
    BornRSealedMethodHistory.wholeProjection (packet.1+1)
      (term.eval (environment observation nontrivial half packet)))
    (sourceOccurrence_expression observation nontrivial half packet)
  have read := paid.trans (literal.trans (sourceExpression_read observation nontrivial half packet
    (environment observation nontrivial half packet)))
  have actions := ActionSource.material_actions observation nontrivial half (sourceData observation nontrivial half packet)
  simpa only [result,actions.1,actions.2] using read

variable (depth ordinal : Nat)
namespace Actual
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : Price.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

/-- The query's source data is THIS installed fourth compiler leaf, as a whole dependent object. -/
theorem data_source : sourceData observation nontrivial half method.source =
    Generic.compiledGamma observation nontrivial half depth ordinal method :=
  ((Generic.compiledGamma_source observation nontrivial half depth ordinal method).trans
    (Installed.read_source observation nontrivial half method.gammaNative)).symm

attribute [local irreducible] Generic.compiledGamma

theorem result_compiled : result observation nontrivial half method.source =
    (((Generic.compiledGamma observation nontrivial half depth ordinal method).nextCotest -
       (Generic.compiledGamma observation nontrivial half depth ordinal method).cotest,
      (Generic.compiledGamma observation nontrivial half depth ordinal method).native.fullR.1.1 -
       (Generic.compiledGamma observation nontrivial half depth ordinal method).native.source.1.1),
     ((Generic.compiledGamma observation nontrivial half depth ordinal method).cotest,
      (Generic.compiledGamma observation nontrivial half depth ordinal method).native.source.1.1)) :=
  (result_source observation nontrivial half method.source).trans
    (congrArg (fun data : ActionMaterial observation nontrivial half
      (A.nativeStock method.source.1 method.source.2.1.1) =>
      ((data.nextCotest-data.cotest,data.native.fullR.1.1-data.native.source.1.1),
       (data.cotest,data.native.source.1.1)))
      (data_source observation nontrivial half depth ordinal method))

/-- The true Feed terminal pays the original bill in its two actual operation positions. -/
theorem result_bill :
    inner ℂ (result observation nontrivial half method.source).1.1
      (result observation nontrivial half method.source).2.2 =
        (Generic.compiledGamma observation nontrivial half depth ordinal method).bill ∧
    inner ℂ (result observation nontrivial half method.source).2.1
      (result observation nontrivial half method.source).1.2 =
        (Generic.compiledGamma observation nontrivial half depth ordinal method).bill := by
  rw [result_compiled observation nontrivial half depth ordinal method]
  exact ⟨(Generic.compiledGamma observation nontrivial half depth ordinal method).bill_source.symm,
    (Generic.compiledGamma observation nontrivial half depth ordinal method).bill_effect.symm⟩

/-- The Feed retains the newly computed physical boundary as a relation in its original born stock. -/
theorem boundary_written :
    (Finsupp.single (request observation nontrivial half method.source).expression 1 -
       Finsupp.single (.const ((request observation nontrivial half method.source).expression.eval
         (environment observation nontrivial half method.source))) 1) ∈
      SourceInventoryExecutionFeed.relationSpace (Cfa.bornStock factory method.source) := by
  exact SourceInventoryExecutionFeed.request_boundary_written
    (environment observation nontrivial half method.source)
    (AS.stockScalar (Cfa.selected factory method.source) (Cfa.nativePacket factory method.source).2.2.1)
    (request observation nontrivial half method.source) (request_member observation nontrivial half method.source)

open private source_actor fullR_actor from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Consumer

theorem result_nu : (result observation nontrivial half method.source).1.2 =
    Word.actualEffect observation nontrivial half depth ordinal update cutoff := by
  rw [result_compiled observation nontrivial half depth ordinal method]
  exact (congrArg₂ (fun left right : CompletedSourceRCalculation.Value slot => left.1.1-right.1.1)
    (fullR_actor observation nontrivial half depth ordinal method)
    (source_actor observation nontrivial half depth ordinal method)).trans
      (actual_nu_physical observation nontrivial half depth ordinal update cutoff).symm

theorem result_source_price :
    inner ℂ (result observation nontrivial half method.source).1.1
      (result observation nontrivial half method.source).2.2 =
    PaCoefficientSourceGramConsumer.returnCoefficient observation nontrivial half *
      (UnitBalance.programmeSourcePrice observation half
        (2*generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate+update+4) -
       UnitBalance.programmeSourcePrice observation half
        (2*generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate+update+3)) :=
  (result_bill observation nontrivial half depth ordinal method).1.trans
    (UnitBalance.Generic.actual_nu_source_bill observation nontrivial half depth ordinal method)

/-- The actual same-source request, its original nu and both operation positions are written by the original Feed. -/
theorem actual_physical_gamma_query_writeback :
    method.source = (Word.installedMethod observation nontrivial half depth ordinal update cutoff).method.source ∧
    (request observation nontrivial half method.source) ∈ Feed.requests
      (AS.stockScalar (Cfa.selected factory method.source) (Cfa.nativePacket factory method.source).2.2.1) ∧
    (result observation nontrivial half method.source).1.2 =
      Word.actualEffect observation nontrivial half depth ordinal update cutoff ∧
    (Cfa.sourceBorn factory method.source).2.1.1.inventory = some (Cfa.bornStock factory method.source) ∧
    ∀ event ∈ (SourceOperationPaidRelations.exposure
      (receipt observation nontrivial half method.source)).trace,
      event ∈ (Cfa.bornStock factory method.source).trace :=
  ⟨(Generic.actual_nu_disposition observation nontrivial half depth ordinal method).1,
    request_member observation nontrivial half method.source,
    result_nu observation nontrivial half depth ordinal method,
    Cfa.born_inventory factory method.source,
    receipt_written observation nontrivial half method.source⟩

end Actual

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaActionQuery
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
