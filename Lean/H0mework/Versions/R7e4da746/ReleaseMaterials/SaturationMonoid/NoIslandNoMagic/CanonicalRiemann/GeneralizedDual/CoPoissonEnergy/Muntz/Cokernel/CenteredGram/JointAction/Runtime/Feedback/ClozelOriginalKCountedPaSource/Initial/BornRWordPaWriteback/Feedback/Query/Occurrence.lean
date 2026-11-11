import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRCanonicalMethodRuntime
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.CoefficientOccurrence
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace G
export SourceInventoryExecutionFeed.AdmissionReceipt
 (GeneratorOccurrence generatorRequest generator_request_member)
end G
namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory nativeWordData nativeWordInventory)
end A
namespace Lower
export BornRCanonicalMethodRuntime.Lower (Value groups)
end Lower
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket scalar stockScalar stockDecodedEnvironment)
end AS
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace Cfa
export ActualCofinalSourceAction (nativePacket selected bornStock paid_prefix_stocks)
end Cfa

private def along {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
 {source target : SourceInventoryExecutionFeed.Inventory (V := V) (X := X) (s := s)}
 (point : G.GeneratorOccurrence source) (segment : SourceInventoryTraceSegment source target) :
 G.GeneratorOccurrence target :=
 ⟨segment.before ++ point.before, point.expression, point.after ++ segment.after, by
  rw [segment.trace_eq, point.trace_eq]
  simp only [List.append_assoc, List.cons_append]⟩

private def preserveSegment {α : Type u} (prior : Option (RootedAccountedUnfolding α))
 (source : RootedAccountedUnfolding α) : SourceInventoryTraceSegment source (Stock.preserve prior source) := by
 cases prior with
 | none => exact SourceInventoryTraceSegment.refl source
 | some carried => exact SourceInventoryTraceSegment.right carried source

section Trace
variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable {environment : Env V X} {operation : V s →+ V s} {input : Expr V X s} {result : V s}

/-- The last source branch fixes a position for the entire ordered coefficient AST. -/
def traceCodeOccurrence (trace : Trace environment (.linear operation input) (.const result)) :
 G.GeneratorOccurrence (traceInventory trace) :=
 let inner := SourceHistoryCommon.seed (P.exposure trace)
  (P.exposure (SourceOperationExecution.originalInput trace).2.1)
 ⟨inner.root :: inner.trace, Coefficients.expression (traceGamma trace), [], by
  change inner.root :: (inner.trace ++
   ([PresentedRelationEventAt.generator (Coefficients.expression (traceGamma trace))] ++ [])) = _
  simp only [List.append_nil, List.cons_append]⟩

theorem traceCodeOccurrence_expression
 (trace : Trace environment (.linear operation input) (.const result)) :
 (traceCodeOccurrence trace).expression = Coefficients.expression (traceGamma trace) := rfl
end Trace

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance baseGroups : ∀ t, AddCommGroup (A.W t) := BornRCanonicalMethodRuntime.levelGroups 0
local instance levelGroups (n : Nat) : ∀ t, AddCommGroup (Lower.Value A.W n t) :=
 BornRCanonicalMethodRuntime.levelGroups n
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half

def nativeWordOccurrence (n : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Lower.Value A.W n) (Var := A.X) (sort := slot)) :
 G.GeneratorOccurrence (A.nativeWordInventory observation nontrivial half n frame) :=
 traceCodeOccurrence (A.nativeWordData observation nontrivial half n frame).trace

theorem nativeWordOccurrence_expression (n : Nat)
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Lower.Value A.W n) (Var := A.X) (sort := slot)) :
 (nativeWordOccurrence observation nontrivial half n frame).expression =
 Coefficients.expression (A.nativeWordData observation nontrivial half n frame).gamma := rfl

variable (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))

def expression : Expr (Lower.Value A.W (packet.1+1)) packet.2.2.1.LowVar slot :=
 packet.2.2.2.down.symm ▸
  Coefficients.expression (A.nativeWordData observation nontrivial half packet.1 packet.2.1.1).gamma

/-- The original extraScalar branch is a literal segment of this admission's scalar stock. -/
def scalarOccurrence : G.GeneratorOccurrence
 (AS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 let segment : SourceInventoryTraceSegment
   (A.nativeWordInventory observation nontrivial half n frame)
   (AS.scalar factory n ⟨frame, seed⟩ ⟨A.X, datum, scalar, pair⟩ rfl) := by
  unfold AS.scalar
  refine SourceInventoryTraceSegment.trans ?_ (preserveSegment _ _)
  refine SourceInventoryTraceSegment.trans ?_ (preserveSegment _ _)
  refine SourceInventoryTraceSegment.trans ?_ (SourceInventoryTraceSegment.left _ _)
  change SourceInventoryTraceSegment
   (A.nativeWordInventory observation nontrivial half n frame)
   (SourceHistoryCommon.seed (A.nativeWordInventory observation nontrivial half n frame) _)
  exact SourceInventoryTraceSegment.left _ _
 exact along (nativeWordOccurrence observation nontrivial half n frame) segment

theorem scalarOccurrence_expression :
 (scalarOccurrence observation nontrivial half packet).expression =
 expression observation nontrivial half packet := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 rfl

def selectedOccurrence : G.GeneratorOccurrence
 (AS.stockScalar (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1) :=
 along (scalarOccurrence observation nontrivial half packet) (by
  unfold AS.stockScalar
  rw [(Cfa.paid_prefix_stocks factory packet _ (Nat.le_refl _)).1]
  exact SourceInventoryTraceSegment.left _ _)

theorem selectedOccurrence_expression :
 (selectedOccurrence observation nontrivial half packet).expression =
 expression observation nontrivial half packet :=
 scalarOccurrence_expression observation nontrivial half packet

/-- Feed appends its actual executions after this same generator occurrence. -/
def bornOccurrence : G.GeneratorOccurrence (Cfa.bornStock factory packet) := by
 let point := selectedOccurrence observation nontrivial half packet
 let frame := Cfa.selected factory packet
 let base := (Cfa.nativePacket factory packet).2.2.1
 let tail := RootedAccountedUnfolding.traceBranches
  (SourceInventoryExecutionFeed.executionBranches (AS.stockDecodedEnvironment frame base)
   (SourceInventoryExecutionFeed.requests (AS.stockScalar frame base)))
 refine ⟨point.before, point.expression, point.after ++ tail, ?_⟩
 change (SourceInventoryExecutionFeed.written (AS.stockDecodedEnvironment frame base)
  (AS.stockScalar frame base)).trace = _
 rw [SourceInventoryExecutionFeed.written_trace, point.trace_eq]
 simp only [tail, List.cons_append, List.append_assoc]

theorem bornOccurrence_expression :
 (bornOccurrence observation nontrivial half packet).expression =
 expression observation nontrivial half packet :=
 selectedOccurrence_expression observation nontrivial half packet

end CountedPaInitial.BornRWordPaWriteback.CoefficientOccurrence
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
