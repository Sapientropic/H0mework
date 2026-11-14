import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedNativeWrite
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeQuery

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift RootInquiryCompletion
open OriginalKCofinalFullBranchFibre.KernelWrite

namespace N
export BoundaryCountedNativeWrite (Grade WordAt generatedNext generated_next_source actualRelation)
export BoundaryCountedNativeWord (gradeChart nextChart NextValues)
end N
namespace W
export NativeSigma.Writeback (nativeTrace nativeBoundary nativeReceiptTransfer nativeEvaluation)
end W
namespace B
export NativeDelta.BetaDecoder (nextNative)
end B
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
  (state presentation)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry (query)
end Stock
namespace Timeline
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (startAt index index_eq_stop packetAt sourceRuntime)
end Timeline
namespace Source
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (nativePresentation admission_native_full stockCfg)
end Source
namespace Install
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (resultFace result_value result_history)
end Install
namespace Origin
export SourceOperationInquiry.Context.Installation (Occurrence)
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end Origin
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (raw)
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (query_word_read)
end Joint
namespace Word
export SourceInventoryExecutionFeed.WordReceipt (orderedExpression ordered_eval)
end Word

local instance groups (grade : Nat) (slot : Unit) : AddCommGroup (N.Grade grade slot) :=
  L.groups (PairValue C.Value) grade slot

attribute [local irreducible] AS.localNativeReceipt

variable (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)

local notation "next" => B.nextNative factory native
abbrev frame := (next).2.1.1
abbrev configuration := Source.stockCfg (next).2.2.1
abbrev base := Stock.state (frame factory native) (configuration factory native)
local notation "f" => frame factory native
private abbrev nextSeed := (next).2.1.2
local notation "seed" => nextSeed factory native
private abbrev answerChart (slot : Unit) :
    PairValue (N.NextValues factory native) slot ≃+ PairValue (N.NextValues factory native) slot :=
  Rechart.pairChart (N.nextChart coordinate n factory native) slot
local notation "e" => answerChart coordinate n factory native

private abbrev originalWord : Formal ℤ (PairValue (N.NextValues factory native)) C.Var () :=
  W.nativeReceiptTransfer factory native (W.nativeBoundary native)

private abbrev evaluator :
    Formal ℤ (PairValue (N.NextValues factory native)) C.Var () →ₗ[ℤ]
      PairValue (N.NextValues factory native) () :=
  W.nativeEvaluation next

def steps : List (Formal ℤ (PairValue (N.NextValues factory native)) C.Var ()) :=
  (SourceOperationPaidRelations.words
    (Rechart.trace (N.gradeChart coordinate n native.1) (W.nativeTrace native))).map
    (W.nativeReceiptTransfer factory native)

theorem steps_boundary : (steps coordinate n factory native).sum = N.generatedNext coordinate n factory native :=
  rfl

/-- The next occurrence supplies the environment and the original paid steps supply the ordered expression. -/
def reader {current : Origin.Current (f).registered} (supplied : Origin.Occurrence f (current := current)) :
    Install.Raw (Value := PairValue (N.NextValues factory native)) (Var := C.Var) (sort := ()) :=
  ⟨Rechart.env e (Joint.raw seed (A.epoch f) supplied).environment,
    Word.orderedExpression (steps coordinate n factory native)⟩

local notation "old" => base factory native
local notation "read" => reader coordinate n factory native

def request :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.query old read
    (Stock.query f (configuration factory native))

def inquiry :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.state old read

def result :=
  (Install.resultFace old read).rootRead

/-- Read the full value carried by the installed result. -/
def resultValue : PairValue (N.NextValues factory native) () :=
  (result coordinate n factory native).2.2.1

theorem original_ledger :
    (inquiry coordinate n factory native).root.toAuthoritativeRoot.toLedgerRoot =
      (old).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_visit : HEq (inquiry coordinate n factory native).visit (old).visit := HEq.rfl

private theorem encoded_read (environment : Env (PairValue (N.NextValues factory native)) C.Var)
    (word : Formal ℤ (PairValue (N.NextValues factory native)) C.Var ()) :
    evaluation (R := ℤ) (Rechart.env e environment) (Rechart.word e () word) =
      e () (evaluation (R := ℤ) environment word) :=
  congrArg Prod.fst (Rechart.inventory e environment 0 word)

private theorem installed_value :
    let raw := read (S.actualOccurrence f)
    resultValue coordinate n factory native = raw.expression.eval raw.environment :=
  Install.result_value old read

private theorem original_value :
    let environment := (Joint.raw seed (A.epoch f) (S.actualOccurrence f)).environment
    evaluator factory native (originalWord factory native) =
      evaluation (R := ℤ) environment (originalWord factory native) :=
  Joint.query_word_read seed (A.epoch f) (S.actualOccurrence f) (originalWord factory native)

/-- The registered executor reads the complete transferred relation from the actual next Joint. -/
theorem result_source :
    resultValue coordinate n factory native =
      e () (evaluator factory native (originalWord factory native)) := by
  let environment := (Joint.raw seed (A.epoch f) (S.actualOccurrence f)).environment
  let word := originalWord factory native
  let view := Rechart.env e environment
  have source := installed_value coordinate n factory native
  have ordered := Word.ordered_eval (steps coordinate n factory native) view
  have boundary : (steps coordinate n factory native).sum = Rechart.word e () word :=
    N.generated_next_source coordinate n factory native
  have evaluated := (congrArg (evaluation (R := ℤ) view) boundary).trans
    (encoded_read coordinate n factory native environment word)
  exact source.trans (ordered.trans
    (evaluated.trans (congrArg (e ()) (original_value factory native).symm)))

theorem decoded_result :
    (e ()).symm (resultValue coordinate n factory native) =
      evaluator factory native (originalWord factory native) :=
  (congrArg (e ()).symm (result_source coordinate n factory native)).trans
    ((e ()).symm_apply_apply _)

theorem result_budget :
    (result coordinate n factory native).2.1.2.length =
      remaining (Word.orderedExpression (steps coordinate n factory native)) :=
  Install.result_history old read

private theorem native_opening (factory : NativeSigma.NativeFactory)
    (initial : A.M.Frame (Value := PairValue C.Value) (Var := C.Var) (sort := ()))
    (configuration : A.Programme (PhysicalValue := PairValue C.Value) (PhysicalVar := C.Var) (sort := ()))
    (language : configuration.LowVar = C.Var) (ordinal : Nat) :
    ((Timeline.sourceRuntime factory initial configuration language).stateAt
      (Timeline.index factory initial configuration language ordinal+1)).engine.node =
      .active (Source.nativePresentation
        (AS.nativeAfterAdmission factory (Timeline.packetAt factory initial configuration language ordinal)) 0) := by
  have stop := Timeline.index_eq_stop factory initial configuration language ordinal
  have arrived := Source.admission_native_full factory initial configuration language
    (Timeline.startAt factory initial configuration language ordinal) 0 (Nat.zero_le _)
  rw [← stop, Nat.add_zero] at arrived
  exact (Family.actual_node factory initial configuration language _).trans
    (congrArg RootInquiryProcessNode.active arrived)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "F" => D.factory observation nontrivial half
local notation "initial" => D.initial observation nontrivial half depth
local notation "cfg" => D.firstCfg observation nontrivial half depth
local notation "nativeAt" => originalNative observation nontrivial half depth
local notation "runtime" => originalRuntime observation nontrivial half depth

theorem actual_word (ordinal n : Nat) :
    (steps c n F (nativeAt (ordinal+1))).sum = (N.actualRelation observation nontrivial half depth ordinal n).val :=
  rfl

abbrev openingTick (ordinal : Nat) := Timeline.index F initial cfg rfl ordinal+1

/-- The exact opening of the original native segment is the same current used by this query. -/
theorem original_opening (ordinal : Nat) :
    ((runtime).stateAt (openingTick observation nontrivial half depth ordinal)).engine.node =
      .active (Source.nativePresentation (nativeAt ordinal) 0) :=
  native_opening F initial cfg rfl ordinal

theorem actual_query_current (ordinal : Nat) :
    ((runtime).stateAt (openingTick observation nontrivial half depth (ordinal+2))).engine.node =
      .active (Stock.presentation (frame F (nativeAt (ordinal+1))) (configuration F (nativeAt (ordinal+1)))) :=
  (original_opening observation nontrivial half depth (ordinal+2)).trans
    (congrArg (fun packet => RootInquiryProcessNode.active (Source.nativePresentation packet 0))
      (NativeDelta.BetaDecoder.Rooting.native_successor observation nontrivial half depth (ordinal+1)))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedNativeQuery
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
