import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Install
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre.KernelWrite
namespace Previous
export OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Install
  (born configuration write actual_born_write original_ledger original_occurrence)
end Previous
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Seed cfg defaultFactory)
end SF
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
  (raw action_reader actual_value actual_trace actual_base_value actual_reader_environment updated_total)
end AI
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (codeAt collapseValue)
end CF
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation (jointCode)
end FR
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (baseRoot actualOccurrence next datum)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader actionResultAt occurrence)
end R
namespace MR
export SourceGeneratedInquiryReceiptAction.Read (raw_source environment_source state_source occurrence_source)
end MR
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (oldPaid nativeValue born programme sourceTarget born_environment born_inventory born_pair_inventory
   configured_actual_paid_pair_writeback source_compiles source_whole source_target_next source_target_root actual_receipt_next)
end WB
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end E
local instance groups (grade : Nat) : ∀ slot, AddCommGroup (L.Value (PairValue C.Value) grade slot) :=
  L.groups (PairValue C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate=-2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth n : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth
local notation "total" => BoundaryNativeKAction.total
local notation "W" => PairValue C.Value

def grade (ordinal : Nat) : Nat := Sigma.fst (NativeDelta.BetaDecoder.nextNative factory (nativeAt (ordinal+1)))+1

def frame (ordinal : Nat) : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
    (Value := L.Value W (grade observation nontrivial half depth ordinal)) (Var := C.Var) (sort := ()) :=
  Previous.born c n factory (nativeAt (ordinal+1))

theorem frame_generated (ordinal : Nat) : frame observation nontrivial half depth n ordinal=
    Previous.born c n factory (nativeAt (ordinal+1)) := rfl

theorem current_value (ordinal : Nat) :
    total (grade observation nontrivial half depth ordinal) ((frame observation nontrivial half depth n ordinal).activeEnvironment () ())=
      OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Consumer.value
        observation nontrivial half depth ordinal n :=
  congrArg (fun generated : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
    (Value := L.Value W (grade observation nontrivial half depth ordinal)) (Var := C.Var) (sort := ()) =>
      total (grade observation nontrivial half depth ordinal) (generated.activeEnvironment () ()))
    (frame_generated observation nontrivial half depth n ordinal)

attribute [local irreducible] frame

def seed (ordinal : Nat) : SF.Seed W C.Var () (grade observation nontrivial half depth ordinal) :=
  Material.inventorySeed (BoundaryCountedNativeUpdate.selected factory (nativeAt (ordinal+1)))
    (Previous.configuration c n factory (nativeAt (ordinal+1))) (Previous.write factory (nativeAt (ordinal+1)))

theorem seed_source (ordinal : Nat) : (frame observation nontrivial half depth n ordinal).inventory=
    some (seed observation nontrivial half depth n ordinal) := by
  unfold frame
  exact Material.inventorySeed_source (BoundaryCountedNativeUpdate.selected factory (nativeAt (ordinal+1)))
    (Previous.configuration c n factory (nativeAt (ordinal+1))) (Previous.write factory (nativeAt (ordinal+1)))

attribute [local irreducible] grade

def configuration (ordinal : Nat) : A.Programme
    (PhysicalValue := L.Value W (grade observation nontrivial half depth ordinal)) (PhysicalVar := C.Var) (sort := ()) :=
  SF.cfg factory (grade observation nontrivial half depth ordinal)
  (seed observation nontrivial half depth n ordinal)

def sourceCode : Expr (PairValue W) C.Var () := FR.jointCode (OriginalKCombPhysicalAction.code observation nontrivial half)

abbrev result (ordinal : Nat) := R.actionResultAt (frame observation nontrivial half depth n ordinal)
  (configuration observation nontrivial half depth n ordinal) (S.actualOccurrence (frame observation nontrivial half depth n ordinal))
abbrev material (ordinal : Nat) := R.actualMaterial (frame observation nontrivial half depth n ordinal)
  (configuration observation nontrivial half depth n ordinal)

theorem actual_reader (ordinal : Nat) : R.actionReader (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (S.actualOccurrence (frame observation nontrivial half depth n ordinal)) =
      AI.raw (grade observation nontrivial half depth ordinal) (A.epoch (frame observation nontrivial half depth n ordinal))
        (sourceCode observation nontrivial half) (S.actualOccurrence (frame observation nontrivial half depth n ordinal)) :=
  AI.action_reader (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)
    (S.actualOccurrence (frame observation nontrivial half depth n ordinal))

theorem actual_environment (ordinal : Nat) :
    (R.actionReader (frame observation nontrivial half depth n ordinal) (configuration observation nontrivial half depth n ordinal)
      (S.actualOccurrence (frame observation nontrivial half depth n ordinal))).environment=
      pairEnvironment (frame observation nontrivial half depth n ordinal).activeEnvironment 0 :=
  AI.actual_reader_environment (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)

theorem actual_equation (ordinal : Nat) : (result observation nontrivial half depth n ordinal).2.2.1=
    (CF.codeAt (sourceCode observation nontrivial half) (grade observation nontrivial half depth ordinal)).eval
      (pairEnvironment (frame observation nontrivial half depth n ordinal).activeEnvironment 0) :=
  AI.actual_value (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)

theorem material_raw (ordinal : Nat) : (material observation nontrivial half depth n ordinal).raw=
    CF.codeAt (sourceCode observation nontrivial half) (grade observation nontrivial half depth ordinal) := by
  have generated := AI.action_reader (grade observation nontrivial half depth ordinal)
    (frame observation nontrivial half depth n ordinal) (sourceCode observation nontrivial half)
    (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)
    (R.occurrence (frame observation nontrivial half depth n ordinal) (configuration observation nontrivial half depth n ordinal))
  exact (MR.raw_source (frame observation nontrivial half depth n ordinal) (configuration observation nontrivial half depth n ordinal)).trans
    (congrArg (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue (L.Value W (grade observation nontrivial half depth ordinal))) (Var := C.Var) (sort := ()) => sourceRaw.expression) generated)

theorem actual_paid (ordinal : Nat) : (material observation nontrivial half depth n ordinal).state.2.length=
    remaining (CF.codeAt (sourceCode observation nontrivial half) (grade observation nontrivial half depth ordinal)) :=
  AI.actual_trace (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)

theorem actual_total (ordinal : Nat) :
    total (grade observation nontrivial half depth ordinal+1) (result observation nontrivial half depth n ordinal).2.2.1=
      OriginalKCombPhysicalAction.R observation nontrivial half
        (total (grade observation nontrivial half depth ordinal) ((frame observation nontrivial half depth n ordinal).activeEnvironment () ())) := by
  have base := AI.actual_base_value (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)
  have input := Material.current_collapse (grade observation nontrivial half depth ordinal)
    ((frame observation nontrivial half depth n ordinal).activeEnvironment () ())
  exact (Material.total_collapse _ _).trans ((congrArg (total 1) base).trans
    ((Material.joint_total observation nontrivial half _).trans
      (congrArg (OriginalKCombPhysicalAction.R observation nontrivial half) input)))

attribute [local semireducible] grade

theorem next_environment (ordinal : Nat) :
    (S.next (frame observation nontrivial half depth n ordinal) (configuration observation nontrivial half depth n ordinal)).activeEnvironment=
      (frame observation nontrivial half depth n ordinal).activeEnvironment := by
  unfold frame grade
  exact Material.born_next_environment (BoundaryCountedNativeUpdate.selected factory (nativeAt (ordinal+1)))
    (Previous.configuration c n factory (nativeAt (ordinal+1))) (Previous.write factory (nativeAt (ordinal+1)))
    (configuration observation nontrivial half depth n ordinal)

attribute [local irreducible] grade

def write (ordinal : Nat) (value : PairValue (L.Value W (grade observation nontrivial half depth ordinal)) ()) :
    Env (PairValue (L.Value W (grade observation nontrivial half depth ordinal))) C.Var := fun target _ => by
  cases target
  exact value

abbrev born (ordinal : Nat) := WB.born (frame observation nontrivial half depth n ordinal)
  (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

theorem actual_born_write (ordinal : Nat) : E.At (born observation nontrivial half depth n ordinal)
    (write observation nontrivial half depth ordinal ((material observation nontrivial half depth n ordinal).raw.eval
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material observation nontrivial half depth n ordinal)).environment)) :=
  WB.configured_actual_paid_pair_writeback (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

theorem born_value (ordinal : Nat) : (born observation nontrivial half depth n ordinal).activeEnvironment () ()=
    (result observation nontrivial half depth n ordinal).2.2.1 := by
  have written := E.active (WB.born_environment (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal))
  have totalValue := AI.updated_total (grade observation nontrivial half depth ordinal) (frame observation nontrivial half depth n ordinal)
    (sourceCode observation nontrivial half) (SF.defaultFactory W C.Var ()) (seed observation nontrivial half depth n ordinal)
    (write observation nontrivial half depth ordinal)
  have current := congrArg (fun env => (CF.codeAt (sourceCode observation nontrivial half)
    (grade observation nontrivial half depth ordinal)).eval (pairEnvironment env 0))
    (next_environment observation nontrivial half depth n ordinal)
  exact (congrArg (fun env => env () ()) written).trans
    (totalValue.trans (current.trans (actual_equation observation nontrivial half depth n ordinal).symm))

def value (ordinal : Nat) : BurnolL2 := total (grade observation nontrivial half depth ordinal+1)
  ((born observation nontrivial half depth n ordinal).activeEnvironment () ())

theorem value_source (ordinal : Nat) : value observation nontrivial half depth n ordinal=
    OriginalKCombPhysicalAction.R observation nontrivial half
      (total (grade observation nontrivial half depth ordinal) ((frame observation nontrivial half depth n ordinal).activeEnvironment () ())) :=
  (congrArg (total (grade observation nontrivial half depth ordinal+1)) (born_value observation nontrivial half depth n ordinal)).trans
    (actual_total observation nontrivial half depth n ordinal)

theorem actual_occurrence (ordinal : Nat) : HEq (R.occurrence (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal))
    ((frame observation nontrivial half depth n ordinal).currentState.root.emitted
      (frame observation nontrivial half depth n ordinal).currentState.visit.current) :=
  (heq_of_eq (MR.occurrence_source (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal))).trans HEq.rfl

theorem source_trace (ordinal : Nat) : type_of% (MR.state_source (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal)) :=
  MR.state_source (frame observation nontrivial half depth n ordinal) (configuration observation nontrivial half depth n ordinal)

theorem actual_compiles (ordinal : Nat) : type_of% (WB.source_compiles (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) :=
  WB.source_compiles (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

theorem born_inventory (ordinal : Nat) : type_of% (WB.born_inventory (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) ∧
    type_of% (WB.born_pair_inventory (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) :=
  ⟨WB.born_inventory (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal),
   WB.born_pair_inventory (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)⟩

theorem actual_receipt_next (ordinal : Nat) : type_of% (WB.actual_receipt_next (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) :=
  WB.actual_receipt_next (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

theorem whole_first (ordinal : Nat) : type_of% (WB.source_whole (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) :=
  WB.source_whole (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

theorem old_outcome (ordinal : Nat)
    (projection : (SourceGeneratedInquiryReceiptAction.old (frame observation nontrivial half depth n ordinal)
      (configuration observation nontrivial half depth n ordinal)).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    type_of% ((WB.sourceTarget (frame observation nontrivial half depth n ordinal)
      (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)).target.oldOutcome_heq projection) :=
  (WB.sourceTarget (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)).target.oldOutcome_heq projection

theorem generated_next (ordinal : Nat) : type_of% (WB.source_target_next (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)) :=
  WB.source_target_next (frame observation nontrivial half depth n ordinal)
    (configuration observation nontrivial half depth n ordinal) (write observation nontrivial half depth ordinal)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Install
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
