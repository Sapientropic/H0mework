import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Runtime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Renewal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))

def old := (Shared.baseRoot frame (programme seed)).toAuthoritativeRoot
abbrev origin := (Shared.actualVisit frame).current
abbrev reader := fun (supplied : Context.Installation.Occurrence frame (current:=(Shared.actualVisit frame).current)) =>
  (Shared.datum frame (programme seed)).reader supplied
abbrev calculationRoot := RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot
  (old seed frame) (origin frame) (reader seed frame)
abbrev endpoint := (Shared.resultFace frame (programme seed)).rootRead.2.1
abbrev Occurrence := (calculationRoot seed frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (endpoint seed frame)

def material (supplied : Occurrence seed frame) : RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
    (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) supplied := by
  rcases supplied with ⟨support,event⟩
  cases event
  let raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue PhysicalValue) (Var:=PhysicalVar) (sort:=sort) :=
    (Shared.query frame (programme seed)).raw
  exact {
    environment := raw.environment
    increment := (materialFace seed frame).rootRead.2.2.2.2.2.2.2 - raw.environment
    raw := raw.expression
    state := endpoint seed frame
    owner := RootGeneratedDebtActivationJointSource.OwnerFree.mathEntry (old seed frame) (origin frame) (reader seed frame) (endpoint seed frame) }

def registered := RootGeneratedDebtActivationJointSource.register (fun supplied : Occurrence seed frame =>
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material seed frame supplied))

namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (input expression relations budget updated_value residual_value residual_zero_iff)
end R
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (sourceSuccessor)
end O
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J
abbrev actualMaterial := material seed frame ((calculationRoot seed frame).emitted (endpoint seed frame))

theorem environment_source : (registered seed frame).input.environment =
    (materialFace seed frame).rootRead.2.2.2.2.2.2.2 := add_sub_cancel _ _

theorem completed_effect : (registered seed frame).input.expression.eval (registered seed frame).input.environment =
    effectEvaluator (R:=ℤ) (actualMaterial seed frame).environment (actualMaterial seed frame).increment
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial seed frame).environment
        (R.relations (R:=ℤ) (actualMaterial seed frame))) := R.updated_value (R:=ℤ) (actualMaterial seed frame)

theorem inverse_read : type_of% (R.residual_value (R:=ℤ) (actualMaterial seed frame)) :=
  R.residual_value (R:=ℤ) (actualMaterial seed frame)

private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement (J.initialEvent (registered seed frame)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered seed frame).input.environment
    (registered seed frame).input.expression).settlement_budget_zero settled
  have actualBudget := R.budget (actualMaterial seed frame)
  change remaining (R.expression (actualMaterial seed frame)) = 0 at zero
  omega

def firstStep := match _selected : J.mathAction (J.initialEvent (registered seed frame)) with
  | .inl settled => False.elim (not_settled seed frame settled)
  | .inr paid => paid

theorem firstStep_generated : J.mathAction (J.initialEvent (registered seed frame)) = .inr (firstStep seed frame) := by
  unfold firstStep
  cases selected : J.mathAction (J.initialEvent (registered seed frame)) with
  | inl settled => exact False.elim (not_settled seed frame settled)
  | inr paid => rfl

private theorem successor_option_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V} {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence generated) :
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? generated).isSome = true := by
  cases generated with
  | faithfulTerminal _ _ _ => exact nomatch successor
  | nativeWrite => rfl
  | relationWrite => rfl
  | continuedTransport => rfl
  | borromeanRedirect => rfl

private theorem packet_exists {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (lower : SourceNativeLedgerRootClosure N V) (current : V.Current)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (lower.emitted current) (lower.generatedLedgerAt current)) :
    (J.read? lower current).isSome = true := by
  have found := successor_option_exists (lower.generatedLedgerAt current) successor
  unfold RootGeneratedDebtActivationJointSource.Successor.read?
  cases selected : SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (lower.generatedLedgerAt current) with
  | none => simp only [selected,Option.isSome_none] at found; exact Bool.noConfusion found
  | some successor => rfl

def packets (current : (RootGeneratedDebtActivationJointSource.OwnerFree.vocabulary
    (old seed frame) (origin frame) (reader seed frame)).Current) : J.Packet (calculationRoot seed frame).toLedgerRoot current :=
  (J.read? (calculationRoot seed frame).toLedgerRoot current).get
    (packet_exists (calculationRoot seed frame).toLedgerRoot current
      (O.sourceSuccessor (old seed frame) (origin frame) (reader seed frame) current))

def root := RootGeneratedDebtActivationJointSource.Successor.Restructuring.livingRoot
  (calculationRoot seed frame) (registered seed frame) (packets seed frame)
def runtime := RootGeneratedDebtActivationJointSource.Successor.Restructuring.initialRuntime
  (calculationRoot seed frame) (registered seed frame) (packets seed frame)

theorem first_whole : type_of% (J.join_whole_paid (packets seed frame (endpoint seed frame))
    (J.initialEvent (registered seed frame)) (firstStep seed frame) (firstStep_generated seed frame)) :=
  J.join_whole_paid (packets seed frame (endpoint seed frame))
    (J.initialEvent (registered seed frame)) (firstStep seed frame) (firstStep_generated seed frame)


end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Renewal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
