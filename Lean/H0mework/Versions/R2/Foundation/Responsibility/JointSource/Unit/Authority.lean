import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Root
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

private theorem openAt_subsingleton (support : (World registered).Support)
    (responsibility : (World registered).Responsibility) :
    Subsingleton ((World registered).OpenAt support responsibility) := by
  rcases support with ⟨old, state⟩
  cases responsibility with
  | inl oldResponsibility =>
      constructor
      rintro ⟨left⟩ ⟨right⟩
      rfl
  | inr debt =>
      cases state with
      | none => exact ⟨fun impossible => nomatch impossible⟩
      | some state =>
          constructor
          rintro ⟨⟨left⟩⟩ ⟨⟨right⟩⟩
          rfl

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source registered) :=
  identityOnlyWorldLedgerRestructuringLaw (source registered) PUnit.unit
    (openAt_subsingleton registered)

private theorem patch_origin_injective (current : Current registered) :
    Function.Injective (fun entry =>
      ((patch registered current).toLedgerWriteEvolution.origin entry).1) := by
  intro left right same
  change (rowInventory registered current).forward
      ((rowInventory registered (targetCurrent registered current)).backward left) =
    (rowInventory registered current).forward
      ((rowInventory registered (targetCurrent registered current)).backward right) at same
  have indices := congrArg (rowInventory registered current).backward same
  rw [(rowInventory registered current).backward_forward,
    (rowInventory registered current).backward_forward] at indices
  exact ((rowInventory registered (targetCurrent registered current)).forward_backward left).symm.trans
    ((congrArg (rowInventory registered (targetCurrent registered current)).forward indices).trans
      ((rowInventory registered (targetCurrent registered current)).forward_backward right))

private theorem patch_destination_injective (current : Current registered) :
    Function.Injective (fun entry =>
      ((patch registered current).toLedgerWriteEvolution.destination entry).1) := by
  intro left right same
  change targetRow registered current ((rowInventory registered current).backward left) =
    targetRow registered current ((rowInventory registered current).backward right) at same
  rw [targetRow_inventory, targetRow_inventory] at same
  have indices := congrArg (rowInventory registered (targetCurrent registered current)).backward same
  rw [(rowInventory registered (targetCurrent registered current)).backward_forward,
    (rowInventory registered (targetCurrent registered current)).backward_forward] at indices
  exact ((rowInventory registered current).forward_backward left).symm.trans
    ((congrArg (rowInventory registered current).forward indices).trans
      ((rowInventory registered current).forward_backward right))

def restructuringCertification {current : Current registered}
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw registered)
      ((ledgerCompiler registered).compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (patch_origin_injective registered current) (patch_destination_injective registered current)

def restructuringSource : SourceNativeRestructuringLedgerSource (World registered) (JointV registered) where
  source := source registered
  compiler :=
    { ledgerCompiler := ledgerCompiler registered
      restructuringLaw := restructuringLaw registered
      certifyRestructuring := restructuringCertification registered }

abbrev originalProjectionLaw := CanonicalUnitArithmeticRoot.authoritativeRoot.source.projectionLaw

def originalOccurrence {current : Current registered}
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current) :
    CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current.1 := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact oldOccurrence registered current

/-- The state already contains the exact paid past trace; action and value are reads of the same event. -/
structure MathReadout where
  state : SourceOperationExecutionDebt.State registered.input.environment registered.input.expression
  action : SourceOperationExecutionDebt.Settlement state ⊕
    GeneratedStepAt (Idle.law registered.input.environment registered.input.expression) state
  value : Value sort

def mathReadout (current : Current registered) : MathReadout registered where
  state := current.2.state
  action := mathAction current.2
  value := current.2.state.1.eval registered.input.environment

def projectionLaw : SourceNativeProjectionLaw (restructuringSource registered).toLedgerSource where
  Projection := originalProjectionLaw.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl original => originalProjectionLaw.ActiveAt original (originalOccurrence registered occurrence)
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl original => originalProjectionLaw.InactiveAt original (originalOccurrence registered occurrence)
    | .inr _ => PEmpty
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl original => originalProjectionLaw.classify original (originalOccurrence registered occurrence)
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl original => originalProjectionLaw.PayloadAt original (originalOccurrence registered occurrence) active
    | .inr _ => MathReadout registered
  project := fun projection {current} occurrence active =>
    match projection with
    | .inl original => originalProjectionLaw.project original (originalOccurrence registered occurrence) active
    | .inr _ => mathReadout registered current

theorem original_projection_outcome {current : Current registered}
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current)
    (projection : originalProjectionLaw.Projection) :
    HEq ((projectionLaw registered).outcomeAt (.inl projection) occurrence)
      (originalProjectionLaw.outcomeAt projection (originalOccurrence registered occurrence)) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [projectionLaw]
  cases originalProjectionLaw.classify projection (originalOccurrence registered occurrence) <;> rfl

private theorem original_terminal_empty (current : Current registered) :
    IsEmpty ((JointV registered).FaithfulTerminalAt current) :=
  ⟨fun terminal => nomatch terminal⟩

def authoritySource : SourceNativeAuthoritySource (World registered) (JointV registered) where
  restructuringSource := restructuringSource registered
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource registered)
    (original_terminal_empty registered)
  lawSurface := .rootSemantic (World registered)
  projectionLaw := projectionLaw registered

def authoritativeRoot : SourceNativeAuthoritativeRootClosure (World registered) (JointV registered) where
  source := authoritySource registered
  emitted := emitted registered
  compiler_commutes := (ledgerRoot registered).compiler_commutes

def livingRoot : SourceNativeLivingRootClosure (World registered) (JointV registered) :=
  (authoritativeRoot registered).toLivingWithoutFaithfulTerminal (original_terminal_empty registered)

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
