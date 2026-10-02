import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Ledger
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld DebtActivationLedger

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

private def twoIndex : ConstructivePresentation (Fin 2) (Option PUnit) where
  forward index := if index.val = 0 then some PUnit.unit else none
  backward
    | some _ => 0
    | none => 1
  backward_forward := by
    intro index
    fin_cases index <;> rfl
  forward_backward := by
    intro index
    cases index with
    | none => rfl
    | some value => cases value; rfl

def rowInventory (current : Current registered) :
    ConstructivePresentation (Fin 2) (OpenResponsibilityAt (World registered) (supportAt registered current)) :=
  twoIndex.trans ((source registered).law.affectedInventoryPresentation (emitted registered current).2)

theorem rowInventory_claim (before after : Current registered) (index : Fin 2) :
    ((rowInventory registered before).forward index).claim =
      ((rowInventory registered after).forward index).claim := by
  fin_cases index <;> rfl

private theorem entry_claim_injective (current : Current registered) :
    Function.Injective (fun entry : OpenResponsibilityAt (World registered) (supportAt registered current) => entry.claim) := by
  rintro ⟨left, leftOpen⟩ ⟨right, rightOpen⟩ same
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          have oldEq : (⟨left, leftOpen⟩ : OpenResponsibilityAt CanonicalUnitArithmeticRoot.N current.1) =
              ⟨right, rightOpen⟩ :=
            (CanonicalUnitArithmeticRoot.rootLedgerEntry_unique _ _).trans
              (CanonicalUnitArithmeticRoot.rootLedgerEntry_unique _ _).symm
          exact congrArg (oldEntry (law := Idle.law registered.input.environment registered.input.expression)
            (state? := some current.2.state)) oldEq
      | inr right => exact nomatch same
  | inr left =>
      cases right with
      | inl right => exact nomatch same
      | inr right =>
          cases left
          cases right
          rcases leftOpen with ⟨⟨leftProof⟩⟩
          rcases rightOpen with ⟨⟨rightProof⟩⟩
          rfl

def targetCurrent (current : Current registered) : Current registered :=
  (JointV registered).nativeTarget (native registered current)

def sourceRow (current : Current registered) (index : Fin 2) :=
  (rowInventory registered current).forward index

def targetRow (current : Current registered) (index : Fin 2) :=
  ((wholeEvolution registered current).destination (sourceRow registered current index)).1

theorem targetRow_inventory (current : Current registered) (index : Fin 2) :
    targetRow registered current index = (rowInventory registered (targetCurrent registered current)).forward index := by
  apply entry_claim_injective registered (targetCurrent registered current)
  exact ((wholeEvolution registered current).destination
    (sourceRow registered current index)).2.toDebtLineage.claim_eq.symm.trans
      (rowInventory_claim registered current (targetCurrent registered current) index)

inductive RawRowAt :
    {current : Current registered} →
    (occurrence : (source registered).toRootSource.actual.OccurrenceAt current) →
    {targetSupport : (World registered).Support} →
    OpenResponsibilityAt (World registered)
      ((source registered).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt (World registered) targetSupport → Type
  | inventory (current : Current registered) (index : Fin 2) :
      RawRowAt (emitted registered current)
        (sourceRow registered current index) (targetRow registered current index)

def rowSource : LedgerWriteRowSourceAt (source registered) (RawRowAt registered) where
  IncidenceOccurrenceAt := RawRowAt registered
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    cases event with
    | inventory index =>
        exact ((wholeEvolution registered current).destination (sourceRow registered current index)).2
  compileExact := fun event => event

def rows (current : Current registered) :
    FiniteGeneratedLedgerWriteRowsAt (rowSource registered) (emitted registered current)
      ⟨supportAt registered (targetCurrent registered current)⟩ where
  size := 2
  sourceEntryAt := sourceRow registered current
  targetEntryAt := targetRow registered current
  rowAt index := (rowSource registered).generate (.inventory current index)

def coverage (current : Current registered) : LedgerCompleteFiniteCoverageAt (rows registered current) where
  destinationIndex := (rowInventory registered current).backward
  originIndex := (rowInventory registered (targetCurrent registered current)).backward
  destination_sound := (rowInventory registered current).forward_backward
  origin_sound entry := (targetRow_inventory registered current _).trans
    ((rowInventory registered (targetCurrent registered current)).forward_backward entry)

def patch (current : Current registered) :
    FiniteGeneratedLedgerWritePatchAt (rowSource registered) (emitted registered current)
      ⟨supportAt registered (targetCurrent registered current)⟩ :=
  .complete (rows registered current) (coverage registered current)

theorem wholeEvolution_origin_inventory (current : Current registered)
    (entry : OpenResponsibilityAt (World registered) (supportAt registered (targetCurrent registered current))) :
    (rowInventory registered current).forward
        ((rowInventory registered (targetCurrent registered current)).backward entry) =
      ((wholeEvolution registered current).origin entry).1 := by
  apply entry_claim_injective registered current
  exact (rowInventory_claim registered current (targetCurrent registered current) _).trans
    ((congrArg (fun entry => entry.claim)
      ((rowInventory registered (targetCurrent registered current)).forward_backward entry)).trans
        ((wholeEvolution registered current).origin entry).2.toDebtLineage.claim_eq.symm)

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
