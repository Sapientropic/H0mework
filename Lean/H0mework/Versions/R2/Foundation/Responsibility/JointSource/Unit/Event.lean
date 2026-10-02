import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Unit.Vocabulary

/-! The same original emitter and registered mathematical input generate each complete supported event. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Unit

open SourceOperationEffects DebtActivationWorld

variable {Sorts : Type} {Value Var : Sorts → Type} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {origin : CanonicalUnitArithmeticRoot.Current}
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  CanonicalUnitArithmeticRoot.ledgerRoot origin)

inductive SourceEventAt : (current : Current registered) → (World registered).Support → Type
  | generated (current : Current registered) : SourceEventAt current (supportAt registered current)

def eventAlgebra : SourceNativeEventAlgebra (World registered) (JointV registered) where
  EventAt := SourceEventAt registered
  compile := by
    intro current support event
    cases event with
    | generated => exact .nativeWrite (native registered current)
  AffectedInventoryAt := fun {current} {_support} _ =>
    Option (CanonicalUnitArithmeticRoot.source.law.AffectedInventoryAt
      (CanonicalUnitArithmeticRoot.emitted current.1).2)
  affectedInventoryPresentation := by
    intro current support event
    cases event with
    | generated =>
        exact DebtActivationWorld.activeInventoryPresentation
          (law := Idle.law registered.input.environment registered.input.expression) current.2.state
          (CanonicalUnitArithmeticRoot.source.law.affectedInventoryPresentation
            (CanonicalUnitArithmeticRoot.emitted current.1).2)
  anchorKey := CanonicalUnitArithmeticRoot.source.law.anchorKey
  incidenceKey := CanonicalUnitArithmeticRoot.source.law.incidenceKey
  lineageKey := CanonicalUnitArithmeticRoot.source.law.lineageKey
  anchor_commutes := by
    intro current support event
    cases event with
    | generated =>
        exact CanonicalUnitArithmeticRoot.source.law.anchor_commutes
          (CanonicalUnitArithmeticRoot.emitted current.1).2
  incidence_commutes := by
    intro current support event
    cases event with
    | generated =>
        exact CanonicalUnitArithmeticRoot.source.law.incidence_commutes
          (CanonicalUnitArithmeticRoot.emitted current.1).2
  lineage_commutes := by
    intro current support event
    cases event with
    | generated =>
        exact CanonicalUnitArithmeticRoot.source.law.lineage_commutes
          (CanonicalUnitArithmeticRoot.emitted current.1).2

def source : SourceNativeSource (World registered) (JointV registered) where
  initial := ⟨origin, initialEvent registered⟩
  law := eventAlgebra registered

def emitted (current : Current registered) : (source registered).toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt registered current, .generated current⟩

def oldOccurrence (current : Current registered) :
    CanonicalUnitArithmeticRoot.source.toRootSource.actual.OccurrenceAt current.1 :=
  CanonicalUnitArithmeticRoot.emitted current.1

def targetEvent (current : Current registered) :
    (source registered).toRootSource.actual.OccurrenceAt
      ((JointV registered).nativeTarget (native registered current)) :=
  emitted registered ((JointV registered).nativeTarget (native registered current))

end RootGeneratedDebtActivationJointSource.Unit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
