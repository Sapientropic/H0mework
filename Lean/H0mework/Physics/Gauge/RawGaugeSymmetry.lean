import H0mework.Realization.Relations.FintypeDerivation
import Mathlib

/-!
# Raw gauge operations and independent invariance laws

The gauge parameter carrier may already be a group, but the action on fields
is kept as a plain function.  Identity/composition, invariance of the action
functional, and invariance of an observable are all computed predicates.  No
`MulAction`, invariance certificate, or final admissibility proposition is
stored in the raw structure.

The integer-translation models below show that these three native laws are
independent.  They are algebraic gauge models, not yet the concrete SU(3)
conjugation system from Proposition 348.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uGauge uField uActionValue uObservable

structure RawGaugeOperations
    (Gauge : Type uGauge) (Field : Type uField)
    (ActionValue : Type uActionValue) (Observable : Type uObservable) where
  act : Gauge → Field → Field
  actionFunctional : Field → ActionValue
  observable : Field → Observable

namespace RawGaugeOperations

variable {Gauge : Type uGauge} {Field : Type uField}
variable {ActionValue : Type uActionValue} {Observable : Type uObservable}

/-- The plain action function respects the additive gauge-group laws. -/
def GaugeActionLawful
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable) : Prop :=
  (∀ field : Field, S.act 0 field = field) ∧
    (∀ gauge₁ gauge₂ : Gauge, ∀ field : Field,
      S.act (gauge₁ + gauge₂) field =
        S.act gauge₁ (S.act gauge₂ field))

def ActionFunctionalGaugeInvariant
    (S : RawGaugeOperations Gauge Field ActionValue Observable) : Prop :=
  ∀ gauge : Gauge, ∀ field : Field,
    S.actionFunctional (S.act gauge field) = S.actionFunctional field

def ObservableGaugeInvariant
    (S : RawGaugeOperations Gauge Field ActionValue Observable) : Prop :=
  ∀ gauge : Gauge, ∀ field : Field,
    S.observable (S.act gauge field) = S.observable field

def GaugeAdmissible
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable) : Prop :=
  S.GaugeActionLawful ∧
    S.ActionFunctionalGaugeInvariant ∧
      S.ObservableGaugeInvariant

inductive GaugeCoordinate where
  | actionLaw
  | actionFunctionalInvariance
  | observableInvariance
  deriving DecidableEq, Repr, FintypeViaProxy

def CoordinateHolds
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable) :
    GaugeCoordinate → Prop
  | .actionLaw => S.GaugeActionLawful
  | .actionFunctionalInvariance => S.ActionFunctionalGaugeInvariant
  | .observableInvariance => S.ObservableGaugeInvariant

theorem gaugeAdmissible_iff_all_coordinates
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable) :
    S.GaugeAdmissible ↔ ∀ c, S.CoordinateHolds c := by
  constructor
  · rintro ⟨hlaw, haction, hobservable⟩ c
    cases c with
    | actionLaw => exact hlaw
    | actionFunctionalInvariance => exact haction
    | observableInvariance => exact hobservable
  · intro hall
    exact ⟨hall .actionLaw, hall .actionFunctionalInvariance,
      hall .observableInvariance⟩

theorem not_gaugeAdmissible_iff_exists_failed_coordinate
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable) :
    ¬ S.GaugeAdmissible ↔ ∃ c, ¬ S.CoordinateHolds c := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push Not at hnone
    exact hnot (S.gaugeAdmissible_iff_all_coordinates.mpr hnone)
  · rintro ⟨c, hc⟩ hadmissible
    exact hc (S.gaugeAdmissible_iff_all_coordinates.mp hadmissible c)

def OnlyFails
    [AddGroup Gauge]
    (S : RawGaugeOperations Gauge Field ActionValue Observable)
    (failed : GaugeCoordinate) : Prop :=
  ¬ S.CoordinateHolds failed ∧
    ∀ c, c ≠ failed → S.CoordinateHolds c

namespace RawGaugeOperationsToy

abbrev System := RawGaugeOperations ℤ ℤ ℤ ℤ

def translationAction : ℤ → ℤ → ℤ :=
  fun gauge field => gauge + field

def admissibleSystem : System where
  act := translationAction
  actionFunctional := fun _ => 0
  observable := fun _ => 0

/-- A malformed action, while both readouts remain invariant constants. -/
def actionLawFailureSystem : System where
  act := fun _ _ => 0
  actionFunctional := fun _ => 0
  observable := fun _ => 0

/-- The translation action is lawful, but the action value leaks gauge. -/
def actionFunctionalFailureSystem : System where
  act := translationAction
  actionFunctional := id
  observable := fun _ => 0

/-- The translation action and action functional are sound, but the reported
observable leaks gauge. -/
def observableFailureSystem : System where
  act := translationAction
  actionFunctional := fun _ => 0
  observable := id

theorem translationAction_lawful
    (actionFunctional observable : ℤ → ℤ) :
    GaugeActionLawful
      (⟨translationAction, actionFunctional, observable⟩ : System) := by
  constructor
  · intro field
    simp [translationAction]
  · intro gauge₁ gauge₂ field
    simp [translationAction, add_assoc]

theorem constant_actionFunctional_invariant
    (act : ℤ → ℤ → ℤ) (observable : ℤ → ℤ) :
    ActionFunctionalGaugeInvariant
      (⟨act, fun _ => 0, observable⟩ : System) := by
  intro gauge field
  rfl

theorem constant_observable_invariant
    (act : ℤ → ℤ → ℤ) (actionFunctional : ℤ → ℤ) :
    ObservableGaugeInvariant
      (⟨act, actionFunctional, fun _ => 0⟩ : System) := by
  intro gauge field
  rfl

theorem admissibleSystem_admissible : admissibleSystem.GaugeAdmissible :=
  ⟨translationAction_lawful _ _, constant_actionFunctional_invariant _ _,
    constant_observable_invariant _ _⟩

theorem actionLawFailureSystem_not_lawful :
    ¬ actionLawFailureSystem.GaugeActionLawful := by
  rintro ⟨hidentity, hcomposition⟩
  have hvalue := hidentity 1
  norm_num [actionLawFailureSystem] at hvalue

theorem actionLawFailureSystem_action_invariant :
    actionLawFailureSystem.ActionFunctionalGaugeInvariant :=
  constant_actionFunctional_invariant _ _

theorem actionLawFailureSystem_observable_invariant :
    actionLawFailureSystem.ObservableGaugeInvariant :=
  constant_observable_invariant _ _

theorem actionFunctionalFailureSystem_lawful :
    actionFunctionalFailureSystem.GaugeActionLawful :=
  translationAction_lawful _ _

theorem actionFunctionalFailureSystem_not_action_invariant :
    ¬ actionFunctionalFailureSystem.ActionFunctionalGaugeInvariant := by
  intro hinvariant
  have hvalue := hinvariant 1 0
  norm_num [actionFunctionalFailureSystem, translationAction] at hvalue

theorem actionFunctionalFailureSystem_observable_invariant :
    actionFunctionalFailureSystem.ObservableGaugeInvariant :=
  constant_observable_invariant _ _

theorem observableFailureSystem_lawful :
    observableFailureSystem.GaugeActionLawful :=
  translationAction_lawful _ _

theorem observableFailureSystem_action_invariant :
    observableFailureSystem.ActionFunctionalGaugeInvariant :=
  constant_actionFunctional_invariant _ _

theorem observableFailureSystem_not_observable_invariant :
    ¬ observableFailureSystem.ObservableGaugeInvariant := by
  intro hinvariant
  have hvalue := hinvariant 1 0
  norm_num [observableFailureSystem, translationAction] at hvalue

theorem actionLawFailureSystem_onlyFails :
    actionLawFailureSystem.OnlyFails .actionLaw := by
  refine ⟨actionLawFailureSystem_not_lawful, ?_⟩
  intro c hc
  cases c with
  | actionLaw => exact (hc rfl).elim
  | actionFunctionalInvariance =>
      exact actionLawFailureSystem_action_invariant
  | observableInvariance => exact actionLawFailureSystem_observable_invariant

theorem actionFunctionalFailureSystem_onlyFails :
    actionFunctionalFailureSystem.OnlyFails
      .actionFunctionalInvariance := by
  refine ⟨actionFunctionalFailureSystem_not_action_invariant, ?_⟩
  intro c hc
  cases c with
  | actionLaw => exact actionFunctionalFailureSystem_lawful
  | actionFunctionalInvariance => exact (hc rfl).elim
  | observableInvariance =>
      exact actionFunctionalFailureSystem_observable_invariant

theorem observableFailureSystem_onlyFails :
    observableFailureSystem.OnlyFails .observableInvariance := by
  refine ⟨observableFailureSystem_not_observable_invariant, ?_⟩
  intro c hc
  cases c with
  | actionLaw => exact observableFailureSystem_lawful
  | actionFunctionalInvariance => exact observableFailureSystem_action_invariant
  | observableInvariance => exact (hc rfl).elim

theorem every_gaugeCoordinate_has_only_one_failure_model
    (c : GaugeCoordinate) :
    ∃ S : System, S.OnlyFails c := by
  cases c with
  | actionLaw => exact ⟨actionLawFailureSystem,
      actionLawFailureSystem_onlyFails⟩
  | actionFunctionalInvariance =>
      exact ⟨actionFunctionalFailureSystem,
        actionFunctionalFailureSystem_onlyFails⟩
  | observableInvariance =>
      exact ⟨observableFailureSystem, observableFailureSystem_onlyFails⟩

end RawGaugeOperationsToy

end RawGaugeOperations
end PhysicsCore
end SaturationMonoid
