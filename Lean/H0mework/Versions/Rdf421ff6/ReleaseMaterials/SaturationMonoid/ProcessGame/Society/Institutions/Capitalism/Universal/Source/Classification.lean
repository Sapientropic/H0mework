import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Incidence

/-!
# Source-computed acquisition classification relative to an original relation family

The classifier reads executed authority ports, actual disposition rights
and paid reproduction from the original item-dependent effect.  No actor
membership in a population, institutional name or capitalism verdict enters
the computation.  Failure to find a dependency is not independence.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Relations Power

universe u

namespace ExistingSocietyFace.AcquisitionEffect

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource N V} (society : ExistingSocietyFace source)
  {current : V.Current} (event : ContinuingEventAt source current)
  {Good Quantity : Type u} [AddCommMonoid Quantity] [LinearOrder Quantity]
  {item : OriginalInventoryItem event}
  (effect : society.AcquisitionEffect event Good Quantity item)
  (R : society.Relation event → Prop)

/-- An actually used guard and source disposition right share the original
relation lineage and exact authorization.  This is the reproduction of the
control relation; positive realized profit is a separate stronger readout. -/
def DependentPath : Prop :=
  ∃ guard ∈ effect.requiredPorts, ∃ right ∈ effect.dispositionRights,
    R ((society.relations event).relationOf guard.relation) ∧
    R ((society.relations event).relationOf right.purpose) ∧
    ((society.relations event).relationOf guard.relation).val =
      ((society.relations event).relationOf right.purpose).val ∧
    guard.action.val = right.actualAuthorization.val ∧
    effect.recipient.actor (society.relations event) =
      guard.relation.actor (society.relations event)

def RealizedSurplusPath : Prop :=
  effect.DependentPath society event R ∧
  ∃ right ∈ effect.dispositionRights, ∃ surplus ∈ effect.surplusPorts,
    R ((society.relations event).relationOf surplus.purpose) ∧
    ((society.relations event).relationOf right.purpose).val =
      ((society.relations event).relationOf surplus.purpose).val ∧
    right.purpose.actor (society.relations event) =
      surplus.purpose.actor (society.relations event) ∧
    0 < surplus.effectiveAmount

/-- Independence is relative to R and requires all required authority and
surplus-right ports to avoid R.  A positive maintenance requirement also needs
an actual maintenance action, not merely an optimistic numeric readout. -/
def IndependentPath (good : Good) : Prop :=
  (∀ guard ∈ effect.requiredPorts,
    ¬ R ((society.relations event).relationOf guard.relation)) ∧
  (∀ right ∈ effect.dispositionRights,
    ¬ R ((society.relations event).relationOf right.purpose)) ∧
  (∀ surplus ∈ effect.surplusPorts,
    ¬ R ((society.relations event).relationOf surplus.purpose)) ∧
  effect.reproductionRequired good ≤ effect.reproductionPaid good ∧
  (0 < effect.reproductionRequired good → effect.maintenanceActions ≠ []) ∧
  effect.selfRequestAllowed = true

omit [AddCommMonoid Quantity] [LinearOrder Quantity] in
def dependentDecidable [DecidablePred R] :
    Decidable (effect.DependentPath society event R) := by
  letI := society.actionEquality (originalOccurrence event)
  letI := society.actorEquality event
  letI := society.relationEquality (originalOccurrence event)
  unfold DependentPath
  infer_instance

def independentDecidable [DecidablePred R] (good : Good) :
    Decidable (effect.IndependentPath society event R good) := by
  letI := society.actionEquality (originalOccurrence event)
  unfold IndependentPath
  infer_instance

def realizedSurplusDecidable [DecidablePred R] :
    Decidable (effect.RealizedSurplusPath society event R) := by
  letI := society.actorEquality event
  letI := society.relationEquality (originalOccurrence event)
  letI := effect.dependentDecidable society event R
  unfold RealizedSurplusPath
  infer_instance

theorem dependent_independent_disjoint (good : Good)
    (dependent : effect.DependentPath society event R)
    (independent : effect.IndependentPath society event R good) : False := by
  obtain ⟨guard, member, surplus, _surplusMember, inside, _rest⟩ := dependent
  exact independent.1 guard member inside

inductive Classification (good : Good) : Type u
  | dependent (path : effect.DependentPath society event R)
  | independent (path : effect.IndependentPath society event R good)
  | pending (notDependent : ¬ effect.DependentPath society event R)
      (notIndependent : ¬ effect.IndependentPath society event R good)

/-- The source's raw ports determine all three outcomes.  Neither a desired
class nor a residual bearer is an argument of this producer. -/
def classify [DecidablePred R] (good : Good) :
    effect.Classification society event R good := by
  letI := effect.dependentDecidable society event R
  letI := effect.independentDecidable society event R good
  exact if dependent : effect.DependentPath society event R then .dependent dependent
    else if independent : effect.IndependentPath society event R good then .independent independent
    else .pending dependent independent

def dependentAmount [DecidablePred R] (good : Good) : Quantity :=
  match effect.classify society event R good with
  | .dependent _ => effect.acquired good
  | .independent _ | .pending _ _ => 0

def independentAmount [DecidablePred R] (good : Good) : Quantity :=
  match effect.classify society event R good with
  | .independent _ => effect.acquired good
  | .dependent _ | .pending _ _ => 0

def pendingAmount [DecidablePred R] (good : Good) : Quantity :=
  match effect.classify society event R good with
  | .pending _ _ => effect.acquired good
  | .dependent _ | .independent _ => 0

theorem partition_exact [DecidablePred R] (good : Good) :
    effect.dependentAmount society event R good + effect.independentAmount society event R good +
        effect.pendingAmount society event R good = effect.acquired good := by
  unfold dependentAmount independentAmount pendingAmount
  cases effect.classify society event R good <;> simp

theorem amounts_nonnegative [DecidablePred R] (good : Good)
    (nonnegative : 0 ≤ effect.acquired good) :
    0 ≤ effect.dependentAmount society event R good ∧
    0 ≤ effect.independentAmount society event R good ∧
    0 ≤ effect.pendingAmount society event R good := by
  unfold dependentAmount independentAmount pendingAmount
  cases effect.classify society event R good <;> simp [nonnegative]

theorem positive_dependent_has_actual_path [DecidablePred R] (good : Good)
    (positive : 0 < effect.dependentAmount society event R good) :
    effect.DependentPath society event R := by
  unfold dependentAmount at positive
  cases selected : effect.classify society event R good with
  | dependent path => exact path
  | independent path =>
      simp only [selected] at positive
      exact False.elim ((lt_irrefl (0 : Quantity)) positive)
  | pending notDependent notIndependent =>
      simp only [selected] at positive
      exact False.elim ((lt_irrefl (0 : Quantity)) positive)

theorem positive_independent_has_authority_and_maintenance [DecidablePred R] (good : Good)
    (positive : 0 < effect.independentAmount society event R good) :
    effect.IndependentPath society event R good := by
  unfold independentAmount at positive
  cases selected : effect.classify society event R good with
  | dependent path =>
      simp only [selected] at positive
      exact False.elim ((lt_irrefl (0 : Quantity)) positive)
  | independent path => exact path
  | pending notDependent notIndependent =>
      simp only [selected] at positive
      exact False.elim ((lt_irrefl (0 : Quantity)) positive)

/-- The pending amount retains this effect's original item, its exact claim
and the original compiler disposition.  It does not assert that a terminal
disposition is live or that the material uncertainty has been discharged. -/
theorem pending_row_is_this_effect [DecidablePred R] (good : Good)
    (_positive : 0 < effect.pendingAmount society event R good) :
    (source.source.law.affectedInventoryPresentation event.val.2).backward
        (effect.bearerRow society event) = item ∧
    (effect.bearerRow society event).claim = (originalRow event item).claim ∧
    effect.actualDisposition society event =
      (source.ledgerCompiler.compile event.val).entryDisposition (originalRow event item) :=
  ⟨originalRow_recovers_item event item, rfl, rfl⟩

theorem required_R_without_surplus_is_not_independent (good : Good)
    (guard : society.RequiredAuthorityPort event) (member : guard ∈ effect.requiredPorts)
    (inside : R ((society.relations event).relationOf guard.relation)) :
    ¬ effect.IndependentPath society event R good := by
  intro independent
  exact independent.1 guard member inside

end ExistingSocietyFace.AcquisitionEffect

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source
