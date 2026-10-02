import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRestriction.Declaration

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRestriction
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeAuthoritySource N V} {original generated : EventFamily source}
    (events : ∀ index, original index ≃ generated index)

def eventPointEquiv : EventPoint original ≃ EventPoint generated :=
  Equiv.sigmaCongr (Equiv.refl (Index source)) events

def forwardContinuation (point : EventPoint original) (value : Continuation original point) :
    Continuation generated (eventPointEquiv events point) where
  next := value.next
  occurrencePresentation := presentationFromEquiv ((presentationEquiv value.occurrencePresentation).trans (events point.1))
  occurrence_commutes := congrArg (events point.1) value.occurrence_commutes
  lawSurface_eq := value.lawSurface_eq
  targetDebtOrigin := value.targetDebtOrigin
  sameDebtBudget_not_refilled := value.sameDebtBudget_not_refilled
  sameDebtTarget_unique := value.sameDebtTarget_unique

def backwardContinuation (point : EventPoint original)
    (value : Continuation generated (eventPointEquiv events point)) : Continuation original point where
  next := value.next
  occurrencePresentation := presentationFromEquiv ((presentationEquiv value.occurrencePresentation).trans (events point.1).symm)
  occurrence_commutes := (congrArg (events point.1).symm value.occurrence_commutes).trans
    ((events point.1).symm_apply_apply point.2)
  lawSurface_eq := value.lawSurface_eq
  targetDebtOrigin := value.targetDebtOrigin
  sameDebtBudget_not_refilled := value.sameDebtBudget_not_refilled
  sameDebtTarget_unique := value.sameDebtTarget_unique

private theorem continuation_ext {events : EventFamily source} {point : EventPoint events}
    (first last : Continuation events point) (next : first.next = last.next)
    (presentation : HEq first.occurrencePresentation last.occurrencePresentation)
    (debt : HEq first.targetDebtOrigin last.targetDebtOrigin) : first = last := by
  cases first
  cases last
  cases next
  cases eq_of_heq presentation
  cases eq_of_heq debt
  rfl

def continuationEquiv (point : EventPoint original) :
    Continuation original point ≃ Continuation generated (eventPointEquiv events point) where
  toFun := forwardContinuation events point
  invFun := backwardContinuation events point
  left_inv := fun value => continuation_ext _ _ rfl
    (heq_of_eq (presentation_conjugate_recovers (Equiv.refl _) (events point.1) value.occurrencePresentation)) HEq.rfl
  right_inv := fun value => continuation_ext _ _ rfl
    (heq_of_eq (presentation_conjugate_recovers (Equiv.refl _) (events point.1).symm value.occurrencePresentation)) HEq.rfl

private theorem declaration_ext {events : EventFamily source} (first last : Declaration source events)
    (emit : first.emit = last.emit) (continuation : first.continuation = last.continuation) : first = last := by
  cases first
  cases last
  cases emit
  cases continuation
  rfl

/-- Whole-law reindexing retains every event fiber and every full successor
packet. The inverse reads all programs from the actual generated declaration. -/
def declarationEquiv : Declaration source original ≃ Declaration source generated where
  toFun := fun value => {
    emit := fun index => events index (value.emit index)
    continuation := Equiv.piCongr (eventPointEquiv events) (continuationEquiv events) value.continuation }
  invFun := fun value => {
    emit := fun index => (events index).symm (value.emit index)
    continuation := (Equiv.piCongr (eventPointEquiv events) (continuationEquiv events)).symm value.continuation }
  left_inv := fun value => declaration_ext _ _
    (funext fun index => (events index).symm_apply_apply (value.emit index))
    ((Equiv.piCongr (eventPointEquiv events) (continuationEquiv events)).symm_apply_apply value.continuation)
  right_inv := fun value => declaration_ext _ _
    (funext fun index => (events index).apply_symm_apply (value.emit index))
    ((Equiv.piCongr (eventPointEquiv events) (continuationEquiv events)).apply_symm_apply value.continuation)

def restrictDeclaration (actual : Declaration source generated) : Declaration source original :=
  (declarationEquiv events).symm actual

theorem restrictDeclaration_recovers (old : Declaration source original) :
    restrictDeclaration events (declarationEquiv events old) = old :=
  (declarationEquiv events).symm_apply_apply old

theorem actual_sealed_recovers (old : Declaration source original) (actual : Declaration source generated)
    (formed : actual = declarationEquiv events old) :
    assembleLaw (restrictDeclaration events actual) = assembleLaw old :=
  congrArg assembleLaw ((congrArg (declarationEquiv events).symm formed).trans
    ((declarationEquiv events).symm_apply_apply old))

def restrictActualLaw (actual : SourceNativeTerminalHandoffLaw source)
    (schema : eventsOf actual = generated) : SourceNativeTerminalHandoffLaw source :=
  restrictSealed actual schema (declarationEquiv events).symm

/-- Recovery consumes the actual sealed law, not a copied original record.
The schema equality is the literal identity supplied by source construction. -/
theorem actual_law_recovers (old : Declaration source original) (actual : Declaration source generated)
    (formed : actual = declarationEquiv events old) :
    restrictActualLaw events (assembleLaw actual) (eventsOf_assemble actual) = assembleLaw old :=
  (restrictSealed_assemble actual (declarationEquiv events).symm).trans
    (actual_sealed_recovers events old actual formed)

/-- Transport the entire sealed law when the actual authority-source
restriction has already supplied literal source equality. -/
def sourceEquiv {first last : SourceNativeAuthoritySource N V} (same : first = last) :
    SourceNativeTerminalHandoffLaw first ≃ SourceNativeTerminalHandoffLaw last :=
  Equiv.cast (congrArg SourceNativeTerminalHandoffLaw same)

theorem source_restriction_recovers {first last : SourceNativeAuthoritySource N V}
    (same : first = last) (law : SourceNativeTerminalHandoffLaw first) :
    (sourceEquiv same).symm (sourceEquiv same law) = law :=
  (sourceEquiv same).symm_apply_apply law

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRestriction
