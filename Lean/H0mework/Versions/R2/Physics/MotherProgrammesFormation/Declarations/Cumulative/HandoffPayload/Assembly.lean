import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeAuthoritySource N V} {events : EventFamily source}
    (next : EventPoint events → NextRoot N)

/-- These are exactly the original proof fields. Their evidence is carried
through the full value recovery; this is not another admission procedure. -/
structure Laws (values : Values next) : Prop where
  occurrence_commutes : ∀ point,
    (values.occurrencePresentation point).forward ((next point).2.emitted (next point).2.toRoot.source.initial) = point.2
  lawSurface_eq : ∀ point, (next point).2.source.lawSurface = source.lawSurface
  sameDebtBudget_not_refilled : ∀ point,
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence)) →
    (targetEntry : TargetEntry next point) →
    RootDebtLineageAt N sourceEntry targetEntry → targetEntry.progressBudget ≤ sourceEntry.progressBudget
  sameDebtTarget_unique : ∀ point,
    (sourceEntry : OpenResponsibilityAt N
      (source.restructuringSource.source.toRootSource.account.supportOf point.1.occurrence)) →
    (first last : TargetEntry next point) →
    RootDebtLineageAt N sourceEntry first → RootDebtLineageAt N sourceEntry last → first = last

def assemble (emit : ∀ index, events index) (values : Values next) (laws : Laws next values) : Declaration source events where
  emit := emit
  continuation := fun point => {
    next := next point
    occurrencePresentation := values.occurrencePresentation point
    occurrence_commutes := laws.occurrence_commutes point
    lawSurface_eq := laws.lawSurface_eq point
    targetDebtOrigin := fun target => values.targetDebtOrigin ⟨point, target⟩
    sameDebtBudget_not_refilled := laws.sameDebtBudget_not_refilled point
    sameDebtTarget_unique := laws.sameDebtTarget_unique point }

def valuesOf (declaration : Declaration source events) :
    Values (fun point => (declaration.continuation point).next) where
  occurrencePresentation := fun point => (declaration.continuation point).occurrencePresentation
  targetDebtOrigin := fun point => (declaration.continuation point.1).targetDebtOrigin point.2

theorem lawsOf (declaration : Declaration source events) :
    Laws (fun point => (declaration.continuation point).next) (valuesOf declaration) where
  occurrence_commutes := fun point => (declaration.continuation point).occurrence_commutes
  lawSurface_eq := fun point => (declaration.continuation point).lawSurface_eq
  sameDebtBudget_not_refilled := fun point => (declaration.continuation point).sameDebtBudget_not_refilled
  sameDebtTarget_unique := fun point => (declaration.continuation point).sameDebtTarget_unique

theorem assemble_valuesOf (declaration : Declaration source events) :
    assemble (fun point => (declaration.continuation point).next) declaration.emit
      (valuesOf declaration) (lawsOf declaration) = declaration := by
  cases declaration
  rfl

theorem recovered_laws (declaration : Declaration source events)
    (actual : Values (fun point => (declaration.continuation point).next))
    (same : actual = valuesOf declaration) : Laws (fun point => (declaration.continuation point).next) actual := by
  rw [same]
  exact lawsOf declaration

/-- Whole dependent assembly consumes the actual generated value functions.
The old declaration is used only to prove recovery and retain its paid laws. -/
theorem actual_assembly_recovers (declaration : Declaration source events)
    (emit : ∀ index, events index) (emit_eq : emit = declaration.emit)
    (actual : Values (fun point => (declaration.continuation point).next))
    (same : actual = valuesOf declaration) :
    assemble (fun point => (declaration.continuation point).next) emit actual
      (recovered_laws declaration actual same) = declaration := by
  cases emit_eq
  cases same
  exact assemble_valuesOf declaration

private theorem lawsAtRestoredRoots {schema restored : EventPoint events → NextRoot N}
    (same : restored = schema) (values : Values schema) (laws : Laws schema values) :
    Laws restored (Equiv.cast (congrArg Values same.symm) values) := by
  cases same
  exact laws

/-- The next-vocabulary/root function is the actual complete root readback.
Only inverse type indices and the equality proof mention the old family. -/
def assembleRestored (schema restored : EventPoint events → NextRoot N)
    (same : restored = schema) (emit : ∀ index, events index)
    (values : Values schema) (laws : Laws schema values) : Declaration source events :=
  assemble restored emit (Equiv.cast (congrArg Values same.symm) values)
    (lawsAtRestoredRoots same values laws)

theorem assembleRestored_eq (schema restored : EventPoint events → NextRoot N)
    (same : restored = schema) (emit : ∀ index, events index)
    (values : Values schema) (laws : Laws schema values) :
    assembleRestored schema restored same emit values laws = assemble schema emit values laws := by
  cases same
  rfl

theorem assembleRestored_recovers (declaration : Declaration source events)
    (restored : EventPoint events → NextRoot N)
    (rootsSame : restored = fun point => (declaration.continuation point).next)
    (emit : ∀ index, events index) (emit_eq : emit = declaration.emit)
    (actual : Values (fun point => (declaration.continuation point).next))
    (same : actual = valuesOf declaration) :
    assembleRestored (fun point => (declaration.continuation point).next) restored rootsSame emit actual
      (recovered_laws declaration actual same) = declaration :=
  (assembleRestored_eq _ restored rootsSame emit actual (recovered_laws declaration actual same)).trans
    (actual_assembly_recovers declaration emit emit_eq actual same)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
