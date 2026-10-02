import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Recovery

/-! The original heterogeneous compiler equality induces a full typed
equivalence between the two formed compiler images. It does not assert
heterogeneous equality between their different native representation types. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
namespace AdmissionTransport

private theorem cast_of_heq {A C : Type} {left : A} {right : C} (same : HEq left right) :
    Equiv.cast (type_eq_of_heq same) left = right := by
  cases same
  rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
  {old : SourceNativeRestructuringLedgerSource N V}
  (admission : SourceNativeCompleteEventInventoryAdmission old)
  (value : SourcePair)
  (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
  (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
  (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
  (p : MotherNativeSourceOrigin.Presentation n v old.source (Represented value).source)
  (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)

def compilationAcross (current : V.Current)
    (event : admission.actualSource.source.toRootSource.actual.OccurrenceAt (admission.currentPresentation.backward current)) :
    SourceNativeLedgerEvolutionAt (Represented value).source
      (p.event current ((admission.occurrencePresentation current).forward event)) ≃
    SourceNativeLedgerEvolutionAt value.2.2.source (a.event _ event) :=
  (fullCompilationEquiv p ((admission.occurrencePresentation current).forward event)).symm.trans
    ((Equiv.cast (type_eq_of_heq (admission.wholeLedgerWriteBack_commutes current event))).trans
      (fullCompilationEquiv a event))

variable
  (representedRecovers : ∀ current event,
    (fullCompilationEquiv p event).symm ((Represented value).compiler.ledgerCompiler.compile (p.event current event)) =
      old.compiler.ledgerCompiler.compile event)
  (actualRecovers : ∀ current event,
    (fullCompilationEquiv a event).symm (value.2.2.ledgerCompiler.compile (a.event current event)) =
      admission.actualSource.ledgerCompiler.compile event)

include representedRecovers actualRecovers in
/-- Both entire generated Compilation values commute through the original
admission, including all target occurrences and both complete ledger tables. -/
theorem compilationAcross_compile (current : V.Current)
    (event : admission.actualSource.source.toRootSource.actual.OccurrenceAt (admission.currentPresentation.backward current)) :
    compilationAcross admission value n v w p a current event
      ((Represented value).compiler.ledgerCompiler.compile
        (p.event current ((admission.occurrencePresentation current).forward event))) =
      value.2.2.ledgerCompiler.compile (a.event _ event) := by
  let transport := Equiv.cast (type_eq_of_heq (admission.wholeLedgerWriteBack_commutes current event))
  exact (congrArg (fun compiled => fullCompilationEquiv a event (transport compiled))
    (representedRecovers current ((admission.occurrencePresentation current).forward event))).trans
      ((congrArg (fullCompilationEquiv a event) (cast_of_heq (admission.wholeLedgerWriteBack_commutes current event))).trans
        ((congrArg (fullCompilationEquiv a event) (actualRecovers _ event)).symm.trans
          ((fullCompilationEquiv a event).apply_symm_apply _)))

include representedRecovers actualRecovers in
theorem restored_compilations_heq (current : V.Current)
    (event : admission.actualSource.source.toRootSource.actual.OccurrenceAt (admission.currentPresentation.backward current)) :
    HEq
      ((fullCompilationEquiv p ((admission.occurrencePresentation current).forward event)).symm
        ((Represented value).compiler.ledgerCompiler.compile
          (p.event current ((admission.occurrencePresentation current).forward event))))
      ((fullCompilationEquiv a event).symm (value.2.2.ledgerCompiler.compile (a.event _ event))) := by
  rw [representedRecovers, actualRecovers]
  exact admission.wholeLedgerWriteBack_commutes current event

end AdmissionTransport
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
