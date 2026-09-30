import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.NativeCompiler

/-! The original native admission consumes both complete recovered compiler
outputs. Its existing two heterogeneous equalities apply in their original
indices; no equality of freshly formed source types is introduced. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeRestructuringLedgerSource N V}
    (admission : SourceNativeCompleteEventInventoryAdmission original)
    (value : SourcePair)
    (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
    (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
    (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
    (p : MotherNativeSourceOrigin.Presentation n v original.source (Represented value).source)
    (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)
    (representedCompiler : CompilerPresentation p original.compiler.ledgerCompiler
      (Represented value).compiler.ledgerCompiler)
    (actualCompiler : CompilerPresentation a admission.actualSource.ledgerCompiler value.2.2.ledgerCompiler)

/-- Both signed compiler images are read as whole dependent pairs. Their
complete original values satisfy the original admission without readmission. -/
theorem recovered_admission_fields (current : V.Current)
    (event : admission.actualSource.source.toRootSource.actual.OccurrenceAt
      (admission.currentPresentation.backward current)) :
    HEq
      (representedCompiler.restore ⟨current, (admission.occurrencePresentation current).forward event⟩).1
      (actualCompiler.restore ⟨admission.currentPresentation.backward current, event⟩).1 ∧
    HEq
      (representedCompiler.restore ⟨current, (admission.occurrencePresentation current).forward event⟩).2
      (actualCompiler.restore ⟨admission.currentPresentation.backward current, event⟩).2 := by
  constructor
  · exact (heq_of_eq (representedCompiler.restore_compile
      ⟨current, (admission.occurrencePresentation current).forward event⟩)).trans
      ((admission.wholeLedgerWriteBack_commutes current event).trans
        (heq_of_eq (actualCompiler.restore_compile ⟨admission.currentPresentation.backward current, event⟩)).symm)
  · exact (representedCompiler.restore_patch
      ⟨current, (admission.occurrencePresentation current).forward event⟩).trans
      ((admission.finitePatch_commutes current event).trans
        (actualCompiler.restore_patch ⟨admission.currentPresentation.backward current, event⟩).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
