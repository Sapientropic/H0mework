import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.AdmissionRestriction

/-! The source-only declaration factory is consumed through its actual
Option/Sigma output. Both complete native headers and every original
admission field are recovered at the original indices. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherInventoryAdmission MotherAdmissionAlignment MotherAdmissionRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- One formed material pays both complete compiler/source headers and the
four dependent presentation programs. The final restriction reads their
actual factory output and restores the whole original admission. -/
theorem every_original_admission_recovered (N : WorldRelationNetwork.{0})
    (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V)
    (admission : SourceNativeCompleteEventInventoryAdmission root.source.restructuringSource) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formDeclarationData material).isSome,
        let output := (formDeclarationData material).get available
        ∃ n : MotherNetworkOrigin.Presentation N output.1.1.1.1.1.1,
        ∃ v : MotherVocabularyOrigin.Presentation V (RepresentedV output.1),
        ∃ w : MotherVocabularyOrigin.Presentation admission.ActualV output.1.2.1,
        ∃ p : MotherNativeSourceOrigin.Presentation n v root.source.restructuringSource.source
          (Represented output.1).source,
        ∃ a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source output.1.2.2.source,
        ∃ lowerCompiler : CompilerPresentation p root.source.restructuringSource.compiler.ledgerCompiler
          (Represented output.1).compiler.ledgerCompiler,
        ∃ actualCompiler : CompilerPresentation a admission.actualSource.ledgerCompiler output.1.2.2.ledgerCompiler,
        ∃ dataSame : output.2 = AdmissionTransport.transportedData admission output.1 n v w p a,
          lowerCompiler.restrictHeader = ⟨V, root.source.restructuringSource.toLedgerSource⟩ ∧
          actualCompiler.restrictHeader = ⟨admission.ActualV, admission.actualSource⟩ ∧
          restrictAdmission root.source.restructuringSource ⟨admission.ActualV, admission.actualSource⟩
            output.1 n v w p a actualCompiler
            (originalDataInImage admission output.1 n v w p a output.2 dataSame) = admission ∧
          ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
            Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
              (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, material, value, n, v, w, p, a, lowerCompiler, actualCompiler, formed, original⟩ :=
    every_original_admission_data N V root admission
  have available : (formDeclarationData material).isSome := by
    rw [formed]
    rfl
  have outputSame : (formDeclarationData material).get available =
      ⟨value, AdmissionTransport.transportedData admission value n v w p a⟩ :=
    Option.some.inj ((Option.some_get available).trans formed)
  refine ⟨rank, material, available, ?_⟩
  dsimp only
  rw [outputSame]
  exact ⟨n, v, w, p, a, lowerCompiler, actualCompiler, rfl,
    lowerCompiler.restrictHeader_eq, actualCompiler.restrictHeader_eq,
    original_admission_restricted admission value n v w p a actualCompiler
      (AdmissionTransport.transportedData admission value n v w p a) rfl,
    original⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
