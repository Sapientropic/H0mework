import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeCoverage
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

theorem compilation_on_source {rank : Ordinal.{0}}
    {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original)
    (sourceMaterial : MotherArenaHigher.Material rank)
    (formed : MotherArenaSource.formSource sourceMaterial = some ⟨G, W, generated⟩) :
    ∃ material : MotherArenaHigher.Material rank, ∃ compiled : CompilationSection generated,
      formCompilation material = some ⟨⟨G, W, generated⟩, compiled⟩ ∧
      ∀ point : Sigma original.toRootSource.actual.OccurrenceAt,
        (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2 := by
  obtain ⟨coordinates, sourceFormed⟩ := coordinates_generated sourceMaterial ⟨G, W, generated⟩ formed
  let compiled := compilationSectionEquiv p (originalCompilations compiler)
  obtain ⟨parent, targets, targetFormed, targetEq⟩ :=
    every_target_section sourceMaterial ⟨G, W, generated⟩ coordinates sourceFormed (sectionTargets generated compiled)
  cases targetEq
  obtain ⟨material, ledgers, wholeFormed, wholeEq⟩ :=
    every_whole_section parent ⟨G, W, generated⟩ coordinates (sectionTargets generated compiled)
      targetFormed (sectionLedgers generated compiled)
  refine ⟨material, compiled, ?_, full_original_compilation_recovers p compiler⟩
  rw [formCompilation, wholeFormed, Option.map_some, wholeEq]
  dsimp only
  rw [compilationFromSection]

/-- A source-only rank material forms every complete original compilation
value on all original events. Targets and both entire ledger tables use the
existing native fullCompilationEquiv; no row or branch payload is replaced. -/
theorem every_compilation (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0},
        ∃ generated : SourceNativeSource G W, ∃ compiled : CompilationSection generated,
          ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
            ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
              formCompilation material = some ⟨⟨G, W, generated⟩, compiled⟩ ∧
              (∀ point : Sigma original.toRootSource.actual.OccurrenceAt,
                (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) ∧
              ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
                Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
                  (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, sourceMaterial, G, W, generated, n, v, p, formed, _sourceExact, originalAddress, retained⟩ :=
    MotherArenaSource.every_source N V original
  obtain ⟨material, compiled, compilerFormed, recover⟩ := compilation_on_source p compiler sourceMaterial formed
  exact ⟨rank, material, G, W, generated, compiled, n, v, p, compilerFormed, recover, originalAddress, retained⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
