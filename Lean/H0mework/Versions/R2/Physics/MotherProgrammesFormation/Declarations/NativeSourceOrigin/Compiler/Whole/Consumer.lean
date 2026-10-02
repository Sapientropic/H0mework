import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Transport
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)

def sectionTargets (compiled : CompilationSection source) : TargetSection source := fun point =>
  (bodyEquiv source point.2 (source.toRootSource.actual.compile point.2)
    (compilationEquiv source point.2 (compiled point))).1

def sectionLedgers (compiled : CompilationSection source) : WholeSection source (sectionTargets source compiled) := fun point =>
  (bodyEquiv source point.2 (source.toRootSource.actual.compile point.2)
    (compilationEquiv source point.2 (compiled point))).2

theorem compilationFromSection (compiled : CompilationSection source) :
    compilationFromWhole source (sectionTargets source compiled) (sectionLedgers source compiled) = compiled := by
  funext point
  unfold compilationFromWhole sectionTargets sectionLedgers
  rw [Sigma.eta, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The original compiler enters coverage and the consumer only. One mother
material forms the source, actual targets and full ledger values, which
restore the complete original compilation at every original event. -/
theorem formed_compilation_recovers_original_values (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (encode : MotherNativeSourceOrigin.Total original ↪ B)
    (compiler : SourceNativeLedgerCompiler original) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
        formCompilation material = some ⟨⟨G, W, generated⟩, compiled⟩ ∧
        ∀ point : Sigma original.toRootSource.actual.OccurrenceAt,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2 := by
  obtain ⟨sourceMaterial, G, W, generated, n, v, formed, ⟨p⟩⟩ :=
    MotherNativeSourceOrigin.every_jointly_embedded_source N V original encode
  obtain ⟨coordinates, sourceFormed⟩ := coordinates_generated sourceMaterial ⟨G, W, generated⟩ formed
  let compiled := compilationSectionEquiv p (originalCompilations compiler)
  obtain ⟨parent, targets, targetFormed, targetEq⟩ :=
    every_target_section sourceMaterial ⟨G, W, generated⟩ coordinates sourceFormed (sectionTargets generated compiled)
  cases targetEq
  obtain ⟨material, ledgers, wholeFormed, wholeEq⟩ :=
    every_whole_section parent ⟨G, W, generated⟩ coordinates (sectionTargets generated compiled)
      targetFormed (sectionLedgers generated compiled)
  refine ⟨material, G, W, generated, compiled, n, v, p, ?_, ?_⟩
  · rw [formCompilation, wholeFormed, Option.map_some, wholeEq]
    dsimp only
    rw [compilationFromSection]
  · exact full_original_compilation_recovers p compiler

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
