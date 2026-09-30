import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Compilation
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {U7 : U7ProducerCalculus N}
    (source : U7ActualSuccessorSource N U7)
    (index : EventTotal source ↪ MotherArenaHigher.Base rank)
    (member : ∀ point, DispositionAt source point ↪ MotherArenaHigher.Base rank)

abbrev CompilationSection := (point : EventTotal source) →
  GeneratedU7ObstructionEvolutionAt source point.2.2.2

def assemble (compiled : CompilationSection source) : U7ObstructionEvolutionCalculus N U7 where
  source := source
  compile := fun {support} {obstruction} {demand} event => compiled ⟨support, obstruction, demand, event⟩

/-- Material selects a real disposition for every legal event in every
demand fiber. The native receipt decoder then constructs the entire U7
compiler; no original compile function is an input. -/
def formSection (material : MotherArenaHigher.Material rank) : Option (CompilationSection source) :=
  (MotherArenaReceipts.NativeSection.form index member material).bind (fun disposition =>
    if ready : ∀ point, (formCompilation source point.2.2.2 (disposition point)).isSome then
      some (fun point => (formCompilation source point.2.2.2 (disposition point)).get (ready point))
    else none)

def formCalculus (material : MotherArenaHigher.Material rank) : Option (U7ObstructionEvolutionCalculus N U7) :=
  (formSection source index member material).map (assemble source)

theorem every_section (compiled : CompilationSection source) :
    ∃ material : MotherArenaHigher.Material rank,
      formSection source index member material = some compiled := by
  obtain ⟨material, selected⟩ := MotherArenaReceipts.NativeSection.every_section index member
    (fun point => (compiled point).disposition)
  have ready : ∀ point, (formCompilation source point.2.2.2 (compiled point).disposition).isSome := by
    intro point
    rw [formCompilation_recovers]
    rfl
  refine ⟨material, ?_⟩
  simp only [formSection, selected, Option.bind_some, dif_pos ready]
  apply congrArg some
  funext point
  exact Option.some.inj ((Option.some_get (ready point)).trans (formCompilation_recovers source point.2.2.2 (compiled point)))

theorem every_calculus_at_rank (calculus : U7ObstructionEvolutionCalculus N U7)
    (index : EventTotal calculus.source ↪ MotherArenaHigher.Base rank)
    (member : ∀ point, DispositionAt calculus.source point ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      formCalculus calculus.source index member material = some calculus := by
  obtain ⟨material, formed⟩ := every_section calculus.source index member
    (fun point => calculus.compile point.2.2.2)
  refine ⟨material, ?_⟩
  simp only [formCalculus, formed, Option.map_some]
  rfl

/-- All event and disposition operands are small even though the original
complete compiler output is in a higher structure universe. One rank pays
their whole dependent totals, with no representation premise exported. -/
theorem every_calculus (calculus : U7ObstructionEvolutionCalculus N U7) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ index : EventTotal calculus.source ↪ MotherArenaHigher.Base rank,
      ∃ member : ∀ point, DispositionAt calculus.source point ↪ MotherArenaHigher.Base rank,
        formCalculus calculus.source index member material = some calculus := by
  let total := EventTotal calculus.source ⊕ (Σ point, DispositionAt calculus.source point)
  let rank := MotherArenaHigher.carrierRank total
  let shared := MotherArenaHigher.carrierAddress total
  let index : EventTotal calculus.source ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let allDispositions : (Σ point, DispositionAt calculus.source point) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  let member := fun point => (Function.Embedding.sigmaMk point).trans allDispositions
  obtain ⟨material, formed⟩ := every_calculus_at_rank calculus index member
  exact ⟨rank, material, index, member, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7
