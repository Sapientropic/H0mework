import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.Transitions
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Coverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure TransitionEncoding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (old : Transitions source) where
  incidence : Sigma old.Incidence ↪ B
  exact : Sigma old.Exact ↪ B

namespace TransitionEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (incidence : N.Incidence ↪ MotherArenaHigher.Base rank)
    (old : Transitions source) (encode : TransitionEncoding (rank := rank) old)

def graph (tag : Nat) (code : B) : Prop :=
  let pair := (MotherArenaHigher.unpair rank) code
  let tail := (MotherArenaHigher.unpair rank) pair.2
  match tag with
  | 0 => ∃ context value, incidenceContextEmbedding coordinates incidence context = pair.1 ∧
      encode.incidence ⟨context, value⟩ = pair.2
  | 1 => ∃ context value, writeContextEmbedding coordinates ledger context = pair.1 ∧
      encode.exact ⟨context, value⟩ = pair.2
  | 2 => ∃ context value, writeContextEmbedding coordinates ledger context = pair.1 ∧
      encode.exact ⟨context, value⟩ = tail.1 ∧
      encode.incidence ⟨incidenceContext context, old.project context value⟩ = tail.2
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph coordinates ledger incidence old encode tag code then 0 else 1

theorem reader_bit {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode)
    (tag : Nat) (code : B) : bit material tag code ↔ graph coordinates ledger incidence old encode tag code := by
  by_cases seen : graph coordinates ledger incidence old encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def incidenceEquiv {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode)
    (context : IncidenceContext source) : old.Incidence context ≃ IncidenceMember coordinates incidence material context :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk context).trans encode.incidence)
    (fun address => r2 material 0 (incidenceContextEmbedding coordinates incidence context) address) (by
      intro address
      rw [r2, reader_bit coordinates ledger incidence old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, value, same, valueEq⟩
        have same := (incidenceContextEmbedding coordinates incidence).injective same
        cases same
        exact ⟨value, valueEq⟩
      · rintro ⟨value, valueEq⟩
        exact ⟨context, value, rfl, valueEq⟩)

def exactEquiv {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode)
    (context : WriteContext source) : old.Exact context ≃ ExactMember coordinates ledger material context :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk context).trans encode.exact)
    (fun address => r2 material 1 (writeContextEmbedding coordinates ledger context) address) (by
      intro address
      rw [r2, reader_bit coordinates ledger incidence old encode hm]
      simp only [graph, MotherArenaHigher.unpair_pair]
      constructor
      · rintro ⟨other, value, same, valueEq⟩
        have same := (writeContextEmbedding coordinates ledger).injective same
        cases same
        exact ⟨value, valueEq⟩
      · rintro ⟨value, valueEq⟩
        exact ⟨context, value, rfl, valueEq⟩)

theorem project_graph {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode)
    (context : WriteContext source) (value : old.Exact context) (output : old.Incidence (incidenceContext context)) :
    r3 material 2 (writeContextEmbedding coordinates ledger context)
      (exactEquiv coordinates ledger incidence old encode hm context value).val
      (incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context) output).val ↔
        output = old.project context value := by
  rw [r3, reader_bit coordinates ledger incidence old encode hm]
  simp only [graph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, event, contextEq, eventEq, outputEq⟩
    have same := (writeContextEmbedding coordinates ledger).injective contextEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := old.Exact) context).trans encode.exact).injective eventEq
    cases same
    exact (((Function.Embedding.sigmaMk (β := old.Incidence) (incidenceContext context)).trans encode.incidence).injective outputEq).symm
  · intro same
    cases same
    exact ⟨context, value, rfl, rfl, rfl⟩

theorem checked {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode) :
    TransitionCheck coordinates ledger incidence material where
  project := by
    intro context value
    obtain ⟨value, rfl⟩ := (exactEquiv coordinates ledger incidence old encode hm context).surjective value
    refine ⟨incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context) (old.project context value),
      (project_graph coordinates ledger incidence old encode hm context value _).mpr rfl, ?_⟩
    intro output selected
    obtain ⟨output, rfl⟩ := (incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context)).surjective output
    exact congrArg (incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context))
      ((project_graph coordinates ledger incidence old encode hm context value output).mp selected)
  lineage := by
    intro context value
    exact old.lineage context ((exactEquiv coordinates ledger incidence old encode hm context).symm value)

def presentation {material : MotherArenaHigher.Material rank}
    (hm : (MotherArenaHigher.read rank) material = reader coordinates ledger incidence old encode) :
    TransitionPresentation old (transitions coordinates ledger incidence material (checked coordinates ledger incidence old encode hm)) where
  incidence := incidenceEquiv coordinates ledger incidence old encode hm
  exact := exactEquiv coordinates ledger incidence old encode hm
  project := by
    intro context value
    let produced := Classical.choose ((checked coordinates ledger incidence old encode hm).project context
      (exactEquiv coordinates ledger incidence old encode hm context value))
    have selected := (Classical.choose_spec ((checked coordinates ledger incidence old encode hm).project context
      (exactEquiv coordinates ledger incidence old encode hm context value))).1
    obtain ⟨output, outputEq⟩ := (incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context)).surjective produced
    change r3 material 2 _ _ produced.val at selected
    rw [← outputEq] at selected
    exact outputEq.symm.trans (congrArg (incidenceEquiv coordinates ledger incidence old encode hm (incidenceContext context))
      ((project_graph coordinates ledger incidence old encode hm context value output).mp selected))

end TransitionEncoding

def TransitionEncoding.ofTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {old : Transitions source} (encode : TransitionTotal old ↪ B) : TransitionEncoding (rank := rank) old where
  incidence := ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  exact := ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩

theorem every_transition_program (parent : M) (value : MotherArenaCompiler.SourceValue)
    (compiled : CompilationSection value.2.2) (rows : LedgerTerminalRowSourceAt value.2.2)
    (formed : MotherArenaPrograms.formTerminalSource parent = some ⟨value, compiled, rows⟩) (old : Transitions value.2.2)
    (encode : TransitionTotal old ↪ B) :
    ∃ material : M, ∃ generated : Transitions value.2.2,
      formTransitions material = some ⟨value, compiled, rows, generated⟩ ∧ Nonempty (TransitionPresentation old generated) := by
  let base := ((MotherArenaHigher.split rank) parent).1
  let compiledFormed := terminal_compilation_formed parent value compiled rows formed
  let coordinates := MotherArenaPrograms.coordinatesOfCompilation base value compiled compiledFormed
  let ledger := MotherArenaPrograms.ledgerCoordinatesOfCompilation base value compiled compiledFormed
  let incidence := incidenceCoordinatesOfFormation (MotherArenaPrograms.sourceMaterial base) value
    (MotherArenaPrograms.compilation_source_formed base value compiled compiledFormed)
  let code := TransitionEncoding.ofTotal encode
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (TransitionEncoding.reader coordinates ledger incidence old code)
  let checked := TransitionEncoding.checked coordinates ledger incidence old code hm
  exact ⟨(MotherArenaHigher.pack rank) (parent, material), transitions coordinates ledger incidence material checked,
    transitions_formed parent material value compiled rows formed checked,
    ⟨TransitionEncoding.presentation coordinates ledger incidence old code hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
