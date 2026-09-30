import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.Context
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Transitions

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

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) (incidence : N.Incidence ↪ MotherArenaHigher.Base rank)

abbrev IncidenceMember (material : M) (context : IncidenceContext source) :=
  {value : B // r2 material 0 (incidenceContextEmbedding coordinates incidence context) value}

abbrev ExactMember (material : M) (context : WriteContext source) :=
  {value : B // r2 material 1 (writeContextEmbedding coordinates ledger context) value}

structure TransitionCheck (material : M) : Prop where
  project : ∀ (context : WriteContext source) (value : ExactMember coordinates ledger material context),
    ∃! output : IncidenceMember coordinates incidence material (incidenceContext context),
      r3 material 2 (writeContextEmbedding coordinates ledger context) value.val output.val
  lineage : ∀ (context : WriteContext source), ExactMember coordinates ledger material context →
    N.lineageAt context.2.1.1 = N.lineageAt context.2.2.1

def transitions (material : M) (checked : TransitionCheck coordinates ledger incidence material) : Transitions source where
  Incidence := IncidenceMember coordinates incidence material
  Exact := ExactMember coordinates ledger material
  project := fun context value => Classical.choose (checked.project context value)
  lineage := checked.lineage

def formTransitionParts (parent material : M) :
    Option (Σ value : MotherArenaCompiler.SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 × Transitions value.2.2) :=
  (MotherArenaPrograms.formTerminalSource parent).pbind (fun ⟨value, compiled, rows⟩ formed =>
    let base := ((MotherArenaHigher.split rank) parent).1
    let compiledFormed := terminal_compilation_formed parent value compiled rows formed
    let coordinates := MotherArenaPrograms.coordinatesOfCompilation base value compiled compiledFormed
    let ledger := MotherArenaPrograms.ledgerCoordinatesOfCompilation base value compiled compiledFormed
    let incidence := incidenceCoordinatesOfFormation (MotherArenaPrograms.sourceMaterial base) value
      (MotherArenaPrograms.compilation_source_formed base value compiled compiledFormed)
    if checked : TransitionCheck coordinates ledger incidence material then
      some ⟨value, compiled, rows, transitions coordinates ledger incidence material checked⟩
    else none)

/-- Both complete member families and the actual dependent operation are
formed from one material; the parent includes the complete compiler values. -/
def formTransitions (material : M) :
    Option (Σ value : MotherArenaCompiler.SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 × Transitions value.2.2) :=
  let parts := (MotherArenaHigher.split rank) material
  formTransitionParts parts.1 parts.2

theorem transitions_formed (parent material : M) (value : MotherArenaCompiler.SourceValue)
    (compiled : CompilationSection value.2.2) (rows : LedgerTerminalRowSourceAt value.2.2)
    (formed : MotherArenaPrograms.formTerminalSource parent = some ⟨value, compiled, rows⟩)
    (checked : TransitionCheck
      (MotherArenaPrograms.coordinatesOfCompilation ((MotherArenaHigher.split rank) parent).1 value compiled
        (terminal_compilation_formed parent value compiled rows formed))
      (MotherArenaPrograms.ledgerCoordinatesOfCompilation ((MotherArenaHigher.split rank) parent).1 value compiled
        (terminal_compilation_formed parent value compiled rows formed))
      (incidenceCoordinatesOfFormation (MotherArenaPrograms.sourceMaterial ((MotherArenaHigher.split rank) parent).1) value
        (MotherArenaPrograms.compilation_source_formed ((MotherArenaHigher.split rank) parent).1 value compiled
          (terminal_compilation_formed parent value compiled rows formed))) material) :
    formTransitions ((MotherArenaHigher.pack rank) (parent, material)) = some ⟨value, compiled, rows,
      transitions _ _ _ material checked⟩ := by
  unfold formTransitions
  rw [MotherArenaHigher.split_pack]
  dsimp only
  unfold formTransitionParts
  apply Option.pbind_eq_some_iff.mpr
  exact ⟨⟨value, compiled, rows⟩, formed, dif_pos checked⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
