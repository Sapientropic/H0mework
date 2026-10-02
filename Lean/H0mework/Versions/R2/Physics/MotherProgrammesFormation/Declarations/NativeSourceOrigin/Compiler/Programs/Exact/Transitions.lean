import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Context

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

structure Transitions {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) where
  Incidence : IncidenceContext source → Type
  Exact : WriteContext source → Type
  project : ∀ context, Exact context → Incidence (incidenceContext context)
  lineage : ∀ context, Exact context → N.lineageAt context.2.1.1 = N.lineageAt context.2.2.1

def Transitions.ofCompiler {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) : Transitions source where
  Incidence := fun context => compiler.IncidenceTransitionAt context.1.2 context.2.1 context.2.2
  Exact := fun context => compiler.ExactTransitionAt context.2.1 context.2.2.2.1 context.2.2.2.2
  project := fun _ => compiler.exact_incidence
  lineage := fun _ => compiler.exact_lineage

def Transitions.incidenceTransitionAt {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (transitions : Transitions source) {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    (left right : N.Incidence) : Type := transitions.Incidence (⟨current, event⟩, left, right)

def Transitions.exactTransitionAt {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (transitions : Transitions source) {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    {target : N.Support} (a : OpenResponsibilityAt N event.1) (b : OpenResponsibilityAt N target) : Type :=
  transitions.Exact ⟨current, event, target, a, b⟩

def Transitions.exact_incidence {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (transitions : Transitions source) {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : N.Support} {a : OpenResponsibilityAt N event.1} {b : OpenResponsibilityAt N target}
    (value : transitions.exactTransitionAt event a b) :
    transitions.incidenceTransitionAt event (N.incidenceAt event.1) (N.incidenceAt target) :=
  transitions.project ⟨current, event, target, a, b⟩ value

theorem Transitions.exact_lineage {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (transitions : Transitions source) {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {target : N.Support} {a : OpenResponsibilityAt N event.1} {b : OpenResponsibilityAt N target}
    (value : transitions.exactTransitionAt event a b) : N.lineageAt event.1 = N.lineageAt target :=
  transitions.lineage ⟨current, event, target, a, b⟩ value

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledger : LedgerCoordinates N) (incidence : N.Incidence ↪ B)

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
    Option (Σ value : SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 × Transitions value.2.2) :=
  (formTerminalSource parent).pbind (fun ⟨value, compiled, rows⟩ formed =>
    let base := (MotherHigherLawValue.split parent).1
    let compiledFormed := terminal_compilation_formed parent value compiled rows formed
    let coordinates := coordinatesOfCompilation base value compiled compiledFormed
    let ledger := ledgerCoordinatesOfCompilation base value compiled compiledFormed
    let incidence := incidenceCoordinatesOfFormation (sourceMaterial base) value
      (compilation_source_formed base value compiled compiledFormed)
    if checked : TransitionCheck coordinates ledger incidence material then
      some ⟨value, compiled, rows, transitions coordinates ledger incidence material checked⟩
    else none)

/-- Both complete member families and the actual dependent operation are
formed from one material; the parent includes the complete compiler values. -/
def formTransitions (material : M) :
    Option (Σ value : SourceValue,
      CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 × Transitions value.2.2) :=
  let parts := MotherHigherLawValue.split material
  formTransitionParts parts.1 parts.2

theorem transitions_formed (parent material : M) (value : SourceValue)
    (compiled : CompilationSection value.2.2) (rows : LedgerTerminalRowSourceAt value.2.2)
    (formed : formTerminalSource parent = some ⟨value, compiled, rows⟩)
    (checked : TransitionCheck
      (coordinatesOfCompilation (MotherHigherLawValue.split parent).1 value compiled
        (terminal_compilation_formed parent value compiled rows formed))
      (ledgerCoordinatesOfCompilation (MotherHigherLawValue.split parent).1 value compiled
        (terminal_compilation_formed parent value compiled rows formed))
      (incidenceCoordinatesOfFormation (sourceMaterial (MotherHigherLawValue.split parent).1) value
        (compilation_source_formed (MotherHigherLawValue.split parent).1 value compiled
          (terminal_compilation_formed parent value compiled rows formed))) material) :
    formTransitions (MotherHigherLawValue.pack (parent, material)) = some ⟨value, compiled, rows,
      transitions _ _ _ material checked⟩ := by
  unfold formTransitions
  rw [MotherHigherLawValue.split_pack]
  dsimp only
  unfold formTransitionParts
  apply Option.pbind_eq_some_iff.mpr
  exact ⟨⟨value, compiled, rows⟩, formed, dif_pos checked⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
