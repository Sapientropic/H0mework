import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalFormation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (operations : Transitions source) (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (terminal : LedgerTerminalRowSourceAt source)

def checkedWritePatch {point : Point source} (target : CompleteLiveLedgerAt N)
    (request : Option (FiniteGeneratedLedgerWritePatchAt rows point.2 target))
    (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ target) :
    Option { patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target // patch.toLedgerWriteEvolution = whole } :=
  request.bind (fun patch => if same : patch.toLedgerWriteEvolution = whole then some ⟨patch, same⟩ else none)

def checkedTerminalPatch {point : Point source}
    (request : Option (SourceGeneratedLedgerTerminalPatchAt terminal point.2))
    (whole : LedgerTerminalEvolutionAt N ⟨point.2.1⟩) :
    Option { patch : SourceGeneratedLedgerTerminalPatchAt terminal point.2 // patch.toLedgerTerminalEvolution = whole } :=
  request.bind (fun patch => if same : patch.toLedgerTerminalEvolution = whole then some ⟨patch, same⟩ else none)

/-- The fold equality is checked against the actual already formed full
compilation value, retaining the original patch subtype in every branch. -/
def parsePatchAt (point : Point source)
    (writes : (target : N.Support) → Option (FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target⟩))
    (ends : Option (SourceGeneratedLedgerTerminalPatchAt terminal point.2))
    (compiled : SourceNativeLedgerEvolutionAt source point.2) :
    Option (SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled) :=
  match compiled with
  | .nativeWrite _ _ target whole => checkedWritePatch operations rows ⟨target.1⟩ (writes target.1) whole
  | .relationWrite _ _ target whole => checkedWritePatch operations rows ⟨target.1⟩ (writes target.1) whole
  | .continuedTransport _ _ target whole => checkedWritePatch operations rows ⟨target.1⟩ (writes target.1) whole
  | .borromeanRedirect _ _ target whole => checkedWritePatch operations rows ⟨target.1⟩ (writes target.1) whole
  | .faithfulTerminal _ _ whole => checkedTerminalPatch terminal ends whole

def allProgramme (value : AllRequestValue) : WriteProgramValue := requestProgramme value.1

abbrev PatchSection (value : WriteProgramValue) :=
  (point : Point value.1.2.2) → SourceNativeFiniteLedgerPatchAt value.1.2.2 value.2.2.2.1.exactTransitionAt
    value.2.2.2.2 value.2.2.1 (value.2.1 point)

def parsePatchSection (value : AllRequestValue) (point : Point (allProgramme value).1.2.2) :
    Option (SourceNativeFiniteLedgerPatchAt (allProgramme value).1.2.2 (allProgramme value).2.2.2.1.exactTransitionAt
      (allProgramme value).2.2.2.2 (allProgramme value).2.2.1 ((allProgramme value).2.1 point)) :=
  parsePatchAt (allProgramme value).2.2.2.1 (allProgramme value).2.2.2.2 (allProgramme value).2.2.1 point
    (fun target => value.1.2 (point, target)) (value.2 point) ((allProgramme value).2.1 point)

def CompilerCheck (value : AllRequestValue) : Prop := ∀ point, (parsePatchSection value point).isSome = true

def generatedCompiler (value : AllRequestValue) (checked : CompilerCheck value) : SourceNativeLedgerCompiler (allProgramme value).1.2.2 where
  IncidenceTransitionAt := (allProgramme value).2.2.2.1.incidenceTransitionAt
  ExactTransitionAt := (allProgramme value).2.2.2.1.exactTransitionAt
  exact_incidence := (allProgramme value).2.2.2.1.exact_incidence
  exact_lineage := (allProgramme value).2.2.2.1.exact_lineage
  writeRowSource := (allProgramme value).2.2.2.2
  terminalRowSource := (allProgramme value).2.2.1
  compile := fun {current} event => (allProgramme value).2.1 ⟨current, event⟩
  compilePatch := fun {current} event => (parsePatchSection value ⟨current, event⟩).get (checked ⟨current, event⟩)

abbrev CompilerValue := Σ value : WriteProgramValue, SourceNativeLedgerCompiler value.1.2.2

def formCompiler (material : M) : Option CompilerValue :=
  (formAllRequests material).bind (fun value =>
    if checked : CompilerCheck value then some ⟨allProgramme value, generatedCompiler value checked⟩ else none)

def formLedgerSource (material : M) : Option (Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeLedgerSource N V) :=
  (formCompiler material).map (fun ⟨value, compiler⟩ => ⟨value.1.1, value.1.2.1, ⟨value.1.2.2, compiler⟩⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
