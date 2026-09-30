import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Compiler

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

def requestWrite (point : Point source) (target : N.Support)
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target⟩) (asked : N.Support) :
    Option (FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨asked⟩) :=
  if same : target = asked then some (Eq.mp (congrArg (fun support => FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨support⟩) same) patch)
  else none

theorem requestWrite_self (point : Point source) (target : N.Support)
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target⟩) : requestWrite operations rows point target patch target = some patch := by
  unfold requestWrite
  rw [dif_pos rfl]
  rfl

def originalWriteRequest (point : Point source) (compiled : SourceNativeLedgerEvolutionAt source point.2)
    (patch : SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled) :
    (target : N.Support) → Option (FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target⟩) :=
  match compiled with
  | .nativeWrite _ _ target _ => requestWrite operations rows point target.1 patch.1
  | .relationWrite _ _ target _ => requestWrite operations rows point target.1 patch.1
  | .continuedTransport _ _ target _ => requestWrite operations rows point target.1 patch.1
  | .borromeanRedirect _ _ target _ => requestWrite operations rows point target.1 patch.1
  | .faithfulTerminal .. => fun _ => none

def originalTerminalRequest (point : Point source) (compiled : SourceNativeLedgerEvolutionAt source point.2)
    (patch : SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled) :
    Option (SourceGeneratedLedgerTerminalPatchAt terminal point.2) :=
  match compiled with
  | .nativeWrite .. | .relationWrite .. | .continuedTransport .. | .borromeanRedirect .. => none
  | .faithfulTerminal .. => some patch.1

theorem checkedWrite_original {point : Point source} (target : CompleteLiveLedgerAt N)
    (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ target)
    (patch : { patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target // patch.toLedgerWriteEvolution = whole }) :
    checkedWritePatch operations rows target (some patch.1) whole = some patch := by
  unfold checkedWritePatch
  rw [Option.bind_some, dif_pos patch.2]

theorem checkedTerminal_original {point : Point source} (whole : LedgerTerminalEvolutionAt N ⟨point.2.1⟩)
    (patch : { patch : SourceGeneratedLedgerTerminalPatchAt terminal point.2 // patch.toLedgerTerminalEvolution = whole }) :
    checkedTerminalPatch terminal (some patch.1) whole = some patch := by
  unfold checkedTerminalPatch
  rw [Option.bind_some, dif_pos patch.2]

theorem parse_original (point : Point source) (compiled : SourceNativeLedgerEvolutionAt source point.2)
    (patch : SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled) :
    parsePatchAt operations rows terminal point
      (originalWriteRequest operations rows terminal point compiled patch)
      (originalTerminalRequest operations rows terminal point compiled patch) compiled = some patch := by
  cases compiled with
  | nativeWrite write structural target whole =>
      exact (congrArg (fun request => checkedWritePatch operations rows (point := point) ⟨target.1⟩ request whole)
        (requestWrite_self operations rows point target.1 patch.1)).trans
          (checkedWrite_original operations rows (point := point) ⟨target.1⟩ whole patch)
  | relationWrite write structural target whole =>
      exact (congrArg (fun request => checkedWritePatch operations rows (point := point) ⟨target.1⟩ request whole)
        (requestWrite_self operations rows point target.1 patch.1)).trans
          (checkedWrite_original operations rows (point := point) ⟨target.1⟩ whole patch)
  | continuedTransport write structural target whole =>
      exact (congrArg (fun request => checkedWritePatch operations rows (point := point) ⟨target.1⟩ request whole)
        (requestWrite_self operations rows point target.1 patch.1)).trans
          (checkedWrite_original operations rows (point := point) ⟨target.1⟩ whole patch)
  | borromeanRedirect write structural target whole =>
      exact (congrArg (fun request => checkedWritePatch operations rows (point := point) ⟨target.1⟩ request whole)
        (requestWrite_self operations rows point target.1 patch.1)).trans
          (checkedWrite_original operations rows (point := point) ⟨target.1⟩ whole patch)
  | faithfulTerminal stop structural whole =>
      exact checkedTerminal_original terminal whole patch

def compilerOfPatches (value : WriteProgramValue) (patches : PatchSection value) : SourceNativeLedgerCompiler value.1.2.2 where
  IncidenceTransitionAt := value.2.2.2.1.incidenceTransitionAt
  ExactTransitionAt := value.2.2.2.1.exactTransitionAt
  exact_incidence := value.2.2.2.1.exact_incidence
  exact_lineage := value.2.2.2.1.exact_lineage
  writeRowSource := value.2.2.2.2
  terminalRowSource := value.2.2.1
  compile := fun {current} event => value.2.1 ⟨current, event⟩
  compilePatch := fun {current} event => patches ⟨current, event⟩

theorem every_compiler_patch_section (parent : M) (value : WriteProgramValue)
    (formed : formWritePrograms parent = some value) (patches : PatchSection value) :
    ∃ material : M, formCompiler material = some ⟨value, compilerOfPatches value patches⟩ := by
  let writes : OriginalPatchRequests value := fun context =>
    originalWriteRequest value.2.2.2.1 value.2.2.2.2 value.2.2.1 context.1 (value.2.1 context.1) (patches context.1) context.2
  let ends : TerminalRequests value := fun point =>
    originalTerminalRequest value.2.2.2.1 value.2.2.2.2 value.2.2.1 point (value.2.1 point) (patches point)
  obtain ⟨material, inventories, selections, requestsFormed⟩ := every_complete_patch_requests parent value formed writes ends
  let bundle : AllRequestValue := ⟨⟨⟨⟨value, inventories⟩, selections⟩, writes⟩, ends⟩
  have parsed : ∀ point, parsePatchSection bundle point = some (patches point) :=
    fun point => parse_original value.2.2.2.1 value.2.2.2.2 value.2.2.1 point (value.2.1 point) (patches point)
  have checked : CompilerCheck bundle := fun point => by rw [parsed]; rfl
  have patchEq : (fun point => (parsePatchSection bundle point).get (checked point)) = patches := by
    funext point
    exact Option.some.inj ((Option.some_get _).trans (parsed point))
  have compilerEq : generatedCompiler bundle checked = compilerOfPatches value patches :=
    congrArg (compilerOfPatches value) patchEq
  refine ⟨material, ?_⟩
  unfold formCompiler
  rw [requestsFormed, Option.bind_some, dif_pos checked]
  exact congrArg (fun compiler => some (⟨value, compiler⟩ : CompilerValue)) compilerEq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPatchInventory
