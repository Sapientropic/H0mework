import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Terminal

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (operations : Transitions source) (rows : LedgerWriteRowSourceAt source operations.exactTransitionAt)
    (terminal : LedgerTerminalRowSourceAt source) (point : Point source)

def PatchFor : (branch : EvolutionAt V point.1) → (target : TargetFor source branch) →
    LedgerFor source point.2 branch target → Type
  | .nativeWrite _, target, whole => {patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target.1⟩ // patch.toLedgerWriteEvolution = whole}
  | .relationWrite _, target, whole => {patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target.1⟩ // patch.toLedgerWriteEvolution = whole}
  | .continuedTransport _, target, whole => {patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target.1⟩ // patch.toLedgerWriteEvolution = whole}
  | .borromeanRedirect _, target, whole => {patch : FiniteGeneratedLedgerWritePatchAt rows point.2 ⟨target.1⟩ // patch.toLedgerWriteEvolution = whole}
  | .faithfulTerminal _, _, whole => {patch : SourceGeneratedLedgerTerminalPatchAt terminal point.2 // patch.toLedgerTerminalEvolution = whole}

def branchPatchEquiv (branch : EvolutionAt V point.1) (structural : source.toRootSource.actual.compile point.2 = branch)
    (body : Sigma (LedgerFor source point.2 branch)) :
    SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal
      (fromGraph source point.2 ⟨branch, ⟨(bodyEquiv source point.2 branch).symm body, structural⟩⟩) ≃
        PatchFor operations rows terminal point branch body.1 body.2 := by
  cases branch <;> exact Equiv.refl _

def bodyPatchEquiv (body : Sigma (LedgerFor source point.2 (source.toRootSource.actual.compile point.2))) :
    SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal
      ((compilationEquiv source point.2).symm ((bodyEquiv source point.2 _).symm body)) ≃
        PatchFor operations rows terminal point (source.toRootSource.actual.compile point.2) body.1 body.2 :=
  branchPatchEquiv operations rows terminal point _ rfl body

def bodyOfCompilation (compiled : SourceNativeLedgerEvolutionAt source point.2) :
    Sigma (LedgerFor source point.2 (source.toRootSource.actual.compile point.2)) :=
  bodyEquiv source point.2 _ (compilationEquiv source point.2 compiled)

def compilePatchEquiv (compiled : SourceNativeLedgerEvolutionAt source point.2) :
    SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal compiled ≃
      PatchFor operations rows terminal point (source.toRootSource.actual.compile point.2)
        (bodyOfCompilation point compiled).1 (bodyOfCompilation point compiled).2 :=
  (Equiv.cast (congrArg (SourceNativeFiniteLedgerPatchAt source operations.exactTransitionAt rows terminal)
    (((compilationEquiv source point.2).trans (bodyEquiv source point.2 _)).symm_apply_apply compiled).symm)).trans
      (bodyPatchEquiv operations rows terminal point (bodyOfCompilation point compiled))

def castBodyPatch {left right : EvolutionAt V point.1} (same : left = right)
    (body : Sigma (LedgerFor source point.2 left)) (patch : PatchFor operations rows terminal point left body.1 body.2) :
    PatchFor operations rows terminal point right
      ((Equiv.cast (congrArg (fun branch => Sigma (LedgerFor source point.2 branch)) same)) body).1
      ((Equiv.cast (congrArg (fun branch => Sigma (LedgerFor source point.2 branch)) same)) body).2 := by
  cases same
  exact patch

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
