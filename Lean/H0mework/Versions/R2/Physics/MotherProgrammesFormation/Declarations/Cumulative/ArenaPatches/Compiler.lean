import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalFormation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.Compiler

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def formCompiler (material : M) : Option CompilerValue :=
  (formAllRequests material).bind (fun value =>
    if checked : CompilerCheck value then some ⟨allProgramme value, generatedCompiler value checked⟩ else none)

def formLedgerSource (material : M) : Option (Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeLedgerSource N V) :=
  (formCompiler material).map (fun ⟨value, compiler⟩ => ⟨value.1.1, value.1.2.1, ⟨value.1.2.2, compiler⟩⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
