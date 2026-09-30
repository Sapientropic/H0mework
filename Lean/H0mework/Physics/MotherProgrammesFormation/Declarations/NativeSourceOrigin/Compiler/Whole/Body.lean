import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.TargetCoverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def LedgerFor {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current) :
    (branch : EvolutionAt V current) → TargetFor source branch → Type
  | .nativeWrite _, target => LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .relationWrite _, target => LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .continuedTransport _, target => LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .borromeanRedirect _, target => LedgerWriteEvolutionAt N ⟨event.1⟩ ⟨target.1⟩
  | .faithfulTerminal _, _ => LedgerTerminalEvolutionAt N ⟨event.1⟩

/-- The already formed target leaves exactly the original whole ledger as
dependent material. Both full directions and all terminal rows remain data. -/
def bodyEquiv {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V)
    {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current) (branch : EvolutionAt V current) :
    BranchData source event branch ≃ Σ target : TargetFor source branch, LedgerFor source event branch target := by
  cases branch
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact {
      toFun := fun whole => ⟨.unit, whole⟩
      invFun := Sigma.snd
      left_inv := fun _ => rfl
      right_inv := fun ⟨.unit, _⟩ => rfl }

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
