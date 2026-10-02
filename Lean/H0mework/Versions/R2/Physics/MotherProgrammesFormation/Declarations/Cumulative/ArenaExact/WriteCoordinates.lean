import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteCoordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem transitions_terminal_formed (material : M) (value : MotherArenaCompiler.SourceValue) (compiled : CompilationSection value.2.2)
    (rows : LedgerTerminalRowSourceAt value.2.2) (operations : Transitions value.2.2)
    (formed : formTransitions material = some ⟨value, compiled, rows, operations⟩) :
    MotherArenaPrograms.formTerminalSource ((MotherArenaHigher.split rank) material).1 = some ⟨value, compiled, rows⟩ := by
  unfold formTransitions formTransitionParts at formed
  dsimp only at formed
  obtain ⟨⟨base, output, terminals⟩, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  dsimp only at selected
  split at selected
  · have same := congrArg (fun result : TransitionValue =>
      (⟨result.1, result.2.1, result.2.2.1⟩ : Σ value : MotherArenaCompiler.SourceValue,
        CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2)) (Option.some.inj selected)
    exact baseFormed.trans (congrArg some same)
  · cases selected

def exactCoordinatesOfTransitions (material : M) (value : TransitionValue)
    (formed : formTransitions material = some value) :
    ∀ context, value.2.2.2.Exact context ↪ B := by
  have origin := transitions_terminal_formed material value.1 value.2.1 value.2.2.1 value.2.2.2 formed
  unfold formTransitions formTransitionParts at formed
  dsimp only at formed
  simp only [origin, Option.pbind_some] at formed
  split at formed
  · have same := Option.some.inj formed
    exact Eq.mp (congrArg (fun result : TransitionValue => ∀ context, result.2.2.2.Exact context ↪ B) same)
      (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
  · cases formed

def remainderContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) : RemainderContext source ↪ B where
  toFun := fun context => (MotherArenaHigher.pair rank) (coordinates.occurrence context.1, ledger.support context.2)
  inj' := by
    intro left right same
    have same := (MotherArenaHigher.pairEquiv rank).injective same
    exact Prod.ext (coordinates.occurrence.injective (congrArg Prod.fst same))
      (ledger.support.injective (congrArg Prod.snd same))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
