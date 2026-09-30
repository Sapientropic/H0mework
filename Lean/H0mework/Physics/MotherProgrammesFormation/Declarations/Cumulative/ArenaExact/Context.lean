import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPrograms.TerminalConsumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Context

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

def incidenceCoordinatesOfFormation (material : M) (value : MotherArenaCompiler.SourceValue)
    (formed : MotherArenaSource.formSource material = some value) : value.1.Incidence ↪ B := by
  unfold MotherArenaSource.formSource MotherArenaSource.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · have same := Option.some.inj formed
            exact Eq.mp (congrArg (fun source : MotherArenaCompiler.SourceValue => source.1.Incidence ↪ B) same)
              (show (MotherArenaSource.network _ hn).Incidence ↪ B from
                ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

theorem terminal_compilation_formed (material : M) (value : MotherArenaCompiler.SourceValue)
    (compiled : CompilationSection value.2.2) (rows : LedgerTerminalRowSourceAt value.2.2)
    (formed : MotherArenaPrograms.formTerminalSource material = some ⟨value, compiled, rows⟩) :
    MotherArenaCompiler.formCompilation ((MotherArenaHigher.split rank) material).1 = some ⟨value, compiled⟩ := by
  unfold MotherArenaPrograms.formTerminalSource at formed
  dsimp only at formed
  obtain ⟨⟨base, output⟩, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  dsimp only at selected
  split at selected
  · have same := congrArg (fun result : Σ value : MotherArenaCompiler.SourceValue,
        CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 =>
      (⟨result.1, result.2.1⟩ : Σ value : MotherArenaCompiler.SourceValue, CompilationSection value.2.2)) (Option.some.inj selected)
    exact baseFormed.trans (congrArg some same)
  · cases selected

def incidenceContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (incidence : N.Incidence ↪ B) : IncidenceContext source ↪ B where
  toFun := fun context => (MotherArenaHigher.pair rank) (coordinates.occurrence context.1,
    (MotherArenaHigher.pair rank) (incidence context.2.1, incidence context.2.2))
  inj' := by
    intro left right same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have pointEq := coordinates.occurrence.injective (congrArg Prod.fst pairEq)
    have incidenceEq := (MotherArenaHigher.pairEquiv rank).injective (congrArg Prod.snd pairEq)
    exact Prod.ext pointEq (Prod.ext (incidence.injective (congrArg Prod.fst incidenceEq))
      (incidence.injective (congrArg Prod.snd incidenceEq)))

def writeContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledger : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) : WriteContext source ↪ B where
  toFun := fun context => (MotherArenaHigher.pair rank)
    (MotherArenaPrograms.rowContextEmbedding coordinates ledger ⟨⟨context.1, context.2.1⟩, context.2.2.2.1⟩,
      (MotherArenaHigher.pair rank) (ledger.support context.2.2.1, ledger.entry context.2.2.1 context.2.2.2.2))
  inj' := by
    rintro ⟨c, event, target, a, b⟩ ⟨d, other, target', a', b'⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have rowEq := (MotherArenaPrograms.rowContextEmbedding coordinates ledger).injective (congrArg Prod.fst pairEq)
    have pointEq := congrArg Sigma.fst rowEq
    cases pointEq
    have entryEq : a = a' := eq_of_heq (Sigma.mk.inj rowEq).2
    cases entryEq
    have targetEq := (MotherArenaHigher.pairEquiv rank).injective (congrArg Prod.snd pairEq)
    have supportEq := ledger.support.injective (congrArg Prod.fst targetEq)
    cases supportEq
    have entryEq := (ledger.entry target).injective (congrArg Prod.snd targetEq)
    cases entryEq
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
