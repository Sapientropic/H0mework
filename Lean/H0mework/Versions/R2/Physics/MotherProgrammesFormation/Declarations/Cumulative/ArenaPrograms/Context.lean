import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.WholeConsumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Context

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherArenaCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def sourceMaterial (material : M) : M :=
  ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1

/-- Read the actual source origin from the full compilation factory output;
no separate header is supplied by the caller. -/
theorem compilation_source_formed (material : M) (value : MotherArenaCompiler.SourceValue) (compiled : CompilationSection value.2.2)
    (formed : MotherArenaCompiler.formCompilation material = some ⟨value, compiled⟩) :
    MotherArenaSource.formSource (sourceMaterial material) = some value := by
  unfold MotherArenaCompiler.formCompilation at formed
  obtain ⟨⟨source, targets, ledgers⟩, wholeFormed, same⟩ := Option.map_eq_some_iff.mp formed
  have sourceEq := congrArg Sigma.fst same
  unfold MotherArenaCompiler.formWhole MotherArenaCompiler.formWholeParts at wholeFormed
  dsimp only at wholeFormed
  obtain ⟨⟨base, coordinates, targets'⟩, targetFormed, selected⟩ := Option.pbind_eq_some_iff.mp wholeFormed
  dsimp only at selected
  split at selected
  · have baseEq := congrArg Sigma.fst (Option.some.inj selected)
    exact (MotherArenaCompiler.target_source_formed ((MotherArenaHigher.split rank) material).1 base coordinates targets' targetFormed).trans
      (congrArg some (baseEq.trans sourceEq))
  · cases selected

def coordinatesOfCompilation (material : M) (value : MotherArenaCompiler.SourceValue) (compiled : CompilationSection value.2.2)
    (formed : MotherArenaCompiler.formCompilation material = some ⟨value, compiled⟩) : MotherArenaCompiler.Coordinates (rank := rank) value.2.2 :=
  MotherArenaCompiler.coordinatesOfFormation (sourceMaterial material) value (compilation_source_formed material value compiled formed)

def ledgerCoordinatesOfCompilation (material : M) (value : MotherArenaCompiler.SourceValue) (compiled : CompilationSection value.2.2)
    (formed : MotherArenaCompiler.formCompilation material = some ⟨value, compiled⟩) : MotherArenaCompiler.LedgerCoordinates (rank := rank) value.1 :=
  MotherArenaCompiler.ledgerCoordinatesOfFormation (sourceMaterial material) value (compilation_source_formed material value compiled formed)

def rowContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (ledgerCoordinates : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) : RowContext source ↪ B where
  toFun := fun ⟨point, entry⟩ => (MotherArenaHigher.pair rank) (coordinates.occurrence point, ledgerCoordinates.entry point.2.1 entry)
  inj' := by
    rintro ⟨point, entry⟩ ⟨other, otherEntry⟩ same
    have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
    have pointEq := coordinates.occurrence.injective (congrArg Prod.fst pairEq)
    cases pointEq
    have entryEq := (ledgerCoordinates.entry point.2.1).injective (congrArg Prod.snd pairEq)
    cases entryEq
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
