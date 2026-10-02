import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def sourceMaterial (material : M) : M :=
  (MotherHigherLawValue.split (MotherHigherLawValue.split material).1).1

/-- Read the actual source origin from the full compilation factory output;
no separate header is supplied by the caller. -/
theorem compilation_source_formed (material : M) (value : SourceValue) (compiled : CompilationSection value.2.2)
    (formed : formCompilation material = some ⟨value, compiled⟩) :
    MotherNativeSourceOrigin.formSource (sourceMaterial material) = some value := by
  unfold formCompilation at formed
  obtain ⟨⟨source, targets, ledgers⟩, wholeFormed, same⟩ := Option.map_eq_some_iff.mp formed
  have sourceEq := congrArg Sigma.fst same
  unfold formWhole formWholeParts at wholeFormed
  dsimp only at wholeFormed
  obtain ⟨⟨base, coordinates, targets'⟩, targetFormed, selected⟩ := Option.pbind_eq_some_iff.mp wholeFormed
  dsimp only at selected
  split at selected
  · have baseEq := congrArg Sigma.fst (Option.some.inj selected)
    exact (target_source_formed (MotherHigherLawValue.split material).1 base coordinates targets' targetFormed).trans
      (congrArg some (baseEq.trans sourceEq))
  · cases selected

def coordinatesOfCompilation (material : M) (value : SourceValue) (compiled : CompilationSection value.2.2)
    (formed : formCompilation material = some ⟨value, compiled⟩) : Coordinates value.2.2 :=
  coordinatesOfFormation (sourceMaterial material) value (compilation_source_formed material value compiled formed)

def ledgerCoordinatesOfCompilation (material : M) (value : SourceValue) (compiled : CompilationSection value.2.2)
    (formed : formCompilation material = some ⟨value, compiled⟩) : LedgerCoordinates value.1 :=
  ledgerCoordinatesOfFormation (sourceMaterial material) value (compilation_source_formed material value compiled formed)

abbrev Point {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  Sigma source.toRootSource.actual.OccurrenceAt

abbrev RowContext {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  Σ point : Point source, OpenResponsibilityAt N point.2.1

def rowContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledgerCoordinates : LedgerCoordinates N) : RowContext source ↪ B where
  toFun := fun ⟨point, entry⟩ => MotherHigherLawFamily.pair (coordinates.occurrence point, ledgerCoordinates.entry point.2.1 entry)
  inj' := by
    rintro ⟨point, entry⟩ ⟨other, otherEntry⟩ same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have pointEq := coordinates.occurrence.injective (congrArg Prod.fst pairEq)
    cases pointEq
    have entryEq := (ledgerCoordinates.entry point.2.1).injective (congrArg Prod.snd pairEq)
    cases entryEq
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
