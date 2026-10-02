import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.TerminalConsumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev WriteContext {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  MotherNetworkOrigin.RowContext source

abbrev IncidenceContext {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} (source : SourceNativeSource N V) :=
  Point source × N.Incidence × N.Incidence

def incidenceContext {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (context : WriteContext source) : IncidenceContext source :=
  (⟨context.1, context.2.1⟩, N.incidenceAt context.2.1.1, N.incidenceAt context.2.2.1)

def incidenceCoordinatesOfFormation (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) : value.1.Incidence ↪ B := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · have same := Option.some.inj formed
            exact Eq.mp (congrArg (fun source : SourceValue => source.1.Incidence ↪ B) same)
              (show (MotherNativeSourceOrigin.network _ hn).Incidence ↪ B from
                ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

theorem terminal_compilation_formed (material : M) (value : SourceValue)
    (compiled : CompilationSection value.2.2) (rows : LedgerTerminalRowSourceAt value.2.2)
    (formed : formTerminalSource material = some ⟨value, compiled, rows⟩) :
    formCompilation (MotherHigherLawValue.split material).1 = some ⟨value, compiled⟩ := by
  unfold formTerminalSource at formed
  dsimp only at formed
  obtain ⟨⟨base, output⟩, baseFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  dsimp only at selected
  split at selected
  · have same := congrArg (fun result : Σ value : SourceValue,
        CompilationSection value.2.2 × LedgerTerminalRowSourceAt value.2.2 =>
      (⟨result.1, result.2.1⟩ : Σ value : SourceValue, CompilationSection value.2.2)) (Option.some.inj selected)
    exact baseFormed.trans (congrArg some same)
  · cases selected

def incidenceContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (incidence : N.Incidence ↪ B) : IncidenceContext source ↪ B where
  toFun := fun context => MotherHigherLawFamily.pair (coordinates.occurrence context.1,
    MotherHigherLawFamily.pair (incidence context.2.1, incidence context.2.2))
  inj' := by
    intro left right same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have pointEq := coordinates.occurrence.injective (congrArg Prod.fst pairEq)
    have incidenceEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd pairEq)
    exact Prod.ext pointEq (Prod.ext (incidence.injective (congrArg Prod.fst incidenceEq))
      (incidence.injective (congrArg Prod.snd incidenceEq)))

def writeContextEmbedding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledger : LedgerCoordinates N) : WriteContext source ↪ B where
  toFun := fun context => MotherHigherLawFamily.pair
    (rowContextEmbedding coordinates ledger ⟨⟨context.1, context.2.1⟩, context.2.2.2.1⟩,
      MotherHigherLawFamily.pair (ledger.support context.2.2.1, ledger.entry context.2.2.1 context.2.2.2.2))
  inj' := by
    rintro ⟨c, event, target, a, b⟩ ⟨d, other, target', a', b'⟩ same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have rowEq := (rowContextEmbedding coordinates ledger).injective (congrArg Prod.fst pairEq)
    have pointEq := congrArg Sigma.fst rowEq
    cases pointEq
    have entryEq : a = a' := eq_of_heq (Sigma.mk.inj rowEq).2
    cases entryEq
    have targetEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd pairEq)
    have supportEq := ledger.support.injective (congrArg Prod.fst targetEq)
    cases supportEq
    have entryEq := (ledger.entry target).injective (congrArg Prod.snd targetEq)
    cases entryEq
    rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
