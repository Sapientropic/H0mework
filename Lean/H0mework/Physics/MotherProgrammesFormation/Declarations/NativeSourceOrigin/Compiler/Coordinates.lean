import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure Coordinates {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (source : SourceNativeSource N V) where
  current : V.Current ↪ B
  event : ∀ c, source.toRootSource.actual.OccurrenceAt c ↪ B

def Coordinates.occurrence {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    {source : SourceNativeSource N V} (coordinates : Coordinates source) :
    (Sigma source.toRootSource.actual.OccurrenceAt) ↪ B where
  toFun := fun ⟨c, event⟩ => MotherHigherLawFamily.pair (coordinates.current c, coordinates.event c event)
  inj' := by
    rintro ⟨c, event⟩ ⟨d, other⟩ same
    have pairEq := MotherHigherLawFamily.pair_injective same
    have currentEq := coordinates.current.injective (congrArg Prod.fst pairEq)
    cases currentEq
    have eventEq := (coordinates.event c).injective (congrArg Prod.snd pairEq)
    cases eventEq
    rfl

private def canonicalCoordinates (net base events fields : M)
    (hn : MotherNetworkFactory.Check net) (hv : MotherVocabularyOrigin.Check base)
    (ha : MotherActualOrigin.Check base events hv)
    (graphs : MotherNativeSourceOrigin.AccountGraphs net base events fields)
    (compatible : MotherNativeSourceOrigin.Compatible net base events fields hn hv graphs) :
    Coordinates (MotherNativeSourceOrigin.native
      (MotherNativeSourceOrigin.rootSource net base events fields hn hv ha graphs compatible)) where
  current := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  event := fun c => (MotherNativeSourceOrigin.eventEquiv
      (MotherNativeSourceOrigin.rootSource net base events fields hn hv ha graphs compatible) c).symm.toEmbedding.trans
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

abbrev SourceValue := Σ N : WorldRelationNetwork.{0}, Σ V : Vocabulary.{0}, SourceNativeSource N V

/-- Addresses are recovered from the actual source factory output. They are
not a caller-supplied header or a new condition on the original physical P. -/
def coordinatesOfFormation (m : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource m = some value) : Coordinates value.2.2 := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · rename_i hv
      split at formed
      · rename_i ha
        split at formed
        · rename_i graphs
          split at formed
          · rename_i compatible
            have same := Option.some.inj formed
            exact Eq.mp (congrArg (fun source : SourceValue => Coordinates source.2.2) same)
              (canonicalCoordinates _ _ _ _ hn hv ha graphs compatible)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

def formCoordinatedSource (m : M) : Option (Σ source : SourceValue, Coordinates source.2.2) :=
  match formed : MotherNativeSourceOrigin.formSource m with
  | none => none
  | some source => some ⟨source, coordinatesOfFormation m source formed⟩

theorem coordinated_source_original (m : M) :
    (formCoordinatedSource m).map Sigma.fst = MotherNativeSourceOrigin.formSource m := by
  unfold formCoordinatedSource
  split <;> symm <;> assumption

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
