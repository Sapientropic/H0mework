import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.VocabularyOrigin.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Value

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

/-- Expose the exact declaration already returned by the signed factory. -/
def vocabulary (m : M) (h : MotherVocabularyOrigin.Check m) : Vocabulary.{0} :=
  (show {V : Vocabulary.{0} // MotherVocabularyOrigin.formVocabulary m = some V}
    from ⟨_, MotherVocabularyOrigin.formed m h⟩).val

theorem vocabulary_formed (m : M) (h : MotherVocabularyOrigin.Check m) :
    MotherVocabularyOrigin.formVocabulary m = some (vocabulary m h) :=
  MotherVocabularyOrigin.formed m h

def baseMaterial (m : M) : M := (MotherHigherLawValue.split m).1
def eventMaterial (m : M) : M := (MotherHigherLawValue.split m).2

abbrev V (base : M) (h : MotherVocabularyOrigin.Check base) := vocabulary base h

abbrev EventAt (base events : M) (c : MotherVocabularyOrigin.Current base) :=
  {event : B // r2 events 0 c.val event}

def compileGraph (base events : M) (h : MotherVocabularyOrigin.Check base)
    {c : (V base h).Current} (event : EventAt base events c) : EvolutionAt (V base h) c → Prop
  | .nativeWrite w => r3 events 1 c.val event.val w.val
  | .relationWrite w => r3 events 2 c.val event.val w.val
  | .continuedTransport w => r3 events 3 c.val event.val w.val
  | .borromeanRedirect w => r3 events 4 c.val event.val w.val
  | .faithfulTerminal w => r3 events 5 c.val event.val w.val

def Check (base events : M) (h : MotherVocabularyOrigin.Check base) : Prop :=
  ∀ (c : (V base h).Current) (event : EventAt base events c),
    ∃! value : EvolutionAt (V base h) c, compileGraph base events h event value

def actual (base events : M) (h : MotherVocabularyOrigin.Check base)
    (checked : Check base events h) : ActualEventAlgebra (V base h) where
  OccurrenceAt := EventAt base events
  compile := fun {c} event => Classical.choose (checked c event)

def formComponents (base events : M) : Option (Σ V : Vocabulary.{0}, ActualEventAlgebra V) :=
  if h : MotherVocabularyOrigin.Check base then
    if checked : Check base events h then some ⟨V base h, actual base events h checked⟩ else none
  else none

/-- Both the entire event family and its full compiler are formed from the
same mother material as the original Vocabulary. Graph totality and uniqueness
are checked internally across all five constructors. -/
def formActual (m : M) : Option (Σ V : Vocabulary.{0}, ActualEventAlgebra V) :=
  formComponents (baseMaterial m) (eventMaterial m)

theorem formed (base events : M) (h : MotherVocabularyOrigin.Check base)
    (checked : Check base events h) :
    formActual (MotherHigherLawValue.pack (base, events)) =
      some ⟨V base h, actual base events h checked⟩ := by
  unfold formActual baseMaterial eventMaterial
  rw [MotherHigherLawValue.split_pack]
  simp only [formComponents, dif_pos h, dif_pos checked]

theorem compile_selected (base events : M) (h : MotherVocabularyOrigin.Check base)
    (checked : Check base events h) {c : (V base h).Current} (event : EventAt base events c) :
    compileGraph base events h event ((actual base events h checked).compile event) :=
  (Classical.choose_spec (checked c event)).1

theorem compile_eq (base events : M) (h : MotherVocabularyOrigin.Check base)
    (checked : Check base events h) {c : (V base h).Current} (event : EventAt base events c)
    (value : EvolutionAt (V base h) c) (selected : compileGraph base events h event value) :
    (actual base events h checked).compile event = value :=
  ((Classical.choose_spec (checked c event)).2 value selected).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActualOrigin
