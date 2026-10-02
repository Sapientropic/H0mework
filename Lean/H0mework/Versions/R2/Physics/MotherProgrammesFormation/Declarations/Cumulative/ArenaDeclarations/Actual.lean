import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaDeclarations.JointHeader

/-! The original complete event-family and five-branch compiler constructor
on the same rank material. The actual Vocabulary is formed internally. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
open MotherArenaNetwork
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

/-- Expose the exact declaration already returned by the signed factory. -/
def vocabulary (m : M) (h : MotherArenaVocabulary.Check m) : Vocabulary.{0} :=
  (show {V : Vocabulary.{0} // MotherArenaVocabulary.formVocabulary m = some V}
    from ⟨_, MotherArenaVocabulary.formed m h⟩).val

theorem vocabulary_formed (m : M) (h : MotherArenaVocabulary.Check m) :
    MotherArenaVocabulary.formVocabulary m = some (vocabulary m h) :=
  MotherArenaVocabulary.formed m h

def baseMaterial (m : M) : M := ((MotherArenaHigher.split rank) m).1
def eventMaterial (m : M) : M := ((MotherArenaHigher.split rank) m).2

abbrev V (base : M) (h : MotherArenaVocabulary.Check base) := vocabulary base h

abbrev EventAt (base events : M) (c : MotherArenaVocabulary.Current base) :=
  {event : B // r2 events 0 c.val event}

def compileGraph (base events : M) (h : MotherArenaVocabulary.Check base)
    {c : (V base h).Current} (event : EventAt base events c) : EvolutionAt (V base h) c → Prop
  | .nativeWrite w => r3 events 1 c.val event.val w.val
  | .relationWrite w => r3 events 2 c.val event.val w.val
  | .continuedTransport w => r3 events 3 c.val event.val w.val
  | .borromeanRedirect w => r3 events 4 c.val event.val w.val
  | .faithfulTerminal w => r3 events 5 c.val event.val w.val

def Check (base events : M) (h : MotherArenaVocabulary.Check base) : Prop :=
  ∀ (c : (V base h).Current) (event : EventAt base events c),
    ∃! value : EvolutionAt (V base h) c, compileGraph base events h event value

def actual (base events : M) (h : MotherArenaVocabulary.Check base)
    (checked : Check base events h) : ActualEventAlgebra (V base h) where
  OccurrenceAt := EventAt base events
  compile := fun {c} event => Classical.choose (checked c event)

def formComponents (base events : M) : Option (Σ V : Vocabulary.{0}, ActualEventAlgebra V) :=
  if h : MotherArenaVocabulary.Check base then
    if checked : Check base events h then some ⟨V base h, actual base events h checked⟩ else none
  else none

/-- Both the entire event family and its full compiler are formed from the
same mother material as the original Vocabulary. Graph totality and uniqueness
are checked internally across all five constructors. -/
def formActual (m : M) : Option (Σ V : Vocabulary.{0}, ActualEventAlgebra V) :=
  formComponents (baseMaterial m) (eventMaterial m)

theorem formed (base events : M) (h : MotherArenaVocabulary.Check base)
    (checked : Check base events h) :
    formActual ((MotherArenaHigher.pack rank) (base, events)) =
      some ⟨V base h, actual base events h checked⟩ := by
  unfold formActual baseMaterial eventMaterial
  rw [(MotherArenaHigher.split_pack rank)]
  simp only [formComponents, dif_pos h, dif_pos checked]

theorem compile_selected (base events : M) (h : MotherArenaVocabulary.Check base)
    (checked : Check base events h) {c : (V base h).Current} (event : EventAt base events c) :
    compileGraph base events h event ((actual base events h checked).compile event) :=
  (Classical.choose_spec (checked c event)).1

theorem compile_eq (base events : M) (h : MotherArenaVocabulary.Check base)
    (checked : Check base events h) {c : (V base h).Current} (event : EventAt base events c)
    (value : EvolutionAt (V base h) c) (selected : compileGraph base events h event value) :
    (actual base events h checked).compile event = value :=
  ((Classical.choose_spec (checked c event)).2 value selected).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaActual
