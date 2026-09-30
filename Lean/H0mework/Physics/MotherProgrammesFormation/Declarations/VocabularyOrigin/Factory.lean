import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Factory
import H0mework.Foundation.Source.Root

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev Current (m : M) := {x : B // bit m 0 x}
abbrev Anchor (m : M) := {x : B // bit m 1 x}
abbrev Incidence (m : M) := {x : B // bit m 2 x}
abbrev Lineage (m : M) := {x : B // bit m 3 x}
abbrev Native (m : M) (c : Current m) := {w : B // r2 m 4 c.val w}
abbrev Relation (m : M) (c : Current m) := {w : B // r2 m 5 c.val w}
abbrev Continued (m : M) (c : Current m) := {w : B // r2 m 6 c.val w}
abbrev Redirect (m : M) (c : Current m) := {w : B // r2 m 7 c.val w}
abbrev Terminal (m : M) (c : Current m) := {w : B // r2 m 8 c.val w}
abbrev CofinalEvent (m : M) := {w : B // bit m 9 w}

structure Check (m : M) : Prop where
  anchor : ∀ c : Current m, ∃! a : Anchor m, r2 m 10 c.val a.val
  incidence : ∀ c : Current m, ∃! a : Incidence m, r2 m 11 c.val a.val
  lineage : ∀ c : Current m, ∃! a : Lineage m, r2 m 12 c.val a.val
  nativeTarget : ∀ (c : Current m) (w : Native m c), ∃! t : Current m, r3 m 13 c.val w.val t.val
  relationTarget : ∀ (c : Current m) (w : Relation m c), ∃! t : Current m, r3 m 14 c.val w.val t.val
  continuedTarget : ∀ (c : Current m) (w : Continued m c), ∃! t : Current m, r3 m 15 c.val w.val t.val
  redirectTarget : ∀ (c : Current m) (w : Redirect m c), ∃! t : Current m, r3 m 16 c.val w.val t.val
  cofinalTarget : ∀ e : CofinalEvent m, ∃! t : Current m, r2 m 17 e.val t.val
  cofinalPath : ∀ (e : CofinalEvent m) (n : Nat), ∃! t : Current m, r2 m (20 + n) e.val t.val
  cofinalEmit : ∀ e f : CofinalEvent m, bit m 18 e.val → bit m 18 f.val → e = f

private def output {Y : Type} {p : Y → Prop} (unique : ∃! y, p y) : Y := Classical.choose unique

def emitted? (m : M) : Option (CofinalEvent m) :=
  if selected : ∃ e : CofinalEvent m, bit m 18 e.val then some (Classical.choose selected) else none

/-- Current, all five complete payload families, and the entire cofinal law
are formed from the same reader. The source-only factory checks graph output
uniqueness internally before entering the original Vocabulary constructor. -/
private def assemble (m : M) (h : Check m) : Vocabulary.{0} where
  Current := Current m
  Anchor := Anchor m
  Incidence := Incidence m
  Lineage := Lineage m
  anchorAt := fun c => output (h.anchor c)
  incidenceAt := fun c => output (h.incidence c)
  lineageAt := fun c => output (h.lineage c)
  NativeWriteAt := Native m
  RelationWriteAt := Relation m
  ContinuedTransportAt := Continued m
  BorromeanRedirectAt := Redirect m
  FaithfulTerminalAt := Terminal m
  nativeTarget := fun {c} w => output (h.nativeTarget c w)
  relationTarget := fun {c} w => output (h.relationTarget c w)
  continuedTarget := fun {c} w => output (h.continuedTarget c w)
  redirectTarget := fun {c} w => output (h.redirectTarget c w)
  cofinal := {
    Event := CofinalEvent m
    emit? := emitted? m
    pathAt := fun e n => output (h.cofinalPath e n)
    target := fun e => output (h.cofinalTarget e) }

def formVocabulary (m : M) : Option Vocabulary.{0} :=
  if h : Check m then some (assemble m h) else none

theorem formed (m : M) (h : Check m) : formVocabulary m = some (assemble m h) := by
  simp only [formVocabulary, dif_pos h]

theorem rejected (m : M) (h : ¬ Check m) : formVocabulary m = none := by
  simp only [formVocabulary, dif_neg h]

theorem emitted_selected (m : M) (e : CofinalEvent m) (selected : emitted? m = some e) : bit m 18 e.val := by
  unfold emitted? at selected
  split at selected
  · rename_i existsEvent
    have same := Option.some.inj selected
    exact same ▸ Classical.choose_spec existsEvent
  · cases selected

theorem selected_emitted (m : M) (h : Check m) (e : CofinalEvent m) (selected : bit m 18 e.val) :
    emitted? m = some e := by
  have existsEvent : ∃ e : CofinalEvent m, bit m 18 e.val := ⟨e, selected⟩
  unfold emitted?
  rw [dif_pos existsEvent]
  exact congrArg some (h.cofinalEmit _ e (Classical.choose_spec existsEvent) selected)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherVocabularyOrigin
