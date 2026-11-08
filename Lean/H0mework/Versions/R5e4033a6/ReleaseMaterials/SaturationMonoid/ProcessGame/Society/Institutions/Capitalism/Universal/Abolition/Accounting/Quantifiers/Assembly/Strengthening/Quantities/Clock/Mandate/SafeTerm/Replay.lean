import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Interval
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm

open Source.Program PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Current" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Action" => Request Party Good Port (State Party Technology) Instrument
local notation "Word" => List Action
variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port))

def PaidItems (current : Current) (index : Nat) (word : Word) : Prop :=
  ∀ item ∈ ((law base scope).execute current index word).items,
    (law base scope).Valid item.before item.request

instance (current : Current) (index : Nat) (word : Word) :
    Decidable (PaidItems base scope current index word) := by
  unfold PaidItems
  infer_instance

def itemGuards (current : Current) (index : Nat) (word : Word) : List Guard :=
  ((law base scope).execute current index word).items.map fun item =>
    guard base scope item.before item.request

private theorem paid_cons (current : Current) (index : Nat) (action : Action) (tail : Word) :
    PaidItems base scope current index (action :: tail) ↔ (law base scope).Valid current action ∧
      PaidItems base scope ((law base scope).step current action) (index + 1) tail := by
  simp only [PaidItems, RawLaw.execute, List.forall_mem_cons]

private theorem guards_cons (current : Current) (index : Nat) (action : Action)
    (tail : Word) (cutoff : ℚ) :
    (∀ one ∈ itemGuards base scope current index (action :: tail), one.Holds cutoff) ↔
      (guard base scope current action).Holds cutoff ∧
        ∀ one ∈ itemGuards base scope ((law base scope).step current action) (index + 1) tail,
          one.Holds cutoff := by
  simp only [itemGuards, RawLaw.execute, List.map_cons, List.forall_mem_cons]

/-- The clock conditions are necessary and sufficient for every original
payment in this word to keep executing. The full execution result is then
identical, including the original item positions, stock and claims. -/
theorem replays_paid_word_exactly (current : Current) (index : Nat) (word : Word) (cutoff : ℚ)
    (paid : PaidItems base scope current index word) :
    (PaidItems base (withCutoff scope cutoff) current index word ↔
      (Interval.ofGuards (itemGuards base scope current index word)).Holds cutoff) ∧
    ((Interval.ofGuards (itemGuards base scope current index word)).Holds cutoff →
      (law base (withCutoff scope cutoff)).execute current index word =
        (law base scope).execute current index word) := by
  simp only [Interval.of_guards_holds_iff]
  induction word generalizing current index with
  | nil => simp [PaidItems, itemGuards, RawLaw.execute]
  | cons action tail ih =>
    have old := (paid_cons base scope current index action tail).mp paid
    rw [paid_cons, guards_cons]
    have localCut := original_valid_iff_guard base scope current action cutoff old.1
    have rest := ih ((law base scope).step current action) (index + 1) old.2
    constructor
    · constructor
      · rintro ⟨admitted, next⟩
        have fits := localCut.mp admitted
        rw [original_paid_step_keeps_the_entire_current base scope current action cutoff old.1 fits] at next
        exact ⟨fits, rest.1.mp next⟩
      · rintro ⟨fits, next⟩
        refine ⟨localCut.mpr fits, ?_⟩
        rw [original_paid_step_keeps_the_entire_current base scope current action cutoff old.1 fits]
        exact rest.1.mpr next
    · rintro ⟨fits, next⟩
      simp only [RawLaw.execute,
        original_paid_step_keeps_the_entire_current base scope current action cutoff old.1 fits,
        rest.2 next]

theorem word_preserves_next_clock_and_current (current : Current) (word : Word) (cutoff : ℚ)
    (paid : PaidItems base scope current 0 word)
    (fits : (Interval.ofGuards (itemGuards base scope current 0 word)).Holds cutoff) :
    (law base (withCutoff scope cutoff)).next current word = (law base scope).next current word := by
  simp only [RawLaw.next, (replays_paid_word_exactly base scope current 0 word cutoff paid).2 fits]
  rfl

theorem outside_guard_names_an_original_item (current : Current) (index : Nat) (word : Word)
    (cutoff : ℚ)
    (outside : ¬ (Interval.ofGuards (itemGuards base scope current index word)).Holds cutoff) :
    ∃ item ∈ ((law base scope).execute current index word).items,
      ¬ (guard base scope item.before item.request).Holds cutoff := by
  classical
  rw [Interval.of_guards_holds_iff] at outside
  obtain ⟨one, inside, invalid⟩ := not_forall₂.mp outside
  obtain ⟨item, actual, same⟩ := List.mem_map.mp inside
  exact ⟨item, actual, same ▸ invalid⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
