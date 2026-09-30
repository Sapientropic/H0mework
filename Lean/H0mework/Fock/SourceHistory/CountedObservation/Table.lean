import H0mework.Fock.SourceHistory.CountedObservation.Representation
import Mathlib.Data.List.AList

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

abbrev Table (Key : Type*) := AList (fun _ : Key => Entry)

def emptyEntry : Entry := ⟨0, #[], 0, 0⟩

variable {Key : Type*} [DecidableEq Key]

def lookup (table : Table Key) (key : Key) : Entry := (table.lookup key).getD emptyEntry

def collect (keys : List Key) (rows : Key → Entry) : Table Key :=
  keys.foldr (fun key table => table.insert key (rows key)) ∅

def fromInventory (bound stride : Nat) (keys : List Key)
    (frame : SourceRetainedReceiver.Frame Key bound stride) : Table Key :=
  collect keys (fun key => encode bound stride (frame.native key).1
    (SourceRetainedReceiver.rawAt bound stride frame key))

noncomputable def ofFrame (bound stride : Nat) (frame : SourceRetainedReceiver.Frame Key bound stride) : Table Key :=
  collect frame.keys.toList (fun key => encode bound stride (frame.native key).1
    (SourceRetainedReceiver.rawAt bound stride frame key))

def step (bound : Nat) (previous : Table Key) (added : Key) : Table Key :=
  previous.insert added (advance bound (lookup previous added))

def run (bound : Nat) (receipts : Nat → Key) (initial : Table Key) : Nat → Table Key :=
  Nat.rec initial (fun offset previous => step (bound + offset) previous (receipts offset))

theorem collect_lookup (keys : List Key) (rows : Key → Entry) (key : Key) :
    (collect keys rows).lookup key = if key ∈ keys then some (rows key) else none := by
  induction keys with
  | nil => rfl
  | cons first rest previous =>
    change (AList.insert first (rows first) (collect rest rows)).lookup key = _
    by_cases same : key = first
    · subst first
      simp only [AList.lookup_insert, List.mem_cons, true_or, ↓reduceIte]
    · rw [AList.lookup_insert_ne same, previous]
      simp only [List.mem_cons, same, false_or]

theorem collect_keys (keys : List Key) (rows : Key → Entry) (key : Key) :
    key ∈ collect keys rows ↔ key ∈ keys := by
  rw [← AList.lookup_isSome, collect_lookup]
  by_cases present : key ∈ keys <;> simp [present]

theorem ofFrame_lookup (bound stride : Nat) (frame : SourceRetainedReceiver.Frame Key bound stride) (key : Key) :
    lookup (ofFrame bound stride frame) key = if key ∈ frame.keys then
      encode bound stride (frame.native key).1 (SourceRetainedReceiver.rawAt bound stride frame key) else emptyEntry := by
  rw [lookup, ofFrame, collect_lookup]
  simp only [Finset.mem_toList]
  by_cases present : key ∈ frame.keys <;> simp only [present, ↓reduceIte, Option.getD_some, Option.getD_none]

theorem ofFrame_keys (bound stride : Nat) (frame : SourceRetainedReceiver.Frame Key bound stride) (key : Key) :
    key ∈ ofFrame bound stride frame ↔ key ∈ frame.keys := by
  rw [ofFrame, collect_keys, Finset.mem_toList]

theorem step_lookup (bound : Nat) (table : Table Key) (added key : Key) :
    lookup (step bound table added) key =
      if key = added then advance bound (lookup table key) else lookup table key := by
  by_cases same : key = added
  · subst added
    simp only [step, lookup, AList.lookup_insert, Option.getD_some, ↓reduceIte]
  · simp only [step, lookup, AList.lookup_insert_ne same, if_neg same]

theorem step_keys (bound : Nat) (table : Table Key) (added key : Key) :
    key ∈ step bound table added ↔ key = added ∨ key ∈ table := AList.mem_insert table

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
