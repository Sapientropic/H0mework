import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Array

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

structure Entry where
  count : Nat
  hilbert : Array ℚ
  mass : ℚ
  clock : ℚ

def encode (bound stride count : Nat) (raw : SourceRetainedReceiver.Raw bound stride) : Entry where
  count := count
  hilbert := Array.ofFn (fun position => (count : ℚ) * raw.1 position)
  mass := (count : ℚ) * raw.2.1
  clock := (count : ℚ) * raw.2.2

def advance (bound : Nat) (previous : Entry) : Entry where
  count := previous.count + 1
  hilbert := addAt previous.hilbert (bound + 2) 1
  mass := previous.mass + 1
  clock := previous.clock + (bound + 3 : ℚ)

def decode (bound stride : Nat) (entry : Entry) : SourceRetainedReceiver.Raw bound stride :=
  (fun position => coordinate entry.hilbert position.val / entry.count,
    entry.mass / entry.count, entry.clock / entry.count)

theorem decode_encode (bound stride count : Nat) (raw : SourceRetainedReceiver.Raw bound stride)
    (positive : count ≠ 0) : decode bound stride (encode bound stride count raw) = raw := by
  have nonzero : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr positive
  apply Prod.ext
  · funext position
    simp only [decode, encode, coordinate, Array.getElem?_ofFn, dif_pos position.isLt, Option.getD_some]
    exact mul_div_cancel_left₀ _ nonzero
  · apply Prod.ext
    · exact mul_div_cancel_left₀ _ nonzero
    · exact mul_div_cancel_left₀ _ nonzero

theorem advance_coordinate (bound : Nat) (entry : Entry) (position : Nat) :
    coordinate (advance bound entry).hilbert position = coordinate entry.hilbert position +
      if position = bound + 2 then 1 else 0 :=
  addAt_at entry.hilbert (bound + 2) 1 position

end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
