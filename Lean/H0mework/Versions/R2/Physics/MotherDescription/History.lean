import H0mework.Versions.R2.Physics.MotherDescription.Structure

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.WholeDescription

open Stage9C.Revision

noncomputable section

/-- The index is causal depth, not a replacement physical clock. -/
def pointHistory (index : Nat) : List Pointwise :=
  (List.range (index + 1)).map (fun depth => point (SpinPair.visit depth).current)

def weakHistory (index : Nat) : List Compact :=
  (List.range (index + 1)).map (fun depth => weak (SpinPair.visit depth).current)

theorem history_commutes (index : Nat) :
    (pointHistory index).map equivalence = weakHistory index := by
  simp only [pointHistory, weakHistory, List.map_map, Function.comp_def, equivalence_point]

theorem weakHistory_length (index : Nat) : (weakHistory index).length = index + 1 := by
  simp only [weakHistory, List.length_map, List.length_range]

theorem weakHistory_injective : Function.Injective weakHistory := by
  intro left right same
  have length := congrArg List.length same
  rw [weakHistory_length, weakHistory_length] at length
  exact Nat.add_right_cancel length

abbrev History := Set.range weakHistory

def historyAt (index : Nat) : History := ⟨weakHistory index, index, rfl⟩

def decodeHistory (history : History) : Recognition.Visit :=
  SpinPair.visit (history.val.length - 1)

theorem decodeHistory_at (index : Nat) : decodeHistory (historyAt index) = SpinPair.visit index := by
  simp only [decodeHistory, historyAt, weakHistory_length, Nat.add_sub_cancel]

theorem history_step (index : Nat) :
    weakHistory (index + 1) = weakHistory index ++
      [weakNext (weak (SpinPair.visit index).current)] := by
  change weakHistory (index + 1) = weakHistory index ++
    [weakAction SpinPair.next (weak (SpinPair.visit index).current)]
  rw [weakAction_weak SpinPair.next (SpinPair.visit index).current]
  unfold weakHistory
  rw [List.range_succ, List.map_append]
  rfl

theorem historical_fields_recovered (index : Nat) :
    (weakHistory index).map decodeWeak =
      (List.range (index + 1)).map (fun depth => (SpinPair.visit depth).current) := by
  simp only [weakHistory, List.map_map, Function.comp_def, decodeWeak_weak]

end
end SaturationMonoid.PhysicsCore.Stage10.WholeDescription
