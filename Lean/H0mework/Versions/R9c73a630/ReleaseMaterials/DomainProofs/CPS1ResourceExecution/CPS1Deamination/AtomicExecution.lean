import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Machine

set_option autoImplicit false

namespace CPS1Deamination

open CPS1ResourceExecution

/-- The editing sector includes the DNA moieties, water and released
ammonia. Other stock entries retain their independent chemical accounts. -/
def editingAtoms (atom : Atom) : Species → Nat
  | .dna word => wordAtoms word atom
  | .water => waterAtoms atom
  | .ammonia => ammoniaAtoms atom
  | _ => 0

theorem primitive_atom_balance (left right : List Base) (atom : Atom) :
    moiety (editingAtoms atom) (Reaction.deaminate left right).reactants =
      moiety (editingAtoms atom) (Reaction.deaminate left right).products := by
  simpa [moiety, editingAtoms, Reaction.reactants, Reaction.products] using
    deamination_atom_balance left right atom

theorem fire_measure_preserved (reaction : Reaction) (stock next : Stock)
    (paid : fire reaction stock = .ok next) (measure : Species → Nat)
    (balanced : moiety measure reaction.reactants = moiety measure reaction.products) :
    moiety measure stock = moiety measure next :=
  Inventory.fire_measure_preserved Reaction.reactants Reaction.products reaction stock next paid measure balanced

theorem execution_measure_preserved (program : List Reaction) (stock : Stock)
    (measure : Species → Nat)
    (balanced : ∀ reaction ∈ program,
      moiety measure reaction.reactants = moiety measure reaction.products) :
    moiety measure stock = moiety measure (execute program stock).stock :=
  Inventory.execution_measure_preserved Reaction.reactants Reaction.products program stock measure balanced

theorem primitive_finite_inventory_consumed (left right : List Base) :
    fire (.deaminate left right) [.dna (left ++ Base.A :: right), .water] =
      .ok [.dna (left ++ Base.I :: right), .ammonia] := by
  simp [fire, Inventory.fire, Inventory.consume, Reaction.reactants, Reaction.products]

theorem primitive_without_water_cuts (left right : List Base) :
    fire (.deaminate left right) [.dna (left ++ Base.A :: right)] = .error .water := by
  simp [fire, Inventory.fire, Inventory.consume, Reaction.reactants]

theorem primitive_affinity (μ : Species → ℚ) (left right : List Base) :
    reactionAffinity μ (.deaminate left right) =
      μ (.dna (left ++ Base.A :: right)) + μ .water -
        (μ (.dna (left ++ Base.I :: right)) + μ .ammonia) := by
  simp [reactionAffinity, Inventory.reactionAffinity, Inventory.value, Reaction.reactants, Reaction.products]

end CPS1Deamination
