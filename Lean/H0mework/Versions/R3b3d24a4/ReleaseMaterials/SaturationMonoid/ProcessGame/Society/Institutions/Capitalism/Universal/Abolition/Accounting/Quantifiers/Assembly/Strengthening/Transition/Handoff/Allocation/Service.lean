import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Affine
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Data

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {n : ℕ} {Row Lot : Type*}

def decode (index : Row × Lot ≃ Fin n) (values : Fin n → ℚ) (row : Row) (lot : Lot) : ℚ :=
  values (index (row, lot))

def encode (index : Row × Lot ≃ Fin n) (allocation : Row → Lot → ℚ) (i : Fin n) : ℚ :=
  allocation (index.symm i).1 (index.symm i).2

@[simp] theorem decode_encode (index : Row × Lot ≃ Fin n) (allocation : Row → Lot → ℚ) :
    decode index (encode index allocation) = allocation := by
  funext row lot
  simp [decode, encode]

def edge (index : Row × Lot ≃ Fin n) (row : Row) (lot : Lot) : Affine n :=
  Affine.variableAt (index (row, lot))

@[simp] theorem edge_eval (index : Row × Lot ≃ Fin n) (values : Fin n → ℚ) (row : Row) (lot : Lot) :
    (edge index row lot).eval values = decode index values row lot := by simp [edge, decode]

def edgeConstraints (network : Network Row Lot) (index : Row × Lot ≃ Fin n) (row : Row) (lot : Lot) :
    List (Inequality n) :=
  Affine.le (Affine.literal 0) (edge index row lot) ::
    if network.allows row lot then [] else [Affine.le (edge index row lot) (Affine.literal 0)]

theorem edgeConstraints_exact (network : Network Row Lot) (index : Row × Lot ≃ Fin n)
    (row : Row) (lot : Lot) (values : Fin n → ℚ) :
    Feasible (edgeConstraints network index row lot) values ↔
      0 ≤ decode index values row lot ∧ (network.allows row lot = false → decode index values row lot = 0) := by
  cases permits : network.allows row lot with
  | false =>
    simp only [edgeConstraints, permits, Bool.false_eq_true, if_false, feasible_cons, Affine.holds_le,
      Affine.eval_literal, edge_eval, feasible_nil, and_true, true_implies]
    exact ⟨fun bounds => ⟨bounds.1, le_antisymm bounds.2 bounds.1⟩, fun bounds => ⟨bounds.1, bounds.2.le⟩⟩
  | true => simp [edgeConstraints, permits, feasible_cons]

variable [Fintype Lot]

def rowConstraints (network : Network Row Lot) (due : Row → Bool)
    (index : Row × Lot ≃ Fin n) (row : Row) : List (Inequality n) :=
  let total := Affine.sumOver (edge index row)
  Affine.le total (Affine.literal (network.need row)) ::
    if due row then [Affine.le (Affine.literal (network.need row)) total] else []

theorem rowConstraints_exact (network : Network Row Lot) (due : Row → Bool)
    (index : Row × Lot ≃ Fin n) (row : Row) (values : Fin n → ℚ) :
    Feasible (rowConstraints network due index row) values ↔
      Network.rowTotal (decode index values) row ≤ network.need row ∧
        (due row = true → Network.rowTotal (decode index values) row = network.need row) := by
  cases matured : due row with
  | false => simp [rowConstraints, matured, feasible_cons, Network.rowTotal]
  | true =>
    simp only [rowConstraints, matured, if_true, feasible_cons, Affine.holds_le, Affine.eval_sumOver,
      Affine.eval_literal, edge_eval, feasible_nil, and_true,
      true_implies, Network.rowTotal]
    exact ⟨fun bounds => ⟨bounds.1, le_antisymm bounds.1 bounds.2⟩, fun bounds => ⟨bounds.1, bounds.2.ge⟩⟩

variable [Fintype Row]

def serviceConstraints (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n)
    (rows : List Row) (lots : List Lot) : List (Inequality n) :=
  ((rows.flatMap fun row => lots.flatMap (edgeConstraints network index row)) ++
    (rows.flatMap (rowConstraints network due index))) ++
    lots.map (fun lot => Affine.le (Affine.sumOver (fun row => edge index row lot))
      (Affine.literal (network.capacity lot)))

def Covers (network : Network Row Lot) (due : Row → Bool) (allocation : Row → Lot → ℚ) : Prop :=
  network.Admissible allocation ∧ ∀ row, due row = true → Network.rowTotal allocation row = network.need row

theorem serviceConstraints_exact (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n)
    (rows : List Row) (lots : List Lot) (allRows : ∀ row, row ∈ rows) (allLots : ∀ lot, lot ∈ lots)
    (values : Fin n → ℚ) :
    Feasible (serviceConstraints network due index rows lots) values ↔ Covers network due (decode index values) := by
  simp only [serviceConstraints, feasible_append, feasible_flatMap, feasible_map, edgeConstraints_exact,
    rowConstraints_exact, Affine.holds_le, Affine.eval_sumOver, Affine.eval_literal, edge_eval,
    Covers, Network.Admissible, Network.columnTotal]
  constructor
  · rintro ⟨⟨edges, assigned⟩, capacity⟩
    exact ⟨⟨fun row lot => edges row (allRows row) lot (allLots lot),
      fun row => (assigned row (allRows row)).1, fun lot => capacity lot (allLots lot)⟩,
      fun row => (assigned row (allRows row)).2⟩
  · rintro ⟨⟨edges, assigned, capacity⟩, paid⟩
    exact ⟨⟨fun row _ lot _ => edges row lot, fun row _ => ⟨assigned row, paid row⟩⟩,
      fun lot _ => capacity lot⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
