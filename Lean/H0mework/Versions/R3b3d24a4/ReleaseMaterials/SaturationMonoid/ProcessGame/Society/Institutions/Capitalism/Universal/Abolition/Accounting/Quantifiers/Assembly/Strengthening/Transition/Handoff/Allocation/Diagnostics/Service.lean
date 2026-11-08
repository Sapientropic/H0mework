import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Tags
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {Row Lot : Type*} {n : ℕ}

inductive ServiceSite (Row Lot : Type*) where
  | nonnegative (row : Row) (lot : Lot)
  | ineligible (row : Row) (lot : Lot)
  | originalNeed (row : Row)
  | duePayment (row : Row)
  | originalDebit (lot : Lot)

private def edgeLabels (network : Network Row Lot) (row : Row) (lot : Lot) :
    List (ServiceSite Row Lot) :=
  .nonnegative row lot :: if network.allows row lot then [] else [.ineligible row lot]

private def edgeTagged (network : Network Row Lot) (index : Row × Lot ≃ Fin n) (row : Row) (lot : Lot) :
    List (Tagged (ServiceSite Row Lot) n) :=
  attach (edgeLabels network row lot) (edgeConstraints network index row lot)

private theorem edgeTagged_exact (network : Network Row Lot) (index : Row × Lot ≃ Fin n)
    (row : Row) (lot : Lot) :
    numeric (edgeTagged network index row lot) = edgeConstraints network index row lot := by
  apply attach_exact
  cases allowed : network.allows row lot <;> simp [edgeLabels, edgeConstraints, allowed]

variable [Fintype Lot]

private def rowLabels (due : Row → Bool) (row : Row) : List (ServiceSite Row Lot) :=
  .originalNeed row :: if due row then [.duePayment row] else []

private def rowTagged (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n) (row : Row) :
    List (Tagged (ServiceSite Row Lot) n) :=
  attach (rowLabels due row) (rowConstraints network due index row)

private theorem rowTagged_exact (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n)
    (row : Row) :
    numeric (rowTagged network due index row) = rowConstraints network due index row := by
  apply attach_exact
  cases matured : due row <;> simp [rowLabels, rowConstraints, matured]

variable [Fintype Row]

def serviceTagged (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n)
    (rows : List Row) (lots : List Lot) : List (Tagged (ServiceSite Row Lot) n) :=
  ((rows.flatMap fun row => lots.flatMap (edgeTagged network index row)) ++
    (rows.flatMap (rowTagged network due index))) ++
    lots.map (fun lot => ⟨.originalDebit lot, Affine.le (Affine.sumOver (fun row => edge index row lot))
      (Affine.literal (network.capacity lot))⟩)

theorem serviceTagged_exact (network : Network Row Lot) (due : Row → Bool) (index : Row × Lot ≃ Fin n)
    (rows : List Row) (lots : List Lot) :
    numeric (serviceTagged network due index rows lots) = serviceConstraints network due index rows lots := by
  simp only [serviceTagged, serviceConstraints, numeric_append, numeric_flatMap, edgeTagged_exact, rowTagged_exact]
  simp only [numeric, List.map_map, Function.comp_def]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
