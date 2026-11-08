import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Restrict

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed

open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

variable {Choice L R : Type*} [Fintype L] [Fintype R]

structure NamedCut (net : Network L R) where
  receipt : net.Certificate
  positive : 0 < net.gap receipt.group

inductive ResidualSearch (net : Choice → Network L R)
  | noWhole (absent : ∀ _ : Choice, False)
  | short (available : Choice) (cuts : ∀ choice, NamedCut (net choice))
  | available (choice : Choice) (receipt : (net choice).Certificate)
      (complete : (net choice).Complete receipt.allocation)

/-- One exact rational residual problem per original whole assignment. -/
def searchResidual (net : Choice → Network L R) (choices : List Choice)
    (covers : ∀ choice, choice ∈ choices) (certify : ∀ choice, (net choice).Certificate) : ResidualSearch net :=
  match choices with
  | [] => .noWhole (fun choice => List.not_mem_nil (covers choice))
  | first :: rest =>
    let shortage := fun choice => 0 < (net choice).gap (certify choice).group
    match Abolition.Material.inspectList shortage (first :: rest) with
    | .clear all => .short first (fun choice => ⟨certify choice, all choice (covers choice)⟩)
    | .failure choice _ noShort =>
      .available choice (certify choice)
        ((certify choice).complete_or_original_shortage.resolve_right (fun positive => noShort (sub_pos.mpr positive)))

def ResidualSearch.hasAllocation {net : Choice → Network L R} : ResidualSearch net → Bool
  | .available .. => true
  | _ => false

theorem residual_search_passes_iff_some_assignment_fits [DecidableEq L]
    {net : Choice → Network L R} (result : ResidualSearch net) :
    result.hasAllocation = true ↔ ∃ choice allocation, (net choice).Complete allocation := by
  cases result with
  | noWhole absent =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun ⟨choice, _, _⟩ => (absent choice).elim⟩
  | short _ cuts =>
    exact ⟨fun impossible => Bool.noConfusion impossible, fun ⟨choice, allocation, pays⟩ =>
      (((cuts choice).receipt.gap_pos_iff_no_complete).mp (cuts choice).positive ⟨allocation, pays⟩).elim⟩
  | available choice receipt complete =>
    exact ⟨fun _ => ⟨choice, receipt.allocation, complete⟩, fun _ => rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed
