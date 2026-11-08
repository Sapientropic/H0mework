import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.ByAddress
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Restrict

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

section RestrictCut

variable {L R : Type*} [Fintype L] [Fintype R] (net : Network L R) (keep : L → Bool)

private theorem zero_at_inactive {allocation : L → R → ℚ}
    (admitted : (net.restrict keep).Admissible allocation) (line : L) (inactive : keep line = false) :
    Network.rowTotal allocation line = 0 := by
  apply le_antisymm
  · simpa [Network.restrict, inactive] using admitted.2.1 line
  · exact Finset.sum_nonneg fun item _ => (admitted.1 line item).1

private theorem clipped_is_admissible {allocation : L → R → ℚ} (admitted : net.Admissible allocation) :
    (net.restrict keep).Admissible (fun line item => if keep line then allocation line item else 0) := by
  refine ⟨fun line item => ?_, fun line => ?_, fun item => ?_⟩
  · cases active : keep line
    · simp [active]
    · simpa [active, Network.restrict] using admitted.1 line item
  · cases active : keep line
    · simp [active, Network.rowTotal, Network.restrict]
    · simpa [active, Network.rowTotal, Network.restrict] using admitted.2.1 line
  · refine (Finset.sum_le_sum fun line _ => ?_).trans (admitted.2.2 item)
    cases active : keep line
    · simpa [active] using (admitted.1 line item).1
    · simp [active]

omit [Fintype L] in
private theorem on_inactive_complement (group : Finset L) {line : L}
    (present : line ∈ group) (excluded : line ∉ group.filter fun l => keep l = true) : keep line = false := by
  cases active : keep line
  · rfl
  · exact (excluded (Finset.mem_filter.mpr ⟨present, active⟩)).elim

omit [Fintype L] in
private theorem selected_cut_has_at_least_the_old_gap (group : Finset L) :
    (net.restrict keep).gap group ≤ (net.restrict keep).gap (group.filter fun l => keep l = true) := by
  let selected := group.filter fun l => keep l = true
  let cutNet := net.restrict keep
  have sameDemand : cutNet.demandOf selected = cutNet.demandOf group := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro line present excluded
    simp only [cutNet, Network.restrict, on_inactive_complement keep group present excluded, Bool.false_eq_true, if_false]
  have lessSupply : cutNet.supplyOf (cutNet.neighbours selected) ≤ cutNet.supplyOf (cutNet.neighbours group) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro item present
      obtain ⟨line, row, allowed⟩ := (cutNet.mem_neighbours selected item).mp present
      exact (cutNet.mem_neighbours group item).mpr ⟨line, (Finset.mem_filter.mp row).1, allowed⟩
    · exact fun item _ _ => cutNet.capacity_nonnegative item
  change cutNet.demandOf group - _ ≤ cutNet.demandOf selected - _
  linarith only [sameDemand, lessSupply]

omit [Fintype L] in
private theorem active_group_has_its_original_gap (group : Finset L) (active : ∀ line ∈ group, keep line = true) :
    (net.restrict keep).gap group = net.gap group := by
  have sameDemand : (net.restrict keep).demandOf group = net.demandOf group := by
    apply Finset.sum_congr rfl
    intro line present
    simp only [Network.restrict, active line present, if_true]
  unfold Network.gap
  rw [sameDemand]
  rfl

private theorem restricted_sum_on_active_rows {allocation : L → R → ℚ}
    (admitted : (net.restrict keep).Admissible allocation) (rows : Finset L) :
    (∑ line ∈ rows.filter (fun l => keep l = true), Network.rowTotal allocation line) =
      ∑ line ∈ rows, Network.rowTotal allocation line := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro line present excluded
  exact zero_at_inactive net keep admitted line (on_inactive_complement keep rows present excluded)

end RestrictCut

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*} [DecidableEq TaskId]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good

/-- A due cut names only active original rows. Its addresswise deficit is
exact and its chosen payment dominates every original feasible allocation on
that address's active rows. -/
theorem each_original_address_has_its_exact_due_cut
    {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    {reserved : Finset (Ordinal source script)}
    (keep : Need ids task → Bool)
    (receipt : ((network source script ids task reserved).restrict keep).Certificate) (address : Party × Good) :
    let net := network source script ids task reserved
    let rows := (linesAtAddress (ids := ids) (task := task) Finset.univ address).filter fun line => keep line = true
    let named := (linesAtAddress (ids := ids) (task := task) receipt.group address).filter fun line => keep line = true
    (∑ line ∈ rows, (net.need line - Network.rowTotal receipt.allocation line)) = net.gap named ∧
      (∀ other, net.Admissible other →
        (∑ line ∈ rows, Network.rowTotal other line) ≤ ∑ line ∈ rows, Network.rowTotal receipt.allocation line) ∧
      (∀ group ⊆ rows, net.gap group ≤ net.gap named) := by
  dsimp only
  let net := network source script ids task reserved
  let cutNet := net.restrict keep
  let all := linesAtAddress (ids := ids) (task := task) Finset.univ address
  let originalCut := linesAtAddress (ids := ids) (task := task) receipt.group address
  let rows := all.filter fun line => keep line = true
  let named := originalCut.filter fun line => keep line = true
  have bounds := address_bounds (source := source) (script := script) (ids := ids) (task := task)
    cutNet (an_eligible_receipt_has_the_same_original_bearer_and_good (reserved := reserved)) receipt address
  have names : named ⊆ all :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have exactGap : cutNet.gap originalCut = net.gap named := by
    have unchanged := le_antisymm (selected_cut_has_at_least_the_old_gap net keep originalCut) (bounds.2.2 named names)
    exact unchanged.trans (active_group_has_its_original_gap net keep named fun _ present => (Finset.mem_filter.mp present).2)
  have activeRemaining :
      (∑ line ∈ rows, (net.need line - Network.rowTotal receipt.allocation line)) =
        ∑ line ∈ all, (cutNet.need line - Network.rowTotal receipt.allocation line) := by
    calc
      _ = ∑ line ∈ rows, (cutNet.need line - Network.rowTotal receipt.allocation line) := by
        apply Finset.sum_congr rfl
        intro line present
        simp only [cutNet, Network.restrict, (Finset.mem_filter.mp present).2, if_true]
      _ = _ := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro line present outside
        have inactive := on_inactive_complement keep all present outside
        simp [cutNet, Network.restrict, inactive, zero_at_inactive net keep receipt.admitted line inactive]
  refine ⟨activeRemaining.trans (bounds.1.trans exactGap), ?_, ?_⟩
  · intro other legal
    let clipped := fun line item => if keep line then other line item else 0
    have admitted : cutNet.Admissible clipped := clipped_is_admissible net keep legal
    calc
      (∑ line ∈ rows, Network.rowTotal other line) =
          ∑ line ∈ rows, Network.rowTotal clipped line := by
        apply Finset.sum_congr rfl
        intro line present
        simp [Network.rowTotal, clipped, (Finset.mem_filter.mp present).2]
      _ = ∑ line ∈ all, Network.rowTotal clipped line := restricted_sum_on_active_rows net keep admitted all
      _ ≤ ∑ line ∈ all, Network.rowTotal receipt.allocation line := bounds.2.1 clipped admitted
      _ = ∑ line ∈ rows, Network.rowTotal receipt.allocation line :=
        (restricted_sum_on_active_rows net keep receipt.admitted all).symm
  · intro group present
    have unchanged := active_group_has_its_original_gap net keep group
      (fun line listed => (Finset.mem_filter.mp (present listed)).2)
    exact unchanged.symm.trans_le ((bounds.2.2 group (present.trans (Finset.filter_subset _ _))).trans_eq exactGap)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
