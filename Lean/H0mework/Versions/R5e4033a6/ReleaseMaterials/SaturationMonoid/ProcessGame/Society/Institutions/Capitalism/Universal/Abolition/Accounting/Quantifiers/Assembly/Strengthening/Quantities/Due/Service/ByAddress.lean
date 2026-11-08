import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow
open scoped BigOperators

section FiniteCut

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L]

omit [Fintype L] [DecidableEq L] in
private theorem neighbours_of_filtered_lines (net : Network L R) (group : Finset L)
    (lineSelected : L → Prop) (itemSelected : R → Prop)
    [DecidablePred lineSelected] [DecidablePred itemSelected]
    (agrees : ∀ line item, net.allows line item = true → (lineSelected line ↔ itemSelected item)) :
    net.neighbours (group.filter lineSelected) = (net.neighbours group).filter itemSelected := by
  ext item
  simp only [Finset.mem_filter, Network.mem_neighbours]
  constructor
  · rintro ⟨line, ⟨present, selected⟩, allowed⟩
    exact ⟨⟨line, present, allowed⟩, (agrees line item allowed).mp selected⟩
  · rintro ⟨⟨line, present, allowed⟩, selected⟩
    exact ⟨line, ⟨present, (agrees line item allowed).mpr selected⟩, allowed⟩

private theorem allocated_amount_plus_cut_gap_le_required (net : Network L R) {allocation : L → R → ℚ}
    (admitted : net.Admissible allocation) (rows group : Finset L) (inside : group ⊆ rows) :
    (∑ line ∈ rows, Network.rowTotal allocation line) + net.gap group ≤ net.demandOf rows := by
  have paidSplit := Finset.sum_sdiff (f := Network.rowTotal allocation) inside
  have demandSplit := Finset.sum_sdiff (f := net.need) inside
  have supplied := net.group_allocation_le_compatible_supply admitted group
  have outside : (∑ line ∈ rows \ group, Network.rowTotal allocation line) ≤ net.demandOf (rows \ group) :=
    Finset.sum_le_sum fun line _ => admitted.2.1 line
  unfold Network.gap Network.demandOf at *
  linarith only [paidSplit, demandSplit, supplied, outside]

omit [Fintype L] [DecidableEq L] in
private theorem cut_gap_splits_on_matching_selection (net : Network L R) (group : Finset L)
    (lineSelected : L → Prop) (itemSelected : R → Prop)
    [DecidablePred lineSelected] [DecidablePred itemSelected]
    (agrees : ∀ line item, net.allows line item = true → (lineSelected line ↔ itemSelected item)) :
    net.gap (group.filter lineSelected) + net.gap (group.filter fun line => ¬ lineSelected line) = net.gap group := by
  have byLine := Finset.sum_filter_add_sum_filter_not group lineSelected net.need
  have byItem := Finset.sum_filter_add_sum_filter_not (net.neighbours group) itemSelected net.capacity
  rw [← neighbours_of_filtered_lines net group _ _ agrees,
      ← neighbours_of_filtered_lines net group _ _ (fun line item allowed => not_congr (agrees line item allowed))] at byItem
  unfold Network.gap Network.demandOf Network.supplyOf
  linarith only [byLine, byItem]

private theorem filtered_cut_is_tight (net : Network L R) (receipt : net.Certificate)
    (lineSelected : L → Prop) (itemSelected : R → Prop)
    [DecidablePred lineSelected] [DecidablePred itemSelected]
    (agrees : ∀ line item, net.allows line item = true → (lineSelected line ↔ itemSelected item)) :
    (∑ line ∈ Finset.univ.filter lineSelected, Network.rowTotal receipt.allocation line) +
      net.gap (receipt.group.filter lineSelected) = net.demandOf (Finset.univ.filter lineSelected) := by
  let all := (Finset.univ : Finset L)
  let rows := all.filter lineSelected
  let others := all.filter fun line => ¬ lineSelected line
  let blocked := receipt.group.filter lineSelected
  let otherBlock := receipt.group.filter fun line => ¬ lineSelected line
  have inside : blocked ⊆ rows := Finset.filter_subset_filter _ (Finset.subset_univ _)
  have otherInside : otherBlock ⊆ others := Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hereBound := allocated_amount_plus_cut_gap_le_required net receipt.admitted rows blocked inside
  have otherBound := allocated_amount_plus_cut_gap_le_required net receipt.admitted others otherBlock otherInside
  have actual := receipt.optimal.2.2
  have cutSplit : net.gap blocked + net.gap otherBlock = net.gap receipt.group :=
    cut_gap_splits_on_matching_selection net receipt.group lineSelected itemSelected agrees
  have paidSplit : (∑ line ∈ rows, Network.rowTotal receipt.allocation line) +
      (∑ line ∈ others, Network.rowTotal receipt.allocation line) = Network.total receipt.allocation :=
    Finset.sum_filter_add_sum_filter_not all lineSelected (Network.rowTotal receipt.allocation)
  have demandSplit : net.demandOf rows + net.demandOf others = net.demandOf all :=
    Finset.sum_filter_add_sum_filter_not all lineSelected net.need
  change (∑ line ∈ rows, Network.rowTotal receipt.allocation line) + net.gap blocked = net.demandOf rows
  exact le_antisymm hereBound (by linarith only [actual, cutSplit, paidSplit, demandSplit, otherBound])

end FiniteCut

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {TaskId : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Task" => PublicTaskSpec Party Good
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

def lineAddress {ids : Finset TaskId} {task : TaskId → Task} (line : Need ids task) : Party × Good :=
  (line.1.spec.bearer, line.2.val)

def linesAtAddress {ids : Finset TaskId} {task : TaskId → Task} (group : Finset (Need ids task))
    (address : Party × Good) : Finset (Need ids task) :=
  group.filter fun line => lineAddress (ids := ids) (task := task) line = address

def debitAddress (item : Item) (good : Good) : Option (Party × Good) :=
  match item.request.operation with
  | .use bearer _ _ => some (bearer, good)
  | _ => none

theorem an_eligible_receipt_has_the_same_original_bearer_and_good
    {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    {reserved : Finset (Ordinal source script)}
    (line : Need ids task) (item : Supply source script ids task)
    (allowed : (network source script ids task reserved).allows line item = true) :
    debitAddress (Execution.timedAt source script item.1).1 item.2.val = some (lineAddress (ids := ids) (task := task) line) := by
  have eligible := (network_allows_iff source script ids task reserved line item).mp allowed
  have purpose := eligible.2.2.2.2.2
  unfold useFor at purpose
  cases operation : (Execution.timedAt source script item.1).1.request.operation with
  | use bearer bundle purposeTag =>
    simp only [debitAddress, operation]
    rw [operation] at purpose
    exact congrArg some (Prod.ext purpose.1 eligible.2.1.symm)
  | _ => simp [operation] at purpose

/-- A homogeneous receipt cannot trade any bearer or good for another.
Each address therefore inherits the exact cut of a globally tight allocation. -/
theorem address_bounds [DecidableEq TaskId]
    {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    (net : Network (Need ids task) (Supply source script ids task))
    (homogeneous : ∀ line item, net.allows line item = true →
      debitAddress (Execution.timedAt source script item.1).1 item.2.val = some (lineAddress (ids := ids) (task := task) line))
    (receipt : net.Certificate) (address : Party × Good) :
    let rows := linesAtAddress (ids := ids) (task := task) Finset.univ address
    let shortageRows := linesAtAddress (ids := ids) (task := task) receipt.group address
    (∑ line ∈ rows, (net.need line - Network.rowTotal receipt.allocation line)) = net.gap shortageRows ∧
    (∀ other, net.Admissible other →
      (∑ line ∈ rows, Network.rowTotal other line) ≤ ∑ line ∈ rows, Network.rowTotal receipt.allocation line) ∧
    (∀ group ⊆ rows, net.gap group ≤ net.gap shortageRows) := by
  dsimp only
  let here := fun line : Need ids task => lineAddress (ids := ids) (task := task) line = address
  let there := fun item : Supply source script ids task =>
    debitAddress (Execution.timedAt source script item.1).1 item.2.val = some address
  let rows := Finset.univ.filter here
  let blocked := receipt.group.filter here
  have inside : blocked ⊆ rows := Finset.filter_subset_filter _ (Finset.subset_univ _)
  have agrees (line : Need ids task) (item : Supply source script ids task)
      (allowed : net.allows line item = true) : here line ↔ there item := by
    dsimp only [here, there]
    rw [homogeneous line item allowed, Option.some.injEq]
  have tight : (∑ line ∈ rows, Network.rowTotal receipt.allocation line) + net.gap blocked = net.demandOf rows :=
    filtered_cut_is_tight net receipt here there agrees
  change (∑ line ∈ rows, (net.need line - Network.rowTotal receipt.allocation line)) = net.gap blocked ∧
    (∀ other, net.Admissible other →
      (∑ line ∈ rows, Network.rowTotal other line) ≤ ∑ line ∈ rows, Network.rowTotal receipt.allocation line) ∧
    (∀ group ⊆ rows, net.gap group ≤ net.gap blocked)
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib]
    change net.demandOf rows - (∑ line ∈ rows, Network.rowTotal receipt.allocation line) = net.gap blocked
    linarith only [tight]
  · intro other admitted
    have bound := allocated_amount_plus_cut_gap_le_required net admitted rows blocked inside
    linarith only [tight, bound]
  · intro group contained
    have bound := allocated_amount_plus_cut_gap_le_required net receipt.admitted rows group contained
    linarith only [tight, bound]

theorem each_original_address_has_a_tight_payment_and_named_shortage
    [DecidableEq TaskId]
    {source : C} {script : Script} {ids : Finset TaskId} {task : TaskId → Task}
    {reserved : Finset (Ordinal source script)}
    (receipt : (network source script ids task reserved).Certificate) (address : Party × Good) :
    let net := network source script ids task reserved
    let rows := linesAtAddress (ids := ids) (task := task) Finset.univ address
    let shortageRows := linesAtAddress (ids := ids) (task := task) receipt.group address
    (∑ line ∈ rows, remaining receipt line) = net.gap shortageRows ∧
    (∀ other, net.Admissible other →
      (∑ line ∈ rows, Network.rowTotal other line) ≤ ∑ line ∈ rows, Network.rowTotal receipt.allocation line) ∧
    (∀ group ⊆ rows, net.gap group ≤ net.gap shortageRows) :=
  address_bounds (source := source) (script := script) (ids := ids) (task := task)
    (network source script ids task reserved)
    (an_eligible_receipt_has_the_same_original_bearer_and_good (reserved := reserved)) receipt address

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service
