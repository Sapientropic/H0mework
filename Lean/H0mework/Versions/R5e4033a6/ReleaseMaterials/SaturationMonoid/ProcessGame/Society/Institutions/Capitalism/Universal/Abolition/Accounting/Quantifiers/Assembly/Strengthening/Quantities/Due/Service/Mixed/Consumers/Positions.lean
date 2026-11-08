import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers.Clock
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Decision
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Execution
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity
open Innovation.Contribution.Pricing.Consumers.Actual
  (quoteCut source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers (liveClock)

noncomputable section

abbrev atoms : Finset Bool := ([false] : List Bool).toFinset
abbrev fragments : Finset Bool := ([true] : List Bool).toFinset

def halfSlot : ServiceSlot Bool Bool := ⟨false, [(false, 1 / 2)], .external⟩

def agenda (fragment : Bool) : PublicTaskSpec Bool Bool where
  slots := [halfSlot]
  earliest := liveClock
  deadline := if fragment then liveClock else lateClock
  demand := ⟨halfSlot, List.mem_cons_self, (false, 1 / 2), List.mem_cons_self, by decide +kernel⟩

abbrev Position := Ordinal lifeSource mixedScript
abbrev Line := Need fragments agenda
abbrev Receipt := Supply lifeSource mixedScript fragments agenda
private abbrev Item := ExecutionItem Bool Bool Bool Unit Unit
private abbrev law := Physical.Public.interpreter Joint.Consumers.Compact.input

theorem four_material_positions : (inventory lifeSource mixedScript).length = 4 := by
  rw [← timedInventory_is_the_original_inventory, the_original_half_debits_commit_at_distinct_actual_clocks,
    List.length_map]
  unfold timedReceipts
  rw [List.length_append, List.length_map, List.length_map]
  unfold RawLaw.rawItems
  rw [RawLaw.inventory_length, RawLaw.inventory_length]
  rfl

def earlyPosition : Position := ⟨0, by rw [four_material_positions]; decide⟩
def latePosition : Position := ⟨3, by rw [four_material_positions]; decide⟩

def fragmentSlot : Slot fragments agenda := ⟨⟨true, by decide⟩, ⟨0, Nat.zero_lt_one⟩⟩
def fragmentLine : Line := ⟨fragmentSlot, ⟨false, by decide⟩⟩

private theorem only_fragment_slot (slot : Slot fragments agenda) : slot = fragmentSlot := by
  obtain ⟨id, ordinal⟩ := slot
  have sameId : id = fragmentSlot.1 := Subtype.ext (Finset.mem_singleton.mp id.property)
  subst id
  have sameOrdinal : ordinal = fragmentSlot.2 := by
    apply Fin.ext
    have inside : ordinal.val < 1 := ordinal.isLt
    change ordinal.val = 0
    omega
  cases sameOrdinal
  rfl

theorem only_fragment_line (line : Line) : line = fragmentLine := by
  obtain ⟨slot, good⟩ := line
  have sameSlot := only_fragment_slot slot
  subst slot
  have sameGood : good = fragmentLine.2 := Subtype.ext (Finset.mem_singleton.mp good.property)
  cases sameGood
  rfl

abbrev uniqueLine : Unique Line := ⟨⟨fragmentLine⟩, only_fragment_line⟩

private theorem fragment_goods : goods fragments agenda = {false} := by
  ext good
  unfold goods
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨slot, _, inside⟩
    rw [only_fragment_slot slot] at inside
    exact inside
  · intro inside
    exact ⟨fragmentSlot, Finset.mem_univ _, inside⟩

theorem receipt_good (receipt : Receipt) : receipt.2.val = false := by
  have units := congrArg (fun support : Finset Bool => receipt.2.val ∈ support) fragment_goods
  exact Finset.mem_singleton.mp (units.mp receipt.2.property)

def earlyReceipt : Receipt :=
  (earlyPosition, ⟨false, by rw [fragment_goods]; simp⟩)

private def signedWhole (start : ℚ) (entry : Item × ℚ) : Prop :=
  (start ≤ entry.1.before.clock ∧ law.Valid entry.1.before entry.1.request ∧
    Exit.Necessity.UseMatches entry.1.request.operation halfSlot.bearer halfSlot.goods halfSlot.purpose) ∧
    entry.2 ≤ start + 1

private def signedFragment (start : ℚ) (entry : Item × ℚ) : Prop :=
  start ≤ entry.1.before.clock ∧ entry.2 ≤ start ∧ law.Valid entry.1.before entry.1.request ∧
    useFor entry.1 halfSlot

private instance (start : ℚ) (entry : Item × ℚ) : Decidable (signedWhole start entry) := by
  letI : Decidable (law.Valid entry.1.before entry.1.request) :=
    RawLaw.instDecidableValid law entry.1.before entry.1.request
  unfold signedWhole
  infer_instance

private instance (start : ℚ) (entry : Item × ℚ) : Decidable (signedFragment start entry) := by
  letI : Decidable (law.Valid entry.1.before entry.1.request) :=
    RawLaw.instDecidableValid law entry.1.before entry.1.request
  unfold signedFragment
  infer_instance

private def observed (start : ℚ) (entry : Item × ℚ) : ℚ × Bool × Bool :=
  (paidAmount law entry.1 false, decide (signedWhole start entry), decide (signedFragment start entry))

private def measured (position : Fin 4) : ℚ × Bool × Bool :=
  (if position.val = 0 ∨ position.val = 3 then 1 / 2 else 0,
    decide (position.val = 0 ∨ position.val = 3), decide (position.val = 0))

private theorem measurement (position : Fin 4) :
    timedReceipts[position.val]?.map (observed liveClock) = some (measured position) := by
  unfold timedReceipts lateClock liveClock
  rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
  fin_cases position <;> decide +kernel

private theorem actual_timed_position (position : Position) :
    some (timedAt lifeSource mixedScript position) = timedReceipts[position.val]? := by
  rw [← the_original_half_debits_commit_at_distinct_actual_clocks]
  unfold timedAt
  exact (List.getElem?_eq_getElem _).symm

private theorem actual_observation (position : Position) :
    observed liveClock (timedAt lifeSource mixedScript position) = measured (Fin.cast four_material_positions position) := by
  exact Option.some.inj ((congrArg (Option.map (observed liveClock)) (actual_timed_position position)).trans
    (measurement (Fin.cast four_material_positions position)))

theorem original_before_stock (position : Position) (party good : Bool) :
    0 ≤ (timedAt lifeSource mixedScript position).1.before.stock party good := by
  let check := fun entry : Item × ℚ => decide (0 ≤ entry.1.before.stock party good)
  have funded (ordinal : Fin 4) : timedReceipts[ordinal.val]?.map check = some true := by
    unfold check timedReceipts lateClock liveClock
    rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    fin_cases ordinal <;> cases party <;> cases good <;> decide +kernel
  have exactRead := congrArg (Option.map check) (actual_timed_position position)
  exact of_decide_eq_true (Option.some.inj (exactRead.trans (funded (Fin.cast four_material_positions position))))

private def wholeSlot : WholeSlot agenda := ⟨false, ⟨0, Nat.zero_lt_one⟩⟩

private abbrev shape := Clock.Window.Shared.geometry lifeSource atoms agenda mixedScript

private theorem whole_slot_original : shape.leftCarrier = {wholeSlot} := by
  ext slot
  change slot ∈ atoms.sigma (fun id => (Clock.Window.geometry lifeSource (agenda id) mixedScript).leftCarrier) ↔ _
  rw [Finset.mem_sigma, Finset.mem_singleton]
  constructor
  · rintro ⟨id, _⟩
    obtain ⟨part, position⟩ := slot
    have first : part = false := Finset.mem_singleton.mp id
    subst part
    have only : position = wholeSlot.2 := by
      apply Fin.ext
      have less : position.val < 1 := position.isLt
      change position.val = 0
      omega
    cases only
    rfl
  · rintro rfl
    exact ⟨by decide, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩⟩

def originalWhole (position : Position) (fits : position.val = 0 ∨ position.val = 3) :
    WholeChoice lifeSource mixedScript atoms agenda := by
  refine ⟨{(wholeSlot, position)}, shape.singleton_mem_matchings ?_, ?_⟩
  · apply (shape.mem_edgeCarrier_iff _).mpr
    refine ⟨by rw [whole_slot_original]; simp, Finset.mem_univ _, ?_⟩
    have numeric := congrArg (fun report : ℚ × Bool × Bool => report.2.1) (actual_observation position)
    have accepted : signedWhole liveClock (timedAt lifeSource mixedScript position) :=
      of_decide_eq_true (numeric.trans (decide_eq_true fits))
    change (liveClock ≤ ((inventory lifeSource mixedScript).get position).before.clock ∧
      (Physical.Public.interpreter lifeSource.native.input).Valid ((inventory lifeSource mixedScript).get position).before
        ((inventory lifeSource mixedScript).get position).request ∧
      Exit.Necessity.UseMatches ((inventory lifeSource mixedScript).get position).request.operation
        halfSlot.bearer halfSlot.goods halfSlot.purpose) ∧ (timedAt lifeSource mixedScript position).2 ≤ lateClock
    rw [← timedAt_is_the_same_original_item, source_input_is_the_original_registered_input]
    exact accepted
  · rw [whole_slot_original, Finset.card_singleton, Finset.card_singleton]

theorem early_fragment_only (line : Line) (receipt : Receipt) (reserved : Finset Position) :
    (network lifeSource mixedScript fragments agenda reserved).allows line receipt = true ↔
      receipt.1 ∉ reserved ∧ receipt.1.val = 0 := by
  have observedFragment := congrArg (fun report : ℚ × Bool × Bool => report.2.2) (actual_observation receipt.1)
  have exactFragment : signedFragment liveClock (timedAt lifeSource mixedScript receipt.1) ↔ receipt.1.val = 0 :=
    decide_eq_decide.mp observedFragment
  have owner : lifeSource.native.handlerFace.rootRead = law := by
    change Physical.Public.interpreter lifeSource.native.input = _
    rw [source_input_is_the_original_registered_input]
  rw [network_allows_iff, only_fragment_line line]
  have sameUnit := (receipt_good receipt).symm
  constructor
  · intro allowed
    refine ⟨allowed.1, exactFragment.mp ?_⟩
    exact ⟨allowed.2.2.1, allowed.2.2.2.1,
      owner ▸ allowed.2.2.2.2.1, allowed.2.2.2.2.2⟩
  · rintro ⟨unreserved, atEarly⟩
    have allowed := exactFragment.mpr atEarly
    exact ⟨unreserved, sameUnit, allowed.1, allowed.2.1,
      owner.symm ▸ allowed.2.2.1, allowed.2.2.2⟩

theorem early_capacity (reserved : Finset Position) (available : earlyPosition ∉ reserved) :
    (network lifeSource mixedScript fragments agenda reserved).capacity earlyReceipt = 1 / 2 := by
  have observedAmount := congrArg Prod.fst (actual_observation earlyPosition)
  change (if earlyPosition ∈ reserved then 0 else
    paidAmount lifeSource.native.handlerFace.rootRead (timedAt lifeSource mixedScript earlyPosition).1 false) = _
  rw [if_neg available, show lifeSource.native.handlerFace.rootRead = Physical.Public.interpreter lifeSource.native.input from rfl,
    source_input_is_the_original_registered_input]
  exact observedAmount

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers
