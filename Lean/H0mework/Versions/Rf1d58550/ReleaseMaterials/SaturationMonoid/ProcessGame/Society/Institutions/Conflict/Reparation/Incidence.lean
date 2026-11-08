import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

abbrev Key (Party Good : Type) := Party × Party × Good

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- The original signature puts the debit across a community boundary
without the bearer’s consent. Publicly permissive stock ports can also
carry an unassented foreign debit. -/
def Coercive (community : Party → Community) (item : Item) (key : Key Party Good) : Prop :=
  community key.1 ≠ community key.2.1 ∧ item.request.signer = key.2.1 ∧
    key.1 ∉ item.request.consents

instance (community : Party → Community) (item : Item) (key : Key Party Good) :
    Decidable (Coercive community item key) := by
  unfold Coercive
  infer_instance

/-- Debit is measured in the original good after deducting the credit from
the very same item. Rejected proposals have no material effect. -/
def loss (law : Law) (community : Party → Community) (item : Item) (key : Key Party Good) : ℚ :=
  if Coercive community item key then
    max 0 (flowAt (law.actualDebit item.before item.request) key.1 key.2.2 -
      flowAt (law.actualCredit item.before item.request) key.1 key.2.2)
  else 0

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem loss_nonnegative (law : Law) (community : Party → Community) (item : Item) (key : Key Party Good) :
    0 ≤ loss law community item key := by
  unfold loss
  split
  · exact le_max_left _ _
  · exact le_rfl

omit [DecidableEq Port] in
theorem positive_loss_is_an_actual_foreign_debit (law : Law) (community : Party → Community)
    (item : Item) (key : Key Party Good) (positive : 0 < loss law community item key) :
    Coercive community item key ∧ law.Valid item.before item.request ∧
      (law.step item.before item.request).stock key.1 key.2.2 =
        item.before.stock key.1 key.2.2 - loss law community item key := by
  have controlled : Coercive community item key := by
    by_contra contrary
    simp [loss, contrary] at positive
  have admitted : law.Valid item.before item.request := by
    by_contra contrary
    simp [loss, controlled, RawLaw.actualDebit, RawLaw.actualCredit, contrary, flowAt, amount] at positive
  have strict : 0 < flowAt (law.actualDebit item.before item.request) key.1 key.2.2 -
      flowAt (law.actualCredit item.before item.request) key.1 key.2.2 := by
    have amountPositive := positive
    rw [loss, if_pos controlled, lt_max_iff] at amountPositive
    exact amountPositive.resolve_left (lt_irrefl _)
  refine ⟨controlled, admitted, ?_⟩
  rw [loss, if_pos controlled, max_eq_right strict.le]
  have balance := law.material_step_balance item.before item.request key.1 key.2.2
  linarith

abbrev occurred (source : C) (word : Word) : List Item :=
  source.native.input.law.rawItems source.raw word

def gross (source : C) (word : Word) (community : Party → Community) (key : Key Party Good) : ℚ :=
  ((occurred source word).map (fun item => loss source.native.input.law community item key)).sum

theorem loss_le_gross_of_mem (source : C) (word : Word) (community : Party → Community)
    (key : Key Party Good) (item : Item) (present : item ∈ occurred source word) :
    loss source.native.input.law community item key ≤ gross source word community key := by
  unfold gross
  apply List.single_le_sum
  · rintro value listed
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp listed
    exact loss_nonnegative _ _ original _
  · exact List.mem_map_of_mem present

def exposedKeys (source : C) (word : Word) : List (Key Party Good) :=
  ((occurred source word).flatMap fun item =>
    (source.native.input.law.actualDebit item.before item.request).map fun entry =>
      (entry.1.1, item.request.signer, entry.1.2)).dedup

/-- A readout of one fixed paid occurrence. It contains no independently
spendable stock, authority or ledger. Repeated debits at an address aggregate. -/
structure ClaimAt (source : C) (word : Word) (community : Party → Community) (key : Key Party Good) : Prop where
  private mk ::
  paid : Root.Paid source word
  positive : 0 < gross source word community key

def assess (source : C) (word : Word) (community : Party → Community) (paid : Root.Paid source word)
    (key : Key Party Good) : Option (PLift (ClaimAt source word community key)) :=
  if positive : 0 < gross source word community key then some ⟨⟨paid, positive⟩⟩ else none

def claims (source : C) (word : Word) (community : Party → Community) (paid : Root.Paid source word) :
    List {key : Key Party Good // ClaimAt source word community key} :=
  (exposedKeys source word).filterMap fun key => (assess source word community paid key).map
    (fun claim => ⟨key, claim.down⟩)

theorem ClaimAt.has_original_loss {source : C} {word : Word} {community : Party → Community} {key : Key Party Good}
    (claim : ClaimAt source word community key) :
    ∃ item ∈ occurred source word, 0 < loss source.native.input.law community item key := by
  by_contra noLoss
  have empty : gross source word community key = 0 := by
    unfold gross
    apply List.sum_eq_zero
    rintro value present
    obtain ⟨item, member, rfl⟩ := List.mem_map.mp present
    exact le_antisymm (le_of_not_gt fun positive => noLoss ⟨item, member, positive⟩)
      (loss_nonnegative _ _ _ _)
  exact (ne_of_gt claim.positive) empty

theorem original_inventory {source : C} {word : Word} (paid : Root.Paid source word) :
    Quantities.Execution.inventory source (Quantities.Execution.primitiveScript word) =
      (occurred source word).map (fun item => { item with index := 0 }) := by
  have execution := PublicFunction.execute_physical_of_authorized source.native.input.law source.raw 0 word
    (fun item member => PublicFunction.valid_physical _ _ _ (paid.authorized item member))
    (fun item member => paid.authorized item member)
  rw [Quantities.Execution.primitive_inventory paid.trace 0]
  exact congrArg (fun result : ExecutionResult Party Good Port Technology Instrument =>
    result.items.map (fun item => { item with index := 0 })) execution.symm

theorem ClaimAt.key_is_an_original_address {source : C} {word : Word} {community : Party → Community}
    {key : Key Party Good} (claim : ClaimAt source word community key) : key ∈ exposedKeys source word := by
  obtain ⟨item, original, positive⟩ := claim.has_original_loss
  let law := source.native.input.law
  have ⟨controlled, valid, _⟩ := positive_loss_is_an_actual_foreign_debit law community item key positive
  have incoming : 0 ≤ flowAt (law.actualCredit item.before item.request) key.1 key.2.2 := by
    rw [RawLaw.actualCredit, if_pos valid]
    exact amount_nonnegative _ valid.2.2.2.2.1 _
  have real : ∃ entry ∈ law.actualDebit item.before item.request, entry.1 = (key.1, key.2.2) := by
    by_contra absent
    have debitZero : flowAt (law.actualDebit item.before item.request) key.1 key.2.2 = 0 :=
      amount_zero_of_absent _ _ (fun entry listed exactAddress => absent ⟨entry, listed, exactAddress⟩)
    rw [loss, if_pos controlled, debitZero, zero_sub, max_eq_left (neg_nonpos.mpr incoming)] at positive
    exact (lt_irrefl _ positive).elim
  obtain ⟨entry, listed, address⟩ := real
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨item, original, List.mem_map.mpr ⟨entry, listed, ?_⟩⟩
  rw [address, controlled.2.1]

theorem every_positive_address_is_assessed (source : C) (word : Word) (community : Party → Community)
    (paid : Root.Paid source word) {key : Key Party Good} (positive : 0 < gross source word community key) :
    ∃ claim ∈ claims source word community paid, claim.val = key := by
  let claim : ClaimAt source word community key := ⟨paid, positive⟩
  refine ⟨⟨key, claim⟩, List.mem_filterMap.mpr ⟨key, claim.key_is_an_original_address, ?_⟩, rfl⟩
  simp [assess, positive]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation
