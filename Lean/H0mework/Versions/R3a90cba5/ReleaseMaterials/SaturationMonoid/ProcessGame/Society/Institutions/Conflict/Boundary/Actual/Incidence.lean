import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Incidence
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation (Key loss)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

abbrev items (cut : C) (input : Input) := Quantities.Execution.inventory cut [input]
abbrev materialLaw (cut : C) := Physical.Public.interpreter cut.native.input
abbrev Site (cut : C) (input : Input) := Fin (items cut input).length × Key Party Good

/-- A damage address belongs to an actual material item of one source tick.
The list position distinguishes occurrences even when the native item indices coincide. -/
def DamageAt (cut : C) (input : Input) (community : Party → Community) :=
  { site : Site cut input // 0 < loss (materialLaw cut) community (items cut input)[site.1] site.2 }

instance (cut : C) (input : Input) (community : Party → Community) :
    DecidableEq (DamageAt cut input community) := by
  unfold DamageAt
  infer_instance

namespace DamageAt

variable {cut : Root.Cut Party Good Port Technology Instrument}
  {input : Option (Compile.RawInput Party Good Port Technology Instrument)} {community : Party → Community}
  (damage : DamageAt cut input community)

abbrev position := damage.val.1
abbrev key := damage.val.2
abbrev item := (items cut input)[damage.position]
abbrev quantity := loss (materialLaw cut) community damage.item damage.key
theorem positive : 0 < damage.quantity := damage.property

theorem source_item : damage.item ∈ items cut input := List.getElem_mem _

theorem actual_foreign_debit :
    Reparation.Coercive community damage.item damage.key ∧
      (materialLaw cut).Valid damage.item.before damage.item.request ∧
      ((materialLaw cut).step damage.item.before damage.item.request).stock damage.key.1 damage.key.2.2 =
        damage.item.before.stock damage.key.1 damage.key.2.2 - damage.quantity :=
  Reparation.positive_loss_is_an_actual_foreign_debit _ _ _ _ damage.positive

end DamageAt

private def keysAt (cut : C) (item : Item) : List (Key Party Good) :=
  ((materialLaw cut).actualDebit item.before item.request).map fun part =>
    (part.1.1, item.request.signer, part.1.2)

private theorem original_key {cut : C} {input : Input} {community : Party → Community}
    (damage : DamageAt cut input community) : damage.key ∈ keysAt cut damage.item := by
  let law := materialLaw cut
  let item := damage.item
  let key := damage.key
  obtain ⟨controlled, valid, _⟩ := damage.actual_foreign_debit
  have nonnegative : 0 ≤ flowAt (law.actualCredit item.before item.request) key.1 key.2.2 := by
    rw [RawLaw.actualCredit, if_pos valid]
    exact amount_nonnegative _ valid.2.2.2.2.1 _
  have real : ∃ entry ∈ law.actualDebit item.before item.request, entry.1 = (key.1, key.2.2) := by
    by_contra absent
    have debitZero : flowAt (law.actualDebit item.before item.request) key.1 key.2.2 = 0 :=
      amount_zero_of_absent _ _ (fun entry listed exactAddress => absent ⟨entry, listed, exactAddress⟩)
    have positive : 0 < loss law community item key := damage.positive
    rw [loss, if_pos controlled, debitZero, zero_sub, max_eq_left (neg_nonpos.mpr nonnegative)] at positive
    exact (lt_irrefl _ positive).elim
  obtain ⟨entry, present, address⟩ := real
  apply List.mem_map.mpr
  exact ⟨entry, present, by rw [address, controlled.2.1]⟩

/-- Enumerate each actual loss once, in its material item order. -/
def damages (cut : C) (input : Input) (community : Party → Community) : List (DamageAt cut input community) :=
  ((List.finRange (items cut input).length).flatMap fun position =>
    ((keysAt cut (items cut input)[position]).dedup).filterMap fun key =>
      if positive : 0 < loss (materialLaw cut) community (items cut input)[position] key then
        some ⟨(position, key), positive⟩
      else none).dedup

theorem every_actual_debit_is_assessed {cut : C} {input : Input} {community : Party → Community}
    (damage : DamageAt cut input community) : damage ∈ damages cut input community := by
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨damage.position, List.mem_finRange _, List.mem_filterMap.mpr ⟨damage.key, ?_, ?_⟩⟩
  · exact List.mem_dedup.mpr (original_key damage)
  · rcases damage with ⟨⟨position, key⟩, positive⟩
    exact dif_pos positive

theorem each_damage_address_occurs_once (cut : C) (input : Input) (community : Party → Community) :
    (damages cut input community).Nodup := List.nodup_dedup _

theorem no_material_write_has_no_damage (cut : C) (input : Input) (community : Party → Community)
    (empty : items cut input = []) : damages cut input community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have present := damage.source_item
  rw [empty] at present
  exact (List.not_mem_nil present).elim

theorem one_tick_keeps_its_whole_write_and_the_actual_debits (cut : C) (input : Input)
    (community : Party → Community) :
    Quantities.Recorded cut [input] ∧ ∀ damage : DamageAt cut input community,
      damage ∈ damages cut input community ∧
      (materialLaw cut).Valid damage.item.before damage.item.request :=
  ⟨Quantities.record cut [input], fun damage =>
    ⟨every_actual_debit_is_assessed damage, damage.actual_foreign_debit.2.1⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual
