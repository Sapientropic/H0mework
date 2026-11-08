import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual.Inventory
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Service
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Settlement.Profile

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual

open Source.Program PublicFunction Abolition.Root Abolition.Root.Registered Quantities
open _root_.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow

noncomputable section

def task (id : Bool) : PublicTaskSpec Bool Bool :=
  ⟨[⟨true, [(false,1)], .external⟩], if id then 5 else 4, if id then 6 else 5,
    ⟨_, List.mem_cons_self, _, List.mem_cons_self, by norm_num⟩⟩

def ordered : List Bool := [false,true]
abbrev word := script source proposal
abbrev Row := Due.Service.Need ordered.toFinset task
abbrev Lot := Due.Service.Supply source word ordered.toFinset task
abbrev Script := List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

def reserved (script : Script) : Finset (Due.Service.Ordinal source script) := ∅

def row (id : Bool) : Row :=
  ⟨⟨⟨id, by cases id <;> decide⟩, ⟨0, by change (0 : Nat) < 1; decide⟩⟩,
    ⟨false, by change false ∈ ({false} : Finset Bool); simp⟩⟩

theorem a_row_is_its_original_task (line : Row) : line = row line.1.1.val := by
  obtain ⟨⟨id, ⟨position, inside⟩⟩, ⟨good, supplied⟩⟩ := line
  change position < 1 at inside
  have zero : position = 0 := by omega
  subst position
  have same : good = false := Finset.mem_singleton.mp supplied
  subst good
  rfl

theorem original_demands_are_nonnegative : Due.Service.OriginalDemands ordered.toFinset task := by
  rintro ⟨id, ⟨position, inside⟩⟩
  change position < 1 at inside
  have zero : position = 0 := by omega
  subst position
  exact (by decide +kernel : NonnegativeBundle Bool [(false,1)])

def held : Finset Row := {row false}

theorem original_material_inventory :
    Execution.inventory source word = publicLaw.rawItems opening period ++ publicLaw.rawItems firstRaw period := by
  rw [← Execution.timedInventory_is_the_original_inventory, the_ten_original_items_keep_their_two_committing_clocks]
  simp only [List.map_append, List.map_map, Function.comp_def]
  change (publicLaw.rawItems opening period).map id ++ (publicLaw.rawItems firstRaw period).map id = _
  rw [List.map_id, List.map_id]

theorem original_inventory_length : (Execution.inventory source word).length = 10 := by
  rw [original_material_inventory, List.length_append]
  exact congrArg₂ (· + ·) (publicLaw.inventory_length opening 0 period)
    (publicLaw.inventory_length firstRaw 0 period)

def place (id : Bool) : Nat := if id then 9 else 4

def lot (id : Bool) : Lot :=
  (⟨place id, by rw [original_inventory_length]; cases id <;> decide⟩,
    Due.Settlement.originalUnit (row id))

theorem chosen_lots_are_distinct : lot false ≠ lot true := by
  intro shared
  have bad := congrArg (fun receipt : Lot => receipt.1.val) shared
  change (4 : Nat) = 9 at bad
  omega

def assigned (line : Row) (receipt : Lot) : ℚ :=
  if receipt = lot line.1.1.val then 1 else 0

def beforeService (initial : Raw) : Raw :=
  (publicLaw.execute initial 0 [production, provision, life false, life true]).final

def serviceItem (id : Bool) : ExecutionItem Bool Bool Bool Unit Unit :=
  ⟨4, beforeService (if id then firstRaw else opening), service⟩

theorem timed_lot (id : Bool) :
    Execution.timedAt source word (lot id).1 = (serviceItem id, if id then 6 else 5) := by
  have hit : (Execution.timedInventory source word)[place id]? = some (serviceItem id, if id then 6 else 5) := by
    rw [the_ten_original_items_keep_their_two_committing_clocks]
    cases id <;> rfl
  have inside : place id < (Execution.timedInventory source word).length :=
    (List.getElem?_eq_some_iff.mp hit).1
  rw [List.getElem?_eq_getElem inside] at hit
  exact Option.some.inj hit

theorem original_handler : source.native.handlerFace.rootRead = publicLaw := rfl

abbrev net := Due.Service.network source word ordered.toFinset task (reserved word)

theorem needed (line : Row) : net.need line = 1 := by
  rw [a_row_is_its_original_task line]
  cases line.1.1.val <;> decide +kernel

private theorem allowed (id : Bool) : net.allows (row id) (lot id) = true := by
  apply (Due.Service.network_allows_iff _ _ _ _ _ _ _).mpr
  unfold Due.Service.accepts
  dsimp only
  rw [timed_lot, original_handler]
  cases id <;> decide +kernel

private theorem lot_capacity (id : Bool) : net.capacity (lot id) = 1 := by
  have unreserved : (lot id).1 ∉ reserved word := by simp [reserved]
  change (if (lot id).1 ∈ reserved word then 0 else
    Due.Service.paidAmount source.native.handlerFace.rootRead (Execution.timedAt source word (lot id).1).1
      (lot id).2.val) = 1
  rw [if_neg unreserved, timed_lot, original_handler]
  cases id <;> decide +kernel

private theorem full_row (line : Row) : Network.rowTotal assigned line = net.need line := by
  rw [needed]
  unfold Network.rowTotal assigned
  simp

theorem assignment_covers_the_two_original_services (due : Row → Bool) :
    Allocation.Covers net due assigned := by
  refine ⟨⟨?_, fun line => (full_row line).le, ?_⟩, fun line _ => full_row line⟩
  · intro line receipt
    by_cases chosen : receipt = lot line.1.1.val
    · subst receipt
      rw [a_row_is_its_original_task line]
      have admitted (id : Bool) : 0 ≤ assigned (row id) (lot id) ∧
          (net.allows (row id) (lot id) = false → assigned (row id) (lot id) = 0) := by
        refine ⟨?_, ?_⟩
        · have same : (row id).1.1.val = id := rfl
          simp [assigned, same]
        · rw [allowed]
          intro impossible
          cases impossible
      exact admitted line.1.1.val
    · rw [show assigned line receipt = 0 by simp [assigned, chosen]]
      exact ⟨le_rfl, fun _ => rfl⟩
  · intro receipt
    have different : row false ≠ row true := by
      intro same
      exact Bool.noConfusion (congrArg (fun line : Row => line.1.1.val) same)
    have full : (Finset.univ : Finset Row) = {row false, row true} := by
      ext line
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have belongs := a_row_is_its_original_task line
      cases original : line.1.1.val
      · exact Or.inl (by simpa only [original] using belongs)
      · exact Or.inr (by simpa only [original] using belongs)
    unfold Network.columnTotal
    rw [full, Finset.sum_insert (by simpa only [Finset.mem_singleton] using different), Finset.sum_singleton]
    change (if receipt = lot false then (1 : ℚ) else 0) +
      (if receipt = lot true then 1 else 0) ≤ net.capacity receipt
    by_cases first : receipt = lot false
    · subst receipt
      rw [lot_capacity]
      simp [chosen_lots_are_distinct]
    · by_cases second : receipt = lot true
      · subst receipt
        rw [lot_capacity]
        simp [first]
      · simpa [first, second] using net.capacity_nonnegative receipt

theorem the_original_handoff_has_paid_its_native_settlement :
    Quantities.Settled source word := by
  apply Quantities.settle
  refine ⟨?_, ?_⟩
  · intro cell original
    obtain ⟨person, _, due⟩ := List.mem_flatMap.mp original
    have listed : person ∈ [false,true] := by cases person <;> simp
    have inSource : cell ∈ Material.originalRequirements checkInput opening [false,true] :=
      List.mem_flatMap.mpr ⟨person, listed, due⟩
    have keys : Material.originalRequirements checkInput opening [false,true] =
      [(false,.necessity,true,1), (true,.necessity,true,1)] := by decide +kernel
    rw [keys] at inSource
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inSource
    rw [Demand.delivered_is_from_original_inventory, original_material_inventory, original_handler]
    rcases inSource with rfl | rfl <;> decide +kernel
  · change ¬ Pending (completed source proposal)
    rw [end_is_the_original_renewal_and_its_accounting]
    exact (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain _).1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Actual
