import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

theorem admitted_items_of_original_trace {source target : C} {word : Word}
    (actual : Trace source word target) (index : Nat) :
    ∀ item ∈ ((Physical.Public.interpreter source.native.input).execute source.raw index word).items,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request := by
  induction actual generalizing index with
  | nil => simp [RawLaw.execute]
  | cons source request tail target ready review noConsents valid later ih =>
      simp only [RawLaw.execute, List.forall_mem_cons]
      refine ⟨valid, ?_⟩
      have laterPaid := ih (index + 1)
      rw [afterNative_keeps_the_same_original_input source request,
        (two_actual_root_steps_pay_and_consume_the_generated_primitive source request ready review noConsents valid).2] at laterPaid
      exact laterPaid

theorem every_original_request_has_its_paid_native_inventory_item
    {source target : C} {word : Word} (actual : Trace source word target)
    (request : Request Party Good Port Technology Instrument) (listed : request ∈ word) :
    ∃ item ∈ inventory source (primitiveScript word),
      item.request = request ∧ (Physical.Public.interpreter source.native.input).Valid item.before item.request := by
  let law := Physical.Public.interpreter source.native.input
  have original : request ∈ ((law.execute source.raw 0 word).items.map ExecutionItem.request) := by
    rw [RawLaw.inventory_requests_exact]
    exact listed
  obtain ⟨item, inside, same⟩ := List.mem_map.mp original
  refine ⟨{item with index := 0}, ?_, same, admitted_items_of_original_trace actual 0 item inside⟩
  rw [primitive_inventory actual 0]
  exact List.mem_map.mpr ⟨item, inside, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
