import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Positivity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Micro

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem primitive_settlement_has_zero_resource_cost
    (request : Request Party Good Port Technology Instrument)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (settlement : request.operation = .settle instrument debtor holder quantity)
    (channel : Channel) (party : Party) (good : Good) :
    resource input before [.primitive request] channel party good = 0 := by
  unfold resource Programme.items
  cases compiled : Physical.Public.compile input before (.primitive request) with
  | accepted word selected checked =>
      have sourceWord : word = [request.resign request.signer] := (Option.some.inj selected).symm
      cases sourceWord
      simp [Programme.items,Physical.Public.ResultAt.execution,RawLaw.execute,actualPart,part,Request.resign,settlement,flowAt,amount]
  | refused word selected item listed failed =>
      simp [Programme.items,Physical.Public.ResultAt.execution]
  | metadata selected => simp [Programme.items,Physical.Public.ResultAt.execution]

theorem source_settlement_inventories_have_no_hidden_resource_debit
    (word : RawEvent Party Good Port Technology Instrument)
    (settlements : ∀ request ∈ word, ∃ instrument debtor holder quantity,
      request.operation = .settle instrument debtor holder quantity)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (listed : item ∈ Programme.items input before (word.map Compile.RawInput.primitive))
    (channel : Channel) : actualPart (Physical.Public.interpreter input) item.before item.request channel = [] := by
  obtain ⟨request,member,same⟩ := Programme.every_microprogramme_item_retains_its_source_instruction input before word item listed
  obtain ⟨instrument,debtor,holder,quantity,settlement⟩ := settlements request member
  apply a_settlement_does_not_destroy_real_resources _ _ _ _ instrument debtor holder quantity
  simpa only [same,Request.resign] using settlement

theorem all_source_settlement_programmes_have_zero_resource_cost
    (word : RawEvent Party Good Port Technology Instrument)
    (settlements : ∀ request ∈ word, ∃ instrument debtor holder quantity,
      request.operation = .settle instrument debtor holder quantity)
    (channel : Channel) (party : Party) (good : Good) :
    resource input before (word.map Compile.RawInput.primitive) channel party good = 0 := by
  induction word generalizing before with
  | nil => rfl
  | cons request tail prior =>
      obtain ⟨instrument,debtor,holder,quantity,kind⟩ := settlements request (by simp)
      change resource input before ([.primitive request] ++ tail.map Compile.RawInput.primitive) channel party good = 0
      rw [resource_append,primitive_settlement_has_zero_resource_cost input before request instrument debtor holder quantity kind]
      rw [prior _ (fun request listed => settlements request (List.mem_cons_of_mem _ listed)),zero_add]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost
