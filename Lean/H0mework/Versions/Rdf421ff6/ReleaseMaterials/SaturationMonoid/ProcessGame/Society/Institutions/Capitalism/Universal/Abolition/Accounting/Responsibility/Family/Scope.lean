import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Assessment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family

open Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def flowKeys (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) : List (Party × Good) :=
  items.flatMap fun item =>
    (law.actualDebit item.before item.request ++ law.actualCredit item.before item.request).map Prod.fst

omit [DecidableEq Instrument] in
private theorem key_is_present (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument))
    (item : ExecutionItem Party Good Port Technology Instrument) (member : item ∈ items)
    (entry : (Party × Good) × ℚ)
    (inside : entry ∈ law.actualDebit item.before item.request ++ law.actualCredit item.before item.request) :
    entry.1 ∈ flowKeys law items :=
  List.mem_flatMap.mpr ⟨item,member,List.mem_map.mpr ⟨entry,inside,rfl⟩⟩

omit [DecidableEq Instrument] in
private theorem outside_flow_zero (flow : Flow Party Good) (party : Party) (good : Good)
    (outside : (party,good) ∉ flow.map Prod.fst) : flowAt flow party good = 0 := by
  unfold flowAt amount
  apply List.sum_eq_zero
  intro value member
  obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
  have different : entry.1 ≠ (party,good) := by
    intro same
    exact outside (same ▸ List.mem_map.mpr ⟨entry,inside,rfl⟩)
  simp only [if_neg different]

omit [DecidableEq Instrument] in
theorem outside_productive_flow_keys_has_zero_productive_net
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (party : Party) (good : Good)
    (outside : (party,good) ∉ flowKeys law items) : productiveNetFor law items party good = 0 := by
  unfold productiveNetFor
  apply List.sum_eq_zero
  intro value member
  obtain ⟨item,original,rfl⟩ := List.mem_map.mp member
  have debitZero : flowAt (law.actualDebit item.before item.request) party good = 0 := by
    apply outside_flow_zero
    intro present
    obtain ⟨entry,inside,same⟩ := List.mem_map.mp present
    exact outside (same ▸ key_is_present law items item original entry (List.mem_append_left _ inside))
  have creditZero : flowAt (law.actualCredit item.before item.request) party good = 0 := by
    apply outside_flow_zero
    intro present
    obtain ⟨entry,inside,same⟩ := List.mem_map.mp present
    exact outside (same ▸ key_is_present law items item original entry (List.mem_append_right _ inside))
  cases operation : item.request.operation <;> simp [productiveNetAt,operation,debitZero,creditZero]

variable (source : Trials.Mechanism Party Good Port Technology Instrument)
  (past : List (RawEvent Party Good Port Technology Instrument)) (nature : source.Nature)
  (response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- This finite scope is generated from both actual material inventories,
including all debit bearers; no externally selected victim roster is supplied. -/
def scope : List (Party × Good) :=
  (flowKeys source.code.law (Control.responseExecution source past nature response).items ++
    flowKeys (Control.openedProgramme source).code.law
      (Control.responseExecution (Control.openedProgramme source) past nature response).items).dedup

def positiveScope : List (Party × Good) :=
  (scope source past nature response).filter fun key =>
    decide (0 < partyLoss source past nature response key.1 key.2)

def quantity (key : Party × Good) : ℚ := max 0 (partyLoss source past nature response key.1 key.2)

theorem every_positive_original_harm_is_in_the_generated_scope (party : Party) (good : Good)
    (positive : 0 < partyLoss source past nature response party good) :
    (party,good) ∈ positiveScope source past nature response := by
  apply List.mem_filter.mpr
  refine ⟨?_,decide_eq_true positive⟩
  · by_contra outside
    have separate : (party,good) ∉
        flowKeys source.code.law (Control.responseExecution source past nature response).items ++
          flowKeys (Control.openedProgramme source).code.law
            (Control.responseExecution (Control.openedProgramme source) past nature response).items :=
      fun member => outside (List.mem_dedup.mpr member)
    have oldZero := outside_productive_flow_keys_has_zero_productive_net source.code.law
      (Control.responseExecution source past nature response).items party good
      (fun member => separate (List.mem_append_left _ member))
    have newZero := outside_productive_flow_keys_has_zero_productive_net
      (Control.openedProgramme source).code.law
      (Control.responseExecution (Control.openedProgramme source) past nature response).items party good
      (fun member => separate (List.mem_append_right _ member))
    unfold partyLoss at positive
    rw [oldZero,newZero,sub_self] at positive
    exact (lt_irrefl 0 positive)

structure Claim : Type where
  private mk ::
  nonempty : positiveScope source past nature response ≠ []

def assess : Option (Claim source past nature response) :=
  if positive : positiveScope source past nature response ≠ [] then some ⟨positive⟩ else none

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family
