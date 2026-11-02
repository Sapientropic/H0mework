import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw
open Source.Program
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- The same operation partition as productive-loss accounting, expressed
at the raw occurrence boundary rather than a trial/response wrapper. -/
def productiveAt (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) : ℚ :=
  match item.request.operation with
  | .produce _ => flowAt (law.actualCredit item.before item.request) party good -
      flowAt (law.actualDebit item.before item.request) party good
  | .use .. | .revise .. => -flowAt (law.actualDebit item.before item.request) party good
  | _ => 0

def productiveNetFor (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (party : Party) (good : Good) :=
  (items.map fun item => productiveAt law item party good).sum

def flowKeys (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :=
  items.flatMap fun item => (law.actualDebit item.before item.request ++ law.actualCredit item.before item.request).map Prod.fst

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
private theorem outside_productive_flow_keys_has_zero_productive_net
    (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (party : Party) (good : Good)
    (outside : (party,good) ∉ flowKeys law items) : productiveNetFor law items party good = 0 := by
  unfold productiveNetFor
  apply List.sum_eq_zero
  intro value member
  obtain ⟨item,original,rfl⟩ := List.mem_map.mp member
  have excludes : (party,good) ∉ (law.actualDebit item.before item.request ++ law.actualCredit item.before item.request).map Prod.fst := by
    intro present
    exact outside (List.mem_flatMap.mpr ⟨item,original,present⟩)
  have debitZero := outside_flow_zero (law.actualDebit item.before item.request) party good
    (fun present => excludes (by simpa only [List.map_append,List.mem_append] using Or.inl present))
  have creditZero := outside_flow_zero (law.actualCredit item.before item.request) party good
    (fun present => excludes (by simpa only [List.map_append,List.mem_append] using Or.inr present))
  cases operation : item.request.operation <;> simp [productiveAt,operation,debitZero,creditZero]

/-- An occurred input, with no loss amount, victim list or repaired endpoint. -/
structure Occurrence (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  law : RawLaw Party Good Port Technology Instrument
  before : RawCurrent Party Good Technology Instrument
  word : RawEvent Party Good Port Technology Instrument

variable (original : Occurrence Party Good Port Technology Instrument)

def items := original.law.rawItems original.before original.word
def openedLaw := PublicFunction.physicalLaw original.law
def openedItems := (openedLaw original).rawItems original.before original.word
def permissionLaw := { original.law with allowed := fun _ _ _ => true }

def net (law : RawLaw Party Good Port Technology Instrument) (party : Party) (good : Good) :=
  productiveNetFor law (law.rawItems original.before original.word) party good
def permissionLoss (party : Party) (good : Good) :=
  net original (permissionLaw original) party good - net original original.law party good
def policyLoss (party : Party) (good : Good) :=
  net original (openedLaw original) party good - net original (permissionLaw original) party good
def loss (party : Party) (good : Good) :=
  productiveNetFor (openedLaw original) (openedItems original) party good -
    productiveNetFor original.law (items original) party good
def quantity (key : Party × Good) := max 0 (loss original key.1 key.2)
def scope : List (Party × Good) :=
  (flowKeys original.law (items original) ++ flowKeys (openedLaw original) (openedItems original)).dedup
def positiveScope := (scope original).filter fun key => decide (0 < loss original key.1 key.2)

theorem the_loss_keeps_permission_and_policy_separate (party : Party) (good : Good) :
    loss original party good = permissionLoss original party good + policyLoss original party good := by
  unfold loss permissionLoss policyLoss net items openedItems
  ring

theorem every_positive_original_cell_is_generated (party : Party) (good : Good)
    (positive : 0 < loss original party good) : (party,good) ∈ positiveScope original := by
  apply List.mem_filter.mpr
  refine ⟨?_,decide_eq_true positive⟩
  by_contra outside
  have oldOutside : (party,good) ∉ flowKeys original.law (items original) :=
    fun member => outside (List.mem_dedup.mpr (List.mem_append_left _ member))
  have newOutside : (party,good) ∉ flowKeys (openedLaw original) (openedItems original) :=
    fun member => outside (List.mem_dedup.mpr (List.mem_append_right _ member))
  have oldZero := outside_productive_flow_keys_has_zero_productive_net _ _ _ _ oldOutside
  have newZero := outside_productive_flow_keys_has_zero_productive_net _ _ _ _ newOutside
  unfold loss at positive
  rw [oldZero,newZero,sub_self] at positive
  exact (lt_irrefl 0 positive)

theorem no_unlisted_cell_has_a_positive_quantity (key : Party × Good)
    (outside : key ∉ positiveScope original) : quantity original key = 0 := by
  apply max_eq_left
  apply le_of_not_gt
  exact fun positive => outside (every_positive_original_cell_is_generated original _ _ positive)

structure Gate where
  item : { item // item ∈ items original }
  port : { port // port ∈ original.law.requiredPorts item.val.before item.val.request }
  withheld : original.law.allowed item.val.before.technology port.val item.val.request.signer = false ∧
    original.law.controller item.val.before.technology port.val ∉ item.val.request.consents

def Gate.controller (gate : Gate original) :=
  original.law.controller gate.item.val.before.technology gate.port.val

def gates : List (Gate original) :=
  (items original).attach.flatMap fun item =>
    (original.law.requiredPorts item.val.before item.val.request).attach.filterMap fun port =>
      if withheld : original.law.allowed item.val.before.technology port.val item.val.request.signer = false ∧
          original.law.controller item.val.before.technology port.val ∉ item.val.request.consents then
        some ⟨item,port,withheld⟩ else none
def cohort := ((gates original).map (Gate.controller original)).dedup

theorem Gate.original_request_is_refused (gate : Gate original) :
    ¬ original.law.Valid gate.item.val.before gate.item.val.request := by
  intro accepted
  rcases accepted.2.1 gate.port.val gate.port.property with allowed | consent
  · exact Bool.noConfusion (gate.withheld.1.symm.trans allowed)
  · exact gate.withheld.2 consent

theorem every_controller_has_its_original_refused_site (party : Party) (member : party ∈ cohort original) :
    ∃ gate ∈ gates original, gate.controller original = party ∧
      gate.item.val ∈ original.law.rawItems original.before original.word ∧
      ¬ original.law.Valid gate.item.val.before gate.item.val.request := by
  obtain ⟨gate,inside,same⟩ := List.mem_map.mp (List.mem_dedup.mp member)
  exact ⟨gate,inside,same,gate.item.property,gate.original_request_is_refused original⟩

theorem every_generated_matrix_address_is_unique : (positiveScope original).Nodup :=
  (List.nodup_dedup _).filter _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw
