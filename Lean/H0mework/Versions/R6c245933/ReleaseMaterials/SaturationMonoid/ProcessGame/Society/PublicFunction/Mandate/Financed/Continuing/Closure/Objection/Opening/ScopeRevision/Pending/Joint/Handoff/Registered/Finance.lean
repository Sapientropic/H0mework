import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
local notation "sources" => Pending.Joint.Finance.sources

structure FinancingData where
  private mk ::
  first : ResponsibilityState (Financial.Family.vocabulary sources)
  last : ResponsibilityState (Financial.Family.vocabulary sources)
  native : (Financial.Family.process sources).Run first last
  opening : Financial.Family.Migration.FinancingBook.Book sources first
  result : Financial.Family.Migration.FinancingBook.Flow sources native opening

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (word : List Action)


def financingData : FinancingData :=
  ⟨(before authority inventory).current,(after authority inventory fresh word).current,
    run authority inventory fresh word,book authority inventory,funded authority inventory fresh word⟩

structure Receipt where
  private mk ::
  native : Registered.Receipt authority inventory fresh word
  actualVisits : List Visit
  financing : FinancingData
  amounts : Bool → Bool → Good → ℚ

def produce : Receipt authority inventory fresh word :=
  ⟨Registered.produce authority inventory fresh word,entries authority inventory fresh word,
    financingData authority inventory fresh word,account authority inventory fresh word⟩

theorem produced_data_is_the_same_complete_original_source :
    (produce authority inventory fresh word).native = Registered.produce authority inventory fresh word ∧
    (produce authority inventory fresh word).actualVisits = entries authority inventory fresh word ∧
    (produce authority inventory fresh word).financing = financingData authority inventory fresh word ∧
    (produce authority inventory fresh word).amounts = account authority inventory fresh word := ⟨rfl,rfl,rfl,rfl⟩

theorem every_selected_original_item_has_actual_funding_or_control_provenance
    (receipt : Visit) (_visited : receipt ∈ (produce authority inventory fresh word).actualVisits)
    (item : Item) (_inside : item ∈ raw receipt) (marked : selected receipt item.index = true) :
    Financial.Family.Migration.Funding.Cash.selected sources receipt item.index = true ∨
      Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence.selected
        (sources receipt.sourceIndex).law (origin receipt).1 (origin receipt).2 item.index = true :=
  Bool.or_eq_true_iff.mp marked

theorem produced_accounts_are_the_exact_original_net (actor : Bool) (good : Good) :
    (produce authority inventory fresh word).amounts true actor good +
      (produce authority inventory fresh word).amounts false actor good =
    quotedBefore authority inventory fresh word actor good - quotedAfter authority inventory fresh word actor good :=
  the_union_cash_and_complete_native_charge_are_exactly_the_original_net_change authority inventory fresh word actor good

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance
