import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Consume
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.Prefix
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_actual_material_and_financial_tail_retires_its_original_native_slot
    (tag : Epoch.Interface.Tag input depth count) (visit : Epoch.Interface.Visit input depth count tag)
    (before : (Epoch.Finance.process input depth count).GeneratedState)
    (obligation : AdmittedObligation (Epoch.Finance.vocabulary input depth count))
    (single : before.current.slots = [.live obligation])
    (front : RawEvent Party Good Port Technology Instrument) (request : Request Party Good Port Technology Instrument)
    (holder : Party) (quantity : ℚ)
    (operation : request.operation = .settle (obligation.content.instrument input depth count)
      (obligation.content.debtor input depth count) holder quantity)
    (original : (Epoch.Finance.inventory input depth count tag visit).map
      (fun item => (item.instruction input depth count).request) = front ++ [request])
    (material : ∀ request ∈ front, Responsibility.NonFinancialOperation request.operation)
    (accepted : ∀ item ∈ Epoch.Finance.inventory input depth count tag visit,
      (item.interpreter input depth count).Valid (item.instruction input depth count).before
        (item.instruction input depth count).request)
    (balance : obligation.residual = Finsupp.single holder quantity) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary input depth count),
      (Epoch.Finance.consumeVisit input depth count tag visit before).current.slots = [.terminal archive] ∧
      archive.obligation = obligation ∧
      before.current.history <+: (Epoch.Finance.consumeVisit input depth count tag visit before).current.history := by
  obtain ⟨last,member,same,tail⟩ := the_original_material_prefix_reaches_its_same_actual_financial_tail
    input depth count front request _ original material before
  obtain ⟨archive,terminal,identity,history⟩ := the_actual_matching_full_payment_retires_its_original_native_slot
    input depth count before obligation single last holder quantity
      ((congrArg Request.operation same).trans operation) (accepted last member) balance
  have exactNext := (Drain.the_original_financial_consumption_is_its_same_ordered_fold input depth count tag visit before).trans tail
  rw [exactNext]
  exact ⟨archive,terminal,identity,history⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
