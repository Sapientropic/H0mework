import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Reparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem an_original_nonfinancial_item_keeps_the_literal_native_account
    (item : Epoch.Finance.ActualItem input depth count)
    (material : Responsibility.NonFinancialOperation (item.instruction input depth count).request.operation)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    (Epoch.Finance.consume input depth count item before).next input depth count = before := by
  have noClaim : Epoch.Finance.readNewClaim input depth count item = none := by
    cases operation : (item.instruction input depth count).request.operation <;>
      simp_all [Epoch.Finance.readNewClaim,Responsibility.NonFinancialOperation]
  have noMovement : Epoch.Finance.readMovement input depth count item = none := by
    unfold Epoch.Finance.readMovement
    split
    · split <;> simp_all [Responsibility.NonFinancialOperation]
    · rfl
  unfold Epoch.Finance.consume
  split
  · rfl
  · split
    · rename_i fresh generated
      cases noClaim.symm.trans generated
    · rw [noMovement]
      rfl

theorem the_original_material_prefix_reaches_its_same_actual_financial_tail
    (front : RawEvent Party Good Port Technology Instrument)
    (settlement : Request Party Good Port Technology Instrument)
    (items : List (Epoch.Finance.ActualItem input depth count))
    (original : items.map (fun item => (item.instruction input depth count).request) = front ++ [settlement])
    (material : ∀ request ∈ front, Responsibility.NonFinancialOperation request.operation)
    (before : (Epoch.Finance.process input depth count).GeneratedState) :
    ∃ last ∈ items, (last.instruction input depth count).request = settlement ∧
      items.foldl (fun state item => (Epoch.Finance.consume input depth count item state).next input depth count) before =
        (Epoch.Finance.consume input depth count last before).next input depth count := by
  induction front generalizing items with
  | nil =>
      cases items with
      | nil => cases original
      | cons item rest =>
          have exactWord := List.cons.inj original
          have empty : rest = [] := List.map_eq_nil_iff.mp exactWord.2
          subst rest
          exact ⟨item,List.mem_cons_self,exactWord.1,rfl⟩
  | cons request rest later =>
      cases items with
      | nil => cases original
      | cons item remaining =>
          have exactWord := List.cons.inj original
          have actualMaterial : Responsibility.NonFinancialOperation
              (item.instruction input depth count).request.operation := by
            have same : (item.instruction input depth count).request = request := exactWord.1
            rw [same]
            exact material request List.mem_cons_self
          have actual := an_original_nonfinancial_item_keeps_the_literal_native_account input depth count item
            actualMaterial before
          obtain ⟨last,member,same,tail⟩ := later remaining exactWord.2
            (fun next member => material next (List.mem_cons_of_mem request member))
          refine ⟨last,List.mem_cons_of_mem item member,same,?_⟩
          simpa only [List.foldl_cons,actual] using tail

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
