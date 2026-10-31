import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.SourceRank
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Loop

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

local notation "items" => Public.Accounting.items input depth count prefixLimit renewalLimit oldPast start
local notation "step" => Public.Accounting.next input depth count prefixLimit renewalLimit oldPast start
def consume (state : (Epoch.Finance.process input depth count).GeneratedState)
    (item : Epoch.Finance.ActualItem input depth count) :=
  (Epoch.Finance.consume input depth count item state).next input depth count

/-- A normalization of the existing source loop, not a replacement scheduler. -/
theorem suffix_is_consumed_in_its_original_order
    (noIssue : ∀ item ∈ items, Epoch.Finance.readNewClaim input depth count item = none)
    (todo : List (Epoch.Finance.ActualItem input depth count))
    (current : Public.Accounting.Current input depth count anchor)
    (paid : current.bodyPaid = true) (suffix : (items).drop current.position = todo) :
    ((step^[todo.length]) current).account = todo.foldl (consume input depth count) current.account ∧
      ((step^[todo.length]) current).position = current.position + todo.length ∧
      ((step^[todo.length]) current).bodyPaid = true := by
  induction todo generalizing current with
  | nil => exact ⟨rfl,by simp,paid⟩
  | cons item rest later =>
      have present : Public.Accounting.item? input depth count prefixLimit renewalLimit oldPast start current = some item := by
        simp only [Public.Accounting.item?,paid,if_true]
        rw [← List.head?_drop,suffix]
        rfl
      have member : item ∈ items :=
        List.mem_of_getElem? (by simpa only [Public.Accounting.item?,paid,if_true] using present)
      have actualStep : step current = current.afterItem paid item := by
        rw [Public.Accounting.next,dif_pos paid,present]
        dsimp only
        rw [noIssue item member]
      have actual := Public.Accounting.Current.after_item_reads_the_source_generated_native_account current paid item
      have restSuffix : (items).drop (step current).position = rest := by
        rw [actualStep,actual.2.1,List.drop_add_one_eq_tail_drop,suffix]
        rfl
      have account := (congrArg Public.Accounting.Current.account actualStep).trans actual.1
      have nextPaid := (congrArg Public.Accounting.Current.bodyPaid actualStep).trans actual.2.2
      have result := later (step current) nextPaid restSuffix
      rw [List.length_cons,Function.iterate_succ_apply]
      refine ⟨?_,?_,result.2.2⟩
      · exact result.1.trans (congrArg (List.foldl (consume input depth count) · rest) account)
      · rw [result.2.1,actualStep,actual.2.1]
        omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Loop
