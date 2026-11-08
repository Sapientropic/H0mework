import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyExecution
open Institutions.Capitalism.Universal.Source.Program
open Repayment.Recovery (Good)
open WholePartyLift

theorem paidStep (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.paidStep (current old outside) (request action) = current (oldLaw.paidStep old action) outside := by
  apply RawCurrent.ext
  · funext actor good
    simp only [RawLaw.paidStep]
    rw [debit,credit]
    cases actor with
    | inl actor => simp only [flowAt_inl,current]
    | inr actor => cases actor;simp only [flowAt_outside,current,sub_zero,add_zero]
  · funext instrument debtor creditor
    rcases action with ⟨signer,consents,purpose,gates,op⟩
    cases op <;> cases debtor <;> cases creditor <;>
      simp [RawLaw.paidStep,RawLaw.nextClaims,request,operation,current]
  · rcases action with ⟨signer,consents,purpose,gates,op⟩
    cases op <;> rfl
  · rfl
  · rfl

theorem step (old : OldCurrent) (outside : Good → ℚ) (action : OldAction) :
    newLaw.step (current old outside) (request action) = current (oldLaw.step old action) outside := by
  by_cases legal : oldLaw.Valid old action
  · rw [RawLaw.step,if_pos ((valid old outside action).mpr legal),RawLaw.step,if_pos legal,paidStep]
  · rw [RawLaw.step,if_neg (fun allowed => legal ((valid old outside action).mp allowed)),RawLaw.step,if_neg legal]

def item (outside : Good → ℚ) (old : ExecutionItem OldParty Good OldPort OldState Unit) :
    ExecutionItem WholeCursorLaw.Party Good WholeCursorLaw.Port NewState Unit :=
  ⟨old.index,current old.before outside,request old.request⟩

theorem execute (old : OldCurrent) (outside : Good → ℚ) (index : Nat) (word : List OldAction) :
    newLaw.execute (current old outside) index (word.map request) =
      ⟨current (oldLaw.execute old index word).final outside,(oldLaw.execute old index word).items.map (item outside)⟩ := by
  induction word generalizing old index with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,RawLaw.execute,step,ih,item]

theorem next (old : OldCurrent) (outside : Good → ℚ) (word : List OldAction) :
    newLaw.next (current old outside) (word.map request) = current (oldLaw.next old word) outside := by
  unfold RawLaw.next
  rw [execute]
  rfl

-- Invalid instructions retain their original position and before-state in the mapped trace.
theorem every_item_keeps_its_admission_and_refusal (old : OldCurrent) (outside : Good → ℚ)
    (index : Nat) (word : List OldAction) :
    ∀ entry ∈ (oldLaw.execute old index word).items,
      item outside entry ∈ (newLaw.execute (current old outside) index (word.map request)).items ∧
        (newLaw.Valid (item outside entry).before (item outside entry).request ↔ oldLaw.Valid entry.before entry.request) := by
  intro entry member
  rw [execute]
  exact ⟨List.mem_map.mpr ⟨entry,member,rfl⟩,valid entry.before outside entry.request⟩

theorem original_claims_and_external_reserve (old : OldCurrent) (outside : Good → ℚ) (word : List OldAction) :
    (∀ instrument debtor creditor,
      (newLaw.next (current old outside) (word.map request)).claims instrument (.inl debtor) (.inl creditor) =
        (oldLaw.next old word).claims instrument debtor creditor) ∧
      (∀ good, (newLaw.next (current old outside) (word.map request)).stock (.inr ()) good = outside good) := by
  rw [next]
  exact ⟨fun _ _ _ => rfl,fun _ => rfl⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholePartyExecution
