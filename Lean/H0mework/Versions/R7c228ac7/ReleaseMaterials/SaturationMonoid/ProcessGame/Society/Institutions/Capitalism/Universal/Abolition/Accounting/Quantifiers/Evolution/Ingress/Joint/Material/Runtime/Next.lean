import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Answer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private theorem nextVisitEq {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLedgerRootClosure N V} (visit : SourceNativeTemporalVisitAt root)
    {left right : V.Current} (same : left = right)
    (first : (root.toRoot.evolutionAt visit.current).nextCurrent? = some left)
    (second : (root.toRoot.evolutionAt visit.current).nextCurrent? = some right) :
    visit.next first = visit.next second := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

local notation "F" => flow seed claim
local notation "R" => Inquiry.root seed claim

theorem actual_body_visit : (generated seed claim).target.targetVisit = temporalAt seed claim 0 :=
  nextVisitEq (Abolition.Accounting.Root.Compiler.initialVisit F)
    (Abolition.Accounting.Root.Compiler.successor_current F (initial seed))
    (Abolition.Accounting.Root.Compiler.successor F (initial seed)).next_eq
    (Abolition.Accounting.Root.Compiler.nextEq F (initial seed))

theorem source_successor_valid (query : (presentation seed claim).Query) :
    (answerPresentation seed claim 0).erase = (RootInquiryProcessNode.answered (presentation seed claim) query).erase ∧
      (RootInquiryProcessNode.active (presentation seed claim)).PreservesGeneratedLivingLawAt query
        (.active (answerPresentation seed claim 0)) := by
  cases query
  apply RootInquiryProcessNode.active_actualAction_successor_valid
    (presentation seed claim) (answerPresentation seed claim 0) PUnit.unit (generated seed claim)
  · rfl
  · have target := (generated seed claim).target.targetAnswerAndNext_next_eq
    have aligned : (generated seed claim).target.targetAnswerAndNext.nextCurrent =
        ⟨V seed claim,(R).toAuthoritativeRoot,temporalAt seed claim 0⟩ :=
      target.trans (congrArg (fun visit => (⟨V seed claim,(R).toAuthoritativeRoot,visit⟩ :
        SourceNativeAuthoritativeRootCurrentAt (Admission.N seed claim))) (actual_body_visit seed claim))
    exact (congrArg (fun current => (⟨Admission.N seed claim,current⟩ : AnyAuthoritativeRootCurrent)) aligned).symm
  · exact HEq.rfl

theorem next_is_the_same_complete_root (n : Nat) :
    (answerPresentation seed claim (n + 1)).erase =
      (⟨Admission.N seed claim,(R).generatedNextCurrentAt (temporalAt seed claim n)⟩ : AnyAuthoritativeRootCurrent) := by
  rw [Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor R (temporalAt seed claim n)
    (Abolition.Accounting.Root.Compiler.successor F (visitAt seed claim n).current)]
  exact congrArg (fun visit => (⟨Admission.N seed claim,⟨V seed claim,(R).toAuthoritativeRoot,visit⟩⟩ : AnyAuthoritativeRootCurrent))
    (nextVisitEq (temporalAt seed claim n) (Abolition.Accounting.Root.Compiler.successor_current F (visitAt seed claim n).current).symm
      (Abolition.Accounting.Root.Compiler.nextEq F _) (Abolition.Accounting.Root.Compiler.successor F _).next_eq)

theorem successor_valid (n : Nat) (query : (answerPresentation seed claim n).Query) :
    (answerPresentation seed claim (n + 1)).erase =
        (RootInquiryProcessNode.answered (answerPresentation seed claim n) query).erase ∧
      (RootInquiryProcessNode.active (answerPresentation seed claim n)).PreservesGeneratedLivingLawAt query
        (.active (answerPresentation seed claim (n + 1))) := by
  cases query
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (answerPresentation seed claim n) (answerPresentation seed claim (n + 1)) PUnit.unit
    (answerFace seed claim (temporalAt seed claim n)) (consumer seed claim (temporalAt seed claim n))
  · rfl
  · exact next_is_the_same_complete_root seed claim n
  · exact HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
