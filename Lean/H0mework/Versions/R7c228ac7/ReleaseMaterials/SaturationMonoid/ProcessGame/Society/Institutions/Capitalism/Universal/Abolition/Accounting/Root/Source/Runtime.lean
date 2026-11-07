import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Row

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

private theorem next_visit_eq {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLedgerRootClosure N V} (visit : SourceNativeTemporalVisitAt root)
    {left right : V.Current} (same : left = right)
    (first : (root.toRoot.evolutionAt visit.current).nextCurrent? = some left)
    (second : (root.toRoot.evolutionAt visit.current).nextCurrent? = some right) :
    visit.next first = visit.next second := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (word : RawEvent Party Good Port Technology Instrument)

local notation "F" => Source.flow input frame visit claim word
local notation "fullRoot" => root input frame visit claim word

def visitAt : Nat → RootVisit (fullRoot).toAuthoritativeRoot.toRoot
  | 0 => (fullRoot).toAuthoritativeRoot.toRoot.initialVisit.next (Compiler.nextEq F .pending)
  | n + 1 => (visitAt n).next (Compiler.nextEq F (visitAt n).current)

def temporalAt (n : Nat) : SourceNativeTemporalVisitAt (fullRoot).toAuthoritativeRoot.toLedgerRoot :=
  .finite (visitAt input frame visit claim word n)

def authorityAt : (n : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt (fullRoot)
    (temporalAt input frame visit claim word n)
    (entry input frame claim (Source.support input frame visit claim word (visitAt input frame visit claim word n).current))
  | 0 => nextAuthority input frame visit claim word (initialVisit input frame visit claim word)
      (initialAuthority input frame visit claim word)
  | n + 1 => nextAuthority input frame visit claim word (temporalAt input frame visit claim word n) (authorityAt n)

def presentationAt (n : Nat) : RootInquiryStatePresentation :=
  presentation input frame visit claim word (temporalAt input frame visit claim word n) (authorityAt input frame visit claim word n)

theorem next_is_the_same_complete_root_update (n : Nat) :
    (presentationAt input frame visit claim word (n + 1)).erase =
      (⟨Source.N input frame claim,(fullRoot).generatedNextCurrentAt (temporalAt input frame visit claim word n)⟩ :
        AnyAuthoritativeRootCurrent) := by
  rw [Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor (fullRoot)
    (temporalAt input frame visit claim word n) (Compiler.successor F (visitAt input frame visit claim word n).current)]
  exact congrArg (fun targetVisit =>
    (⟨Source.N input frame claim,⟨Source.V input frame visit claim word,(fullRoot).toAuthoritativeRoot,targetVisit⟩⟩ :
      AnyAuthoritativeRootCurrent))
    (next_visit_eq (temporalAt input frame visit claim word n)
      (Compiler.successor_current F (visitAt input frame visit claim word n).current).symm
      (Compiler.nextEq F _) (Compiler.successor F _).next_eq)

theorem successor_valid (n : Nat) (query : (presentationAt input frame visit claim word n).Query) :
    (presentationAt input frame visit claim word (n + 1)).erase =
        (RootInquiryProcessNode.answered (presentationAt input frame visit claim word n) query).erase ∧
      (RootInquiryProcessNode.active (presentationAt input frame visit claim word n)).PreservesGeneratedLivingLawAt query
        (.active (presentationAt input frame visit claim word (n + 1))) := by
  cases query
  apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (presentationAt input frame visit claim word n) (presentationAt input frame visit claim word (n + 1)) PUnit.unit
    (answerFace input frame visit claim word (temporalAt input frame visit claim word n))
    (consumer input frame visit claim word (temporalAt input frame visit claim word n))
  · rfl
  · exact next_is_the_same_complete_root_update input frame visit claim word n
  · exact HEq.rfl

def depth (current : AnyAuthoritativeRootCurrent) : Nat := match current.current.visit.history with
  | .finite history => ProductiveFiniteRootHistoryAt.causalDepth history
  | .postCofinal _ => 0

theorem presentation_depth (n : Nat) : depth (presentationAt input frame visit claim word n).erase = n + 1 := by
  change ProductiveFiniteRootHistoryAt.causalDepth (visitAt input frame visit claim word n).history = n + 1
  induction n with
  | zero => rfl
  | succ n previous => exact congrArg Nat.succ previous

theorem presentation_erase_injective : Function.Injective (fun n => (presentationAt input frame visit claim word n).erase) := by
  intro first second same
  have equalDepth := congrArg depth same
  rw [presentation_depth,presentation_depth] at equalDepth
  exact Nat.add_right_cancel equalDepth

#print axioms successor_valid
#print axioms presentation_erase_injective

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry
