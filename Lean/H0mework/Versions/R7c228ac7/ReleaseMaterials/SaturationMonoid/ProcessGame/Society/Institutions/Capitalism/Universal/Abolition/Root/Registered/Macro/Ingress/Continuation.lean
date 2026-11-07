import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Compilation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

def nextEntry := (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
  (firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).next_eq
  ((initialLedger (review := review) input depth sourceStart datum prefixLimit renewalLimit).forward
    (Continuation.sourceEntry input (frame input depth sourceStart)))

/-- Authority follows the actual action's own initial row through its exact
first successor, retaining the complete living law. -/
def nextAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
    (nextVisit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)
    (nextEntry (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) :=
  (generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).target.initialAuthority.next
    (firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).next_eq

abbrev selectedCursor := Mandatory.executionCursor (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
  Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit)

abbrev sourceResult := (reportAt (review := review) input depth sourceStart datum prefixLimit renewalLimit
  ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current)).2

variable
  (reason : Compile.RefusalAt input depth (cut input depth sourceStart) prefixLimit renewalLimit
    (Actual.initial input depth (cut input depth sourceStart))
    (Mandatory.executionRaw (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit)))
  (refused : sourceResult (review := review) input depth sourceStart datum prefixLimit renewalLimit = .refused reason)

include reason refused

private theorem refusalFlag : Physical.materialWrite input depth (cut input depth sourceStart) prefixLimit renewalLimit
    (selectedCursor (review := review) input depth sourceStart datum prefixLimit renewalLimit) = false := by
  change Physical.resultAt input depth (cut input depth sourceStart) prefixLimit renewalLimit
    (selectedCursor (review := review) input depth sourceStart datum prefixLimit renewalLimit) = .refused reason at refused
  unfold Physical.materialWrite
  split <;> first | rfl | rw [refused]; rfl

theorem source_refusal_compiles_as_continued_transport :
    ∃ transport : (Accounting.V (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0).ContinuedTransportAt
        (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit),
      (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toRoot.evolutionAt
        (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit) = .continuedTransport transport := by
  have noWrite := refusalFlag (review := review) input depth sourceStart datum prefixLimit renewalLimit reason refused
  refine ⟨⟨noWrite⟩, ?_⟩
  change (Accounting.source (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
    depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0).toRootSource.actual.compile
      (Accounting.emitted (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
        depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
        (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit)) = _
  rw [Accounting.source_choice (review := review)]
  have notWrite : ¬ Accounting.writes (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit) = true := by
    change ¬ Physical.materialWrite input depth (cut input depth sourceStart) prefixLimit renewalLimit
      (selectedCursor (review := review) input depth sourceStart datum prefixLimit renewalLimit) = true
    rw [noWrite]
    exact Bool.false_ne_true
  rw [dif_neg notWrite]
  rfl

theorem source_refusal_preserves_the_complete_physical_current :
    Accounting.physical (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (nextVisit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current =
    Accounting.physical (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
      depth (cut input depth sourceStart) Physical.initial (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0
      (bodyInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit) := by
  rw [next_visit_is_the_original_body_target (review := review)]
  exact Physical.refusal_keeps_the_original_physical_current input depth (cut input depth sourceStart) prefixLimit renewalLimit
    (selectedCursor (review := review) input depth sourceStart datum prefixLimit renewalLimit) reason refused

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.nextAuthority
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.source_refusal_compiles_as_continued_transport
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.source_refusal_preserves_the_complete_physical_current
