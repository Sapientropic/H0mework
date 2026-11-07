import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

/-- Read the next from the root's own generated branch. This covers both a
physical write and a continued rejection without selecting another target. -/
theorem next_is_the_same_generated_successor
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted visit.current)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current)) :
    root.generatedNextCurrentAt visit =
      ⟨V, root.toAuthoritativeRoot, visit.next successor.next_eq⟩ := by
  generalize imageEq : root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current = image at successor
  cases image with
  | nativeWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_nativeWriteBranch visit write structural target evolution imageEq successor.next_eq
  | relationWrite write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_relationWriteBranch visit write structural target evolution imageEq successor.next_eq
  | continuedTransport write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_continuedTransportBranch visit write structural target evolution imageEq successor.next_eq
  | borromeanRedirect write structural target evolution =>
      exact root.generatedNextCurrentAt_eq_borromeanRedirectBranch visit write structural target evolution imageEq successor.next_eq
  | faithfulTerminal _ _ _ => exact successor.elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
