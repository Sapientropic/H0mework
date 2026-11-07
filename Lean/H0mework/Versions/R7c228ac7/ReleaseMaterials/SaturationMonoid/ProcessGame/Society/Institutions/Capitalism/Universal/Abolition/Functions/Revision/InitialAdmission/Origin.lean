import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)

abbrev NativeDisclosureAt :=
  PLift (Abolition.Root.ReviewSource.DisclosureBlockerAt input
    (Abolition.Root.Settlement.committedVisit input depth count).current) ⊕
    (Σ task : Abolition.Root.ReviewSource.Material.OriginalTask input depth count,
      Macro.Services.Migration.ImplicitReview.Completion.Native.BothAt task context.germ.snapshot
        (Trigger.nativeAtGerm context))

def nativeDisclosure : NativeDisclosureAt context :=
  match Abolition.Root.ReviewSource.discloseTask input (Abolition.Root.Settlement.committedVisit input depth count).current with
  | .unresolved blocker => .inl ⟨blocker⟩
  | .declared task original => .inr ⟨⟨task, original⟩, Trigger.nativeInspection context ⟨task, original⟩⟩

def publicComponent {world : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    (actualRoot : SourceNativeLivingRootClosure world vocabulary) :
    SourceNativeProjectionLaw actualRoot.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Enactment.Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_} _ _ => match projection with
    | .originalSnapshot => Macro.Raw.Snapshot (input := input) (depth := depth) (count := count)
        (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)
    | .originalRawReadout => Macro.Raw.ResultAt context.native context.data context.reader context.germ
    | .nativeDispositions => NativeDisclosureAt context
    | .currentScope => Mandatory.CurrentScope.View input depth count prefixLimit renewalLimit context.germ.snapshot ×
        PublicPlan.Outcome input depth count prefixLimit renewalLimit (sourceSnapshot context)
  project := fun projection {_} _ _ => match projection with
    | .originalSnapshot => originalSnapshot context
    | .originalRawReadout => Macro.Raw.reportAt context.native context.data context.reader context.germ
    | .nativeDispositions => nativeDisclosure context
    | .currentScope => ⟨Mandatory.CurrentScope.inspect input depth count prefixLimit renewalLimit context.germ.snapshot,
        inspectPublic context⟩

/-- The same four origin coordinates retain the real old result, including
unknown or unpaid native scope. New permission needs no old-success token. -/
def originalComponent (admission : InitialAdmissionAt context)
    {world : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    (actualRoot : SourceNativeLivingRootClosure world vocabulary) :
    SourceNativeProjectionLaw actualRoot.toAuthoritativeRoot.toLedgerRoot.source :=
  match admission with
  | .legacy ready => Enactment.originalComponent context ready actualRoot
  | .publicPlan _ _ => publicComponent context actualRoot

theorem the_old_admitted_branch_keeps_its_literal_component
    (ready : Trigger.ReadyAt context)
    {world : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    (actualRoot : SourceNativeLivingRootClosure world vocabulary) :
    originalComponent context (.legacy ready) actualRoot = Enactment.originalComponent context ready actualRoot := rfl

#print axioms nativeDisclosure
#print axioms originalComponent

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.InitialAdmission
