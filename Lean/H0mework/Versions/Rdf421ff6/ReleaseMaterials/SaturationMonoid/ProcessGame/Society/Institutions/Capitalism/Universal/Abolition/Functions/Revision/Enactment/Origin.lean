import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment

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
  (ready : Trigger.ReadyAt context)

inductive Projection
  | originalSnapshot | originalRawReadout | nativeDispositions | currentScope

def originalComponent {world : WorldRelationNetwork} {vocabulary : ConstructiveRoot.Vocabulary}
    (actualRoot : SourceNativeLivingRootClosure world vocabulary) :
    SourceNativeProjectionLaw actualRoot.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_} _ _ => match projection with
    | .originalSnapshot => Macro.Raw.Snapshot (input := input) (depth := depth) (count := count)
        (prefixLimit := prefixLimit) (renewalLimit := renewalLimit)
    | .originalRawReadout => Macro.Raw.ResultAt context.native context.data context.reader context.germ
    | .nativeDispositions => Macro.Services.Migration.ImplicitReview.Completion.Native.BothAt
        (ready.material.task context) context.germ.snapshot (Trigger.nativeAtGerm context)
    | .currentScope => Trigger.ScopedAt context
  project := fun projection {_} _ _ => match projection with
    | .originalSnapshot => originalSnapshot context
    | .originalRawReadout => Macro.Raw.reportAt context.native context.data context.reader context.germ
    | .nativeDispositions => ready.services
    | .currentScope => ready.scope

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment
