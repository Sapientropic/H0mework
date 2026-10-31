import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Frame
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

/-- This dictionary reads and transports the existing financial rows of one
source. It contains no next query, material outcome, or runtime activation. -/
structure FinancialData
    (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) where
  Ready : frame.V.Current → Prop
  ready_next : ∀ current, Ready current → Ready (frame.next current)
  bodyPaid : ∀ current, Ready current →
    Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current) = true
  familyAt : (current : frame.V.Current) → Ready current →
    { family : Epoch.Finance.Future.Continuation.AccountFamily input depth count frame.N (frame.account current) //
      family.currentSupport = frame.sourceSupport current }
  next_support : ∀ current ready,
    (familyAt current ready).val.support (frame.account (frame.next current)) ⟨frame.native current⟩ =
      frame.sourceSupport (frame.next current)
  occurrence_eq_emitted : (current : frame.V.Current) →
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) →
      occurrence = frame.root.emitted current


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation
