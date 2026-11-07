import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Next
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Forward
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Projection.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (review : Option (ReviewPhase.ContextAt input))

variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount review}

namespace ActivatedFrame

variable (frame : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def rank : Nat × (Nat × Nat) := match frame with
  | .original current => current.rank
  | .enacted origin _ current => (origin.germ.snapshot.past.length + current.rank.1, current.rank.2)

def Layout : Type := match frame with
  | .original current => current.Layout
  | .enacted _ _ current => current.Layout

variable {frame}

theorem rank_eq_of_erasure
    (first second : ActivatedFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (firstLayout : first.Layout) (secondLayout : second.Layout)
    (same : first.presentation.erase = second.presentation.erase) : first.rank = second.rank := by
  cases first with
  | original left =>
    cases second with
    | original right =>
      have snapshots := Frame.snapshot_eq_of_erasure left right firstLayout secondLayout same
      exact Prod.ext (congrArg (fun value => value.past.length) snapshots) (congrArg measure same)
    | enacted origin admission right =>
      have oldCard := firstLayout.card
      have newCard := secondLayout.card
      have cards := congrArg erasedProjectionCard same
      change erasedProjectionCard (ActivatedFrame.original left).presentation.erase = _ at oldCard
      change erasedProjectionCard (ActivatedFrame.enacted origin admission right).presentation.erase = _ at newCard
      split_ifs at oldCard <;> omega
  | enacted origin admission left =>
    cases second with
    | original right =>
      have oldCard := secondLayout.card
      have newCard := firstLayout.card
      have cards := congrArg erasedProjectionCard same
      change erasedProjectionCard (ActivatedFrame.original right).presentation.erase = _ at oldCard
      change erasedProjectionCard (ActivatedFrame.enacted origin admission left).presentation.erase = _ at newCard
      split_ifs at oldCard <;> omega
    | enacted otherOrigin otherReady right =>
      have prefixes := Public.Runtime.Frame.same_erasure_keeps_the_complete_actual_prefix left right firstLayout secondLayout same
      apply Prod.ext ?_ (congrArg measure same)
      have lengths := congrArg List.length prefixes
      simpa only [rank, Public.Runtime.Frame.rank, List.length_append] using lengths

end ActivatedFrame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
