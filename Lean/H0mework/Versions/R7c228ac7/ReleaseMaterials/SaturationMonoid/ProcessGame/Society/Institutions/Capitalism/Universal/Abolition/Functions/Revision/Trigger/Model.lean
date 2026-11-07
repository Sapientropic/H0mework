import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger

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

structure CurrentMaterialAt where
  boundary : Boundary context
  source : Abolition.Root.ReviewSource.Control.boundary? input depth count prefixLimit renewalLimit context.germ.snapshot = some boundary
  fresh : IsCurrentPaidBoundary context boundary

def CurrentMaterialAt.task (material : CurrentMaterialAt context) : Abolition.Root.ReviewSource.Material.OriginalTask input depth count := by
  rcases material with ⟨boundary, source, fresh⟩
  cases boundary with
  | unavailable => exact fresh.elim
  | stopped => exact fresh.elim
  | materialPaid located original prepared generated candidate occurred source => exact prepared.task

structure ScopedAt where
  word : Source.Program.RawEvent Party Good Port Technology Instrument
  phase : (Physical.stateAt input depth count prefixLimit renewalLimit context.germ.snapshot.past).phase = .renewal word
  checked : Mandatory.CurrentScope.Checks input depth count prefixLimit renewalLimit context.germ.snapshot word

structure ReadyAt where
  material : CurrentMaterialAt context
  scope : ScopedAt context
  services : Macro.Services.Migration.ImplicitReview.Completion.Native.BothAt
    (material.task context) context.germ.snapshot (nativeAtGerm context)
  services_exact : services = nativeInspection context (material.task context)

/-- Every negative branch retains its original typed source object. This
selection contains neither an enacted world nor a successful future. -/
inductive Selection : Type
  | seeking (phase : (Physical.stateAt input depth count prefixLimit renewalLimit context.germ.snapshot.past).phase = .seeking)
  | scopeResidual (failure : Mandatory.CurrentScope.Failure input depth count prefixLimit renewalLimit context.germ.snapshot)
  | ordinary (absent : Abolition.Root.ReviewSource.Control.boundary? input depth count prefixLimit renewalLimit context.germ.snapshot = none)
  | boundaryResidual (boundary : Boundary context)
      (source : Abolition.Root.ReviewSource.Control.boundary? input depth count prefixLimit renewalLimit context.germ.snapshot = some boundary)
      (notCurrent : currentPaidBoundaryFlag context boundary = false)
  | enactment (ready : ReadyAt context)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger
