import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.State

import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core.ResidentWrite

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (Resident First StateAt identityWhole)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

/-- An installed occurrence reads its payload on the original live state.
Its stack and all previously installed dependent reads remain in place. -/
structure Landed (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
    (cut : Root.Cut Party Good Port Technology Instrument) (Payload : Type) where
  private mk ::
  state : StateAt seed community cut
  material : SourceNativeRootSemanticFaceAt state.resident.root state.resident.visit
  materialType : material.Restriction = Payload

def Landed.read {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
    {Payload : Type} (visit : Landed seed community cut Payload) : Payload :=
  cast visit.materialType visit.material.rootRead

variable {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {Payload : Type}

private theorem finiteRows (prior : StateAt seed community cut) :
    Finite (OpenResponsibilityAt prior.world prior.resident.support) := by
  rw [prior.exactSupport]
  let native := cut.native
  exact prior.stack.finite _ (native.frame.entries_finite native.visit.current)

theorem ready (prior : StateAt seed community cut) : ResidentWrite.Ready prior.resident :=
  ⟨finiteRows prior, prior.stack.fibres cut.native.frame.family.open_fibres⟩

variable (prior : StateAt seed community cut) (emission : Payload) (writes : Bool)

def action := ResidentWrite.action prior.resident (ready prior) emission writes

private def landed : Resident prior.world :=
  ResidentWrite.landing prior.resident (ready prior) emission writes

def publish : Landed seed community cut Payload where
  state := {
    world := prior.world
    stack := prior.stack
    resident := landed prior emission writes
    exactSupport := (ResidentWrite.support_eq prior.resident (ready prior) emission writes).trans prior.exactSupport }
  material := ResidentWrite.face prior.resident (ready prior) emission writes
  materialType := rfl

theorem the_canonical_write_is_the_published_whole_state :
    (⟨prior.world, (action prior emission writes).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (publish prior emission writes).state.resident.erase :=
  ResidentWrite.canonical_next prior.resident (ready prior) emission writes

theorem original_rows_are_the_whole_first_write :
    let written := (action prior emission writes).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  ResidentWrite.whole_first_write prior.resident (ready prior) emission writes

theorem earlier_reads_are_kept_at_the_landing
    (projection : prior.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (publish prior emission writes).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.resident.root.source.base.projectionLaw.outcomeAt projection
        (prior.resident.root.emitted prior.resident.visit.current)) :=
  ResidentWrite.earlier_reads prior.resident (ready prior) emission writes projection

theorem publish_reads_the_exact_payload :
    (publish prior emission writes).read = emission :=
  rfl

theorem publish_preserves_the_entire_stack :
    (publish prior emission writes).state.stack = prior.stack :=
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core
