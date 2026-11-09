import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.FirstWrite
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Guard

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (Resident First identityWhole)
open Quantities.Execution (endAt)
open Renewal (Native Request Replies Admission Refusal readAction)

noncomputable section

abbrev OldState (history : Original.Word) :=
  Reparation.Actual.State Original.seed Original.community history

abbrev originalNative (history : Original.Word) : Native :=
  (endAt Original.seed history).state

/-- The selected request and its actual source state determine the material
inventory and successor by the revised physical compiler. -/
structure Effect where
  before : Native
  request : Request

abbrev Effect.native (effect : Effect) : Native :=
  (readAction effect.before effect.request).next

abbrev Effect.items (effect : Effect) : List Original.Item :=
  (readAction effect.before effect.request).execution.items

/-- A denied request is a recorded occurrence of the same runtime. Its
material coordinate reads the preceding paid effect. -/
inductive Event where
  | paid (effect : Effect) (answers : Replies effect.before effect.request)
      (approved : Admission effect.before effect.request answers)
  | refused (previous : Effect) (request : Request) (answers : Replies previous.native request)
      (issue : Refusal previous.native request answers)

def Event.effect : Event → Effect
  | .paid effect _ _ => effect
  | .refused previous _ _ _ => previous

def Event.items : Event → List Original.Item
  | .paid effect _ _ => effect.items
  | .refused _ _ _ _ => []

private def Event.writes : Event → Bool
  | .paid effect _ _ => (readAction effect.before effect.request).isAccepted
  | .refused _ _ _ _ => true

/-- The original state carries the entire financial and reparation
account. Material continuation reads the installed exact occurrence. -/
structure Live (history : Original.Word) where
  private mk ::
  state : OldState history
  material : SourceNativeRootSemanticFaceAt state.resident.root state.resident.visit
  materialType : material.Restriction = Event

def Live.event {history : Original.Word} (live : Live history) : Event :=
  cast live.materialType live.material.rootRead

abbrev Live.effect {history : Original.Word} (live : Live history) : Effect :=
  live.event.effect

abbrev Live.native {history : Original.Word} (live : Live history) : Native :=
  live.effect.native

abbrev Live.items {history : Original.Word} (live : Live history) : List Original.Item :=
  live.event.items

variable {history : Original.Word} (prior : OldState history) (emission : Event)

private abbrev action := Core.action prior emission emission.writes

private def publish : Live history :=
  let arrived := Core.publish prior emission emission.writes
  ⟨arrived.state, arrived.material, arrived.materialType⟩

private theorem the_canonical_write_is_the_published_whole_state :
    (⟨prior.world, (action prior emission).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (publish prior emission).state.resident.erase :=
  Core.the_canonical_write_is_the_published_whole_state prior emission emission.writes

private theorem original_rows_are_the_whole_first_write :
    let written := (action prior emission).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  Core.original_rows_are_the_whole_first_write prior emission emission.writes

private theorem earlier_reads_are_kept_at_the_landing
    (projection : prior.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (publish prior emission).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.resident.root.source.base.projectionLaw.outcomeAt projection
        (prior.resident.root.emitted prior.resident.visit.current)) :=
  Core.earlier_reads_are_kept_at_the_landing prior emission emission.writes projection

/-- Enter through the native state of the retained historical cut. -/
private def installAction (request : Request) {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) :=
  action prior (.paid ⟨originalNative history, request⟩ answers approved)

private def install (request : Request) {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) : Live history :=
  publish prior (.paid ⟨originalNative history, request⟩ answers approved)

theorem install_is_the_canonical_whole_write (request : Request)
    {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) :
    (⟨prior.world, (installAction prior request approved).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (install prior request approved).state.resident.erase :=
  the_canonical_write_is_the_published_whole_state prior (.paid ⟨originalNative history, request⟩ answers approved)

theorem install_reads_its_exact_material_effect (request : Request)
    {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) :
    (install prior request approved).effect = ⟨originalNative history, request⟩ :=
  rfl

theorem install_keeps_the_exact_original_stack (request : Request)
    {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) :
    (install prior request approved).state.stack = prior.stack :=
  rfl

theorem install_keeps_every_original_row (request : Request)
    {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers) :
    let written := (installAction prior request approved).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  original_rows_are_the_whole_first_write prior (.paid ⟨originalNative history, request⟩ answers approved)

theorem install_retains_every_earlier_read (request : Request)
    {answers : Replies (originalNative history) request}
    (approved : Admission (originalNative history) request answers)
    (projection : prior.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (install prior request approved).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.resident.root.source.base.projectionLaw.outcomeAt projection
        (prior.resident.root.emitted prior.resident.visit.current)) :=
  earlier_reads_are_kept_at_the_landing prior (.paid ⟨originalNative history, request⟩ answers approved) projection

namespace Live

variable (live : Live history) (request : Request) {answers : Replies live.native request}
  (approved : Admission live.native request answers)

def stepAction := action live.state (.paid ⟨live.native, request⟩ answers approved)

/-- The next write consumes the current material face and the original
account of the same historical cut. -/
def step : Live history :=
  publish live.state (.paid ⟨live.native, request⟩ answers approved)

theorem step_is_the_canonical_whole_write :
    (⟨live.state.world, (stepAction live request approved).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (step live request approved).state.resident.erase :=
  the_canonical_write_is_the_published_whole_state live.state (.paid ⟨live.native, request⟩ answers approved)

theorem step_reads_its_exact_material_effect :
    (step live request approved).effect = ⟨live.native, request⟩ :=
  rfl

theorem step_keeps_the_exact_original_stack :
    (step live request approved).state.stack = live.state.stack :=
  rfl

theorem step_keeps_every_original_row :
    let written := (stepAction live request approved).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole live.state.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  original_rows_are_the_whole_first_write live.state (.paid ⟨live.native, request⟩ answers approved)

theorem step_retains_every_earlier_read
    (projection : live.state.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (step live request approved).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (live.state.resident.root.source.base.projectionLaw.outcomeAt projection
        (live.state.resident.root.emitted live.state.resident.visit.current)) :=
  earlier_reads_are_kept_at_the_landing live.state (.paid ⟨live.native, request⟩ answers approved) projection

end Live

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation
