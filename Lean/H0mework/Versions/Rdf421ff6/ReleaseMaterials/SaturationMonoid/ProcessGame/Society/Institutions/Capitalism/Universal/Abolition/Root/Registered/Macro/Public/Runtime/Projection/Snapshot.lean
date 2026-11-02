import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Projection.Layout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Query

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem component_heq {P Q : Type} (same : P = Q) :
    HEq (SourceNativeProjectionCoface.component Inquiry.Projection.snapshot : SourceNativeProjectionCoface P Inquiry.Projection)
      (SourceNativeProjectionCoface.component Inquiry.Projection.snapshot : SourceNativeProjectionCoface Q Inquiry.Projection) := by
  cases same
  exact HEq.rfl

private theorem project_congr_unique (first second : AnyAuthoritativeRootCurrent)
    (left : first.current.root.source.projectionLaw.Projection)
    (right : second.current.root.source.projectionLaw.Projection)
    (leftActive : first.current.root.source.projectionLaw.ActiveAt left
      (first.current.root.emitted first.current.visit.current))
    (rightActive : second.current.root.source.projectionLaw.ActiveAt right
      (second.current.root.emitted second.current.visit.current))
    (unique : Subsingleton (first.current.root.source.projectionLaw.ActiveAt left
      (first.current.root.emitted first.current.visit.current)))
    (same : first = second) (projections : HEq left right) :
    HEq (first.current.root.source.projectionLaw.project left
      (first.current.root.emitted first.current.visit.current) leftActive)
      (second.current.root.source.projectionLaw.project right
        (second.current.root.emitted second.current.visit.current) rightActive) := by
  cases same
  cases projections
  cases unique.elim leftActive rightActive
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}

namespace Frame
variable (frame : Frame origin admission)

def snapshotFace : SourceNativeRootSemanticFaceAt frame.full.root (.finite frame.visit) where
  projection := (Inquiry.installation frame.source frame.reader).embed .snapshot
  active := frame.actual
  classifier_eq := Inquiry.the_unique_source_active_is_selected frame.source .snapshot _ frame.actual

def snapshotRead : Inquiry.Snapshot (input := input) (depth := depth) (count := count) := frame.snapshotFace.rootRead

theorem snapshot_read_is_the_literal_actual_source :
    frame.snapshotRead.oldPast = origin.germ.snapshot.past ∧
      frame.snapshotRead.physical = frame.snapshot ∧ frame.snapshotRead.account = frame.account := ⟨rfl, rfl, rfl⟩

end Frame

variable {otherOrigin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {otherAdmission : Abolition.Functions.Revision.InitialAdmissionAt otherOrigin}

 theorem Frame.same_erasure_keeps_the_complete_actual_prefix
    (first : Frame origin admission) (second : Frame otherOrigin otherAdmission)
    (leftLayout : first.Layout) (rightLayout : second.Layout)
    (same : first.presentation.erase = second.presentation.erase) :
    origin.germ.snapshot.past ++ first.snapshot.past = otherOrigin.germ.snapshot.past ++ second.snapshot.past := by
  have cards := congrArg Macro.Runtime.erasedProjectionCard same
  have sources := leftLayout.source_eq_of_card rightLayout cards
  have projections := component_heq sources
  have values : first.snapshotRead = second.snapshotRead :=
    eq_of_heq (project_congr_unique first.presentation.erase second.presentation.erase
      first.snapshotFace.projection second.snapshotFace.projection
      first.snapshotFace.active second.snapshotFace.active
      (Inquiry.instSubsingletonActualAt (frame := first.source) first.visit.current) same projections)
  have prefixes := congrArg (fun (value : Inquiry.Snapshot (input := input) (depth := depth) (count := count)) =>
    value.oldPast ++ value.physical.past) values
  rw [first.snapshot_read_is_the_literal_actual_source.1, second.snapshot_read_is_the_literal_actual_source.1,
    first.snapshot_read_is_the_literal_actual_source.2.1, second.snapshot_read_is_the_literal_actual_source.2.1] at prefixes
  exact prefixes

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime
