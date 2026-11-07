import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.ProjectionLayout
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem component_heq {P Q : Type} (same : P = Q) :
    HEq (SourceNativeProjectionCoface.component Raw.Projection.snapshot : SourceNativeProjectionCoface P Raw.Projection)
      (SourceNativeProjectionCoface.component Raw.Projection.snapshot : SourceNativeProjectionCoface Q Raw.Projection) := by
  cases same
  exact HEq.rfl

private theorem project_congr (first second : AnyAuthoritativeRootCurrent)
    (firstProjection : first.current.root.source.projectionLaw.Projection)
    (secondProjection : second.current.root.source.projectionLaw.Projection)
    (firstActive : first.current.root.source.projectionLaw.ActiveAt firstProjection
      (first.current.root.emitted first.current.visit.current))
    (secondActive : second.current.root.source.projectionLaw.ActiveAt secondProjection
      (second.current.root.emitted second.current.visit.current))
    (same : first = second) (projections : HEq firstProjection secondProjection)
    (active : HEq firstActive secondActive) :
    HEq (first.current.root.source.projectionLaw.project firstProjection
      (first.current.root.emitted first.current.visit.current) firstActive)
      (second.current.root.source.projectionLaw.project secondProjection
        (second.current.root.emitted second.current.visit.current) secondActive) := by
  cases same
  cases projections
  cases active
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace Frame

theorem snapshot_eq_of_erasure
    (first second : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)
    (firstLayout : first.Layout) (secondLayout : second.Layout)
    (same : first.presentation.erase = second.presentation.erase) : first.snapshot = second.snapshot := by
  have cards := congrArg erasedProjectionCard same
  have sourceTypes := firstLayout.source_eq_of_card secondLayout cards
  have projections : HEq first.snapshotFace.projection second.snapshotFace.projection := component_heq sourceTypes
  have values : first.snapshotFace.rootRead = second.snapshotFace.rootRead :=
    eq_of_heq (project_congr first.presentation.erase second.presentation.erase
      first.snapshotFace.projection second.snapshotFace.projection
      first.snapshotFace.active second.snapshotFace.active same projections HEq.rfl)
  have pairs := congrArg Raw.Snapshot.toPair values
  rw [first.snapshot_reads_the_actual_current, second.snapshot_reads_the_actual_current] at pairs
  exact congrArg Prod.fst pairs

end Frame

variable (input depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (reader : Raw.Reader input depth count)
  (nativeOrigin : Option (ReviewSource.Native.OriginAt input) := none)

theorem same_erased_frame_has_the_same_original_past (first second : Nat)
    (same : (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader first).presentation.erase =
      (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader second).presentation.erase) :
    (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader first).snapshot =
      (frames (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader second).snapshot :=
  Frame.snapshot_eq_of_erasure _ _
    (framesLayout (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader first)
    (framesLayout (nativeOrigin := nativeOrigin) (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition reader second) same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.same_erased_frame_has_the_same_original_past
