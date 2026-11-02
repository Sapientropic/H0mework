import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def snapshotFace : SourceNativeRootSemanticFaceAt frame.package.frame.root (.finite frame.visit) :=
  Raw.snapshotFace frame.package.source frame.package.sourceData frame.package.reader frame.package.basis (.finite frame.visit)

theorem snapshot_reads_the_actual_current : frame.snapshotFace.rootRead.toPair = (frame.snapshot, frame.account) := by
  exact (Raw.installed_snapshot_reads_the_same_source frame.package.source frame.package.sourceData
    frame.package.reader frame.package.basis (.finite frame.visit)).trans
    (congrArg (fun snapshot => (snapshot, frame.account))
      (Raw.snapshot_of_a_completed_body_is_the_actual_past frame.package.source frame.package.sourceData
        frame.visit.current frame.ready))

theorem reentry_snapshot_is_the_original_mandatory_step
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (frame.reenter germ).snapshot = Mandatory.step (review := review) input depth count prefixLimit renewalLimit frame.snapshot germ.raw := by
  change Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit germ.snapshot germ.raw = _
  have original := (Raw.input_uses_the_literal_current_account frame.package.source frame.package.sourceData
    frame.package.reader germ).2.1
  rw [original]
  rfl

theorem reentry_adds_one_actual_input_to_the_original_past
    (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (frame.reenter germ).snapshot.past.length = frame.snapshot.past.length + 1 := by
  rw [frame.reentry_snapshot_is_the_original_mandatory_step germ]
  simp only [Mandatory.step, Mandatory.executionCursor, Physical.next, Physical.receive,
    List.length_append, List.length_singleton]

#print axioms snapshot_reads_the_actual_current
#print axioms reentry_adds_one_actual_input_to_the_original_past

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Frame
