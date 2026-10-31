import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

namespace Frame
variable (frame : Frame input)

theorem ordinary_erase : ((frame.ordinary input).presentation input).erase =
    (⟨frame.native.N, frame.native.root.generatedNextCurrentAt (frame.temporal input)⟩ : AnyAuthoritativeRootCurrent) := by
  let image := frame.native.program.emit frame.visit.current
  rw [frame.native.root.generatedNextCurrentAt_eq_nativeWriteBranch (frame.temporal input)
    image.write image.structural_eq image.targetOccurrence image.evolution image.generated_eq
    (nativeNext_eq input frame.native frame.visit.current)]
  rfl

theorem born_erase (registered : Registration input frame.native frame.visit.current) :
    ((frame.born input registered).presentation input).erase =
      (⟨(debtCore input frame.native (frame.temporal input) frame.authority registered).target.TargetN,
        (debtCore input frame.native (frame.temporal input) frame.authority registered).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) := by
  rw [(debtCore input frame.native (frame.temporal input) frame.authority registered).target.targetAnswerAndNext_next_eq]
  rfl

theorem successor_valid (query : (frame.presentation input).Query) :
    (((frame.next input).presentation input).erase =
        (RootInquiryProcessNode.answered (frame.presentation input) query).erase) ∧
      (RootInquiryProcessNode.active (frame.presentation input)).PreservesGeneratedLivingLawAt
        query (RootInquiryProcessNode.active ((frame.next input).presentation input)) := by
  cases query
  unfold Frame.next
  cases selected : registration? input frame.native frame.visit.current with
  | none =>
      apply RootInquiryProcessNode.active_directlyAnswered_successor_valid
        (frame.presentation input) ((frame.ordinary input).presentation input) PUnit.unit
        (answerFace input frame.native (frame.temporal input))
        (frame.installed.consumer input (frame.temporal input)
          (registration_absent_is_ordinary input frame.native (frame.temporal input) selected))
      · exact source_selected_ordinary input frame.native frame.installed (frame.temporal input) frame.authority selected
      · exact frame.ordinary_erase input
      · exact HEq.rfl
  | some registered =>
      apply RootInquiryProcessNode.active_debtAdmission_successor_valid
        (frame.presentation input) ((frame.born input registered).presentation input) PUnit.unit
        (debtCore input frame.native (frame.temporal input) frame.authority registered)
      · exact source_selected_debt_core input frame.native frame.installed (frame.temporal input)
          frame.authority registered selected
      · exact frame.born_erase input registered
      · exact HEq.rfl

end Frame

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
