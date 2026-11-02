import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (visit : RootFace.Visit input) (item : RootFace.Item input visit)

omit [DecidableEq Port] in
include item in
theorem the_original_actual_instruction_generates_positive_registration :
    0 < ProgrammeSource.registrationSize input := by
  cases emitted : input.emission? with
  | some emit => exact ProgrammeSource.generated_registration_positive input emit emitted
  | none =>
      rw [ProgrammeSource.registrationSize_fixed input emitted]
      apply List.length_pos_iff.mpr
      intro empty
      have original := item.property
      cases actual : visit.current with
      | bootstrap =>
          simp only [actual, ProgrammeSource.rawEvent, RawLaw.rawItems, RawLaw.execute,
            List.not_mem_nil] at original
      | running raw past =>
          simp only [actual, ProgrammeSource.rawEvent, ProgrammeSource.wordAt, emitted, empty,
            RawLaw.rawItems, RawLaw.execute, List.not_mem_nil] at original

#print axioms the_original_actual_instruction_generates_positive_registration

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
