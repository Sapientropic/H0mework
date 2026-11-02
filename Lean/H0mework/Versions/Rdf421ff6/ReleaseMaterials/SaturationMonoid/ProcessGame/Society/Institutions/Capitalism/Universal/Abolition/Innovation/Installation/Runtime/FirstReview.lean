import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Drain

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

def firstPublic (nature : RequestAt) (admission : InitialAdmissionAt (firstOrigin nature)) :=
  Macro.Public.Runtime.Frame.initial (closedOriginal nature).package (.finite (closedOriginal nature).visit)
    (closedOriginal nature).authority (firstRaw nature).germ admission

private theorem original_next_at_its_raw_query
    (frame : Macro.Runtime.Frame (review := none) input 0 count 0 0 0 count)
    (raw : Macro.Runtime.ActivatedFrame.OriginalBoundary frame) :
    (.original frame : Macro.Runtime.ActivatedFrame (review := none) input 0 count 0 0 0 count).next =
      match InitialAdmission.select (frame.controlOrigin raw.germ) with
      | .admitted admission => .enacted (frame.controlOrigin raw.germ) admission
          (Macro.Public.Runtime.Frame.initial frame.package (.finite frame.visit) frame.authority raw.germ admission)
      | .obstructed _ => .original (frame.reenter raw.germ) := by
  dsimp only [Macro.Runtime.ActivatedFrame.next]
  rw [raw.selected]
  dsimp only
  simp only [Macro.Runtime.Frame.controlOrigin, Macro.Runtime.Frame.nextAt]
  split <;> simp_all only

theorem the_first_review_executes_its_own_source_selection (nature : RequestAt) :
    match InitialAdmission.select (firstOrigin nature) with
    | .admitted admission =>
        current nature (boundaryTick nature 0 + 1) =
          .enacted (firstOrigin nature) admission (firstPublic nature admission)
    | .obstructed _ =>
        current nature (boundaryTick nature 0 + 1) =
          .original ((closedOriginal nature).reenter (firstRaw nature).germ) := by
  have next := (congrArg Macro.Runtime.ActivatedFrame.next
    (the_first_raw_boundary_is_source_generated nature)).trans
      (original_next_at_its_raw_query (closedOriginal nature) (firstRaw nature))
  have successor : current nature (boundaryTick nature 0 + 1) = (boundary nature 0).next := rfl
  have actualNext := successor.trans next
  cases choice : InitialAdmission.select (firstOrigin nature) with
  | admitted admission =>
      simp only [firstOrigin] at choice
      with_unfolding_all simpa only [choice, firstPublic, firstOrigin] using actualNext
  | obstructed failure =>
      simp only [firstOrigin] at choice
      with_unfolding_all simpa only [choice] using actualNext

theorem the_generated_admission_reaches_its_fully_accounted_actual_public_cut
    (nature : RequestAt) (admission : InitialAdmissionAt (firstOrigin nature))
    (chosen : InitialAdmission.select (firstOrigin nature) = .admitted admission) :
    boundary nature 1 = .enacted (firstOrigin nature) admission (firstPublic nature admission).drained ∧
      ¬ (firstPublic nature admission).drained.HasWork := by
  have started := the_first_review_executes_its_own_source_selection nature
  rw [chosen] at started
  exact ⟨an_actual_public_current_reaches_its_own_native_boundary nature
    (firstPublic nature admission) (boundaryTick nature 0 + 1) started,
    (firstPublic nature admission).drain.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
