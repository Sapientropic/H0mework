import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Feed
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- This finite readout preserves each original occurrence address. Equal
reports do not merge task declarations; undisclosed rows are retained too. -/
def pastDisclosures (cut : Nat) : List (Σ ordinal : Nat,
    TaskDisclosureAt input (ProgrammeHistory.visitAt input ordinal).current) :=
  (List.range cut).map fun ordinal => ⟨ordinal,
    discloseTask input (ProgrammeHistory.visitAt input ordinal).current⟩

theorem every_prior_original_occurrence_is_retained (cut : Nat) :
    pastDisclosures input (cut + 1) = pastDisclosures input cut ++
      [⟨cut, discloseTask input (ProgrammeHistory.visitAt input cut).current⟩] := by
  simp only [pastDisclosures, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem an_earlier_task_or_disclosure_blocker_is_not_erased (cut : Nat) :
    pastDisclosures input cut <+: pastDisclosures input (cut + 1) := by
  rw [every_prior_original_occurrence_is_retained]
  exact List.prefix_append _ _

theorem each_readout_has_its_exact_original_visit (cut ordinal : Nat) (earlier : ordinal < cut) :
    (⟨ordinal, discloseTask input (ProgrammeHistory.visitAt input ordinal).current⟩ :
      Σ index : Nat, TaskDisclosureAt input (ProgrammeHistory.visitAt input index).current) ∈ pastDisclosures input cut :=
  List.mem_map.mpr ⟨ordinal, List.mem_range.mpr earlier, rfl⟩

/-- Public source entry: both components are restrictions of the canonical
finite original history, never a caller-built current or a new runtime. -/
def originalVisitFeed (ordinal bound : Nat) :=
  ((reviewProjection input bound).project ()
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input ordinal).current) (),
    pastDisclosures input ordinal)

theorem original_visit_feed_keeps_its_actual_occurrence_and_whole_write (ordinal bound : Nat) :
    (originalVisitFeed input ordinal bound).1.1 =
      (ProgrammeSource.ledgerCompiler input).compile
        (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input ordinal).current) ∧
    (originalVisitFeed input ordinal bound).1.2 =
      sourceReviewFeed input (ProgrammeHistory.visitAt input ordinal).current bound ∧
    (originalVisitFeed input ordinal bound).2 = pastDisclosures input ordinal := ⟨rfl, rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.each_readout_has_its_exact_original_visit

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.original_visit_feed_keeps_its_actual_occurrence_and_whole_write
