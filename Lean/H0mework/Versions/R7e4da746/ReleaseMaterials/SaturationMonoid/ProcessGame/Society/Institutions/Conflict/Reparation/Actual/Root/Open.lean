import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Material

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open Quantities.Execution (endAt next query)
open Transport (sourceSupport)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (origin : Occurrence seed community)

abbrev originalCut := endAt seed origin.past
abbrev queriedCut := query (originalCut origin) origin.input
abbrev originalNext := next (originalCut origin) origin.input

def originalDraft := materialDraft (originalCut origin) origin.input (material_ready origin.damage)

def openOnTheActualWrite := (originalDraft origin).generated (file origin)

def openedVisit := (originalDraft origin).landed (file origin)

def originalVictimRow := (originalDraft origin).bornAtLanding (file origin)

def originalVictimAuthority := (originalDraft origin).bornAuthority (file origin)

theorem the_actual_material_cut_is_the_base_of_the_filing :
    HEq (openedVisit origin).support.1 (sourceSupport (originalNext origin).native) := by
  let first := (originalDraft origin).joined (file origin)
  have support := first.landed_support (first.inherit (originalDraft origin).resident)
    (Draft.inheritedEntry (originalDraft origin))
  exact (heq_of_eq (congrArg Prod.fst support)).trans
    (material_draft_reaches_the_original_visit (originalCut origin) origin.input (material_ready origin.damage))

theorem the_original_damage_is_filed_by_its_own_material_write :
    let actual := openOnTheActualWrite origin
    let reached := openedVisit origin
    actual.answer = origin ∧
    (⟨ExtendedNetwork (originalCut origin).native.frame.N (law origin),
      actual.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = reached.erase ∧
    HEq (originalVictimRow origin)
      (debtEntry (N := (originalCut origin).native.frame.N) (law := law origin)
        (originalDraft origin).afterSupport (Phase.live (opening origin))) ∧
    Quantities.Recorded seed (origin.past ++ [origin.input]) :=
  ⟨rfl, (originalDraft origin).the_joint_write_generates_its_own_successor (file origin),
    (originalDraft origin).the_born_row_at_the_successor_is_the_original_claim (file origin),
    Quantities.record seed _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
