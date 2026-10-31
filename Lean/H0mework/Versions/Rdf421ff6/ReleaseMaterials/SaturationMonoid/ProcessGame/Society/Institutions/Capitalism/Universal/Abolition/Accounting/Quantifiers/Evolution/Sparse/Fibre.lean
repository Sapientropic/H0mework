import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Evolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Fibre

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)

abbrev Origin := current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current

/-- Unselected source elements retain their original support and whole account.
Only the emitted occurrence is the live action. -/
def supportAt (phase : Bool) (origin : Origin claim current) : (N).Support := by
  classical
  exact match phase with
  | false => origin.1
  | true => if origin = current.root.emitted current.visit.current then
      Sparse.support claim current word true else origin.1

theorem initial_support (origin : Origin claim current) : supportAt claim current word false origin = origin.1 := rfl

theorem emitted_support (phase : Bool) :
    supportAt claim current word phase (current.root.emitted current.visit.current) = Sparse.support claim current word phase := by
  cases phase with
  | false => rfl
  | true => exact if_pos rfl

theorem unselected_support (origin : Origin claim current) (notSelected : origin ≠ current.root.emitted current.visit.current) :
    supportAt claim current word true origin = origin.1 := by simp [supportAt,notSelected]

theorem anchor_coherent (phase : Bool) (origin : Origin claim current) :
    (N).anchorAt (supportAt claim current word phase (current.root.emitted current.visit.current)) =
      (N).anchorAt (supportAt claim current word phase origin) := by
  have same := (current.root.toAuthoritativeRoot.toRoot.account.anchor_commutes
    (current.root.emitted current.visit.current)).symm.trans
    (current.root.toAuthoritativeRoot.toRoot.account.anchor_commutes origin)
  cases phase with
  | false => exact same
  | true =>
    rw [emitted_support]
    by_cases selected : origin = current.root.emitted current.visit.current
    · subst origin; rw [emitted_support]
    · rw [unselected_support claim current word origin selected]; exact same

theorem incidence_coherent (phase : Bool) (origin : Origin claim current) :
    (N).incidenceAt (supportAt claim current word phase (current.root.emitted current.visit.current)) =
      (N).incidenceAt (supportAt claim current word phase origin) := by
  have same := (current.root.toAuthoritativeRoot.toRoot.account.incidence_commutes
    (current.root.emitted current.visit.current)).symm.trans
    (current.root.toAuthoritativeRoot.toRoot.account.incidence_commutes origin)
  cases phase with
  | false => exact same
  | true =>
    rw [emitted_support]
    by_cases selected : origin = current.root.emitted current.visit.current
    · subst origin; rw [emitted_support]
    · rw [unselected_support claim current word origin selected]; exact same

theorem lineage_coherent (phase : Bool) (origin : Origin claim current) :
    (N).lineageAt (supportAt claim current word phase (current.root.emitted current.visit.current)) =
      (N).lineageAt (supportAt claim current word phase origin) := by
  have same := (current.root.toAuthoritativeRoot.toRoot.account.lineage_commutes
    (current.root.emitted current.visit.current)).symm.trans
    (current.root.toAuthoritativeRoot.toRoot.account.lineage_commutes origin)
  cases phase with
  | false => exact same
  | true =>
    rw [emitted_support]
    by_cases selected : origin = current.root.emitted current.visit.current
    · subst origin; rw [emitted_support]
    · rw [unselected_support claim current word origin selected]; exact same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Fibre
