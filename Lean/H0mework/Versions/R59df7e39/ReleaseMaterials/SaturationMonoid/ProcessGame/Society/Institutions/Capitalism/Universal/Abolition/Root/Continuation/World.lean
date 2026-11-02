import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Frame
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorRead

/-! A conservative support extension.  The physical coordinate belongs to
the new source; every responsibility, claim and open witness is the original
one.  This does not allocate a second account or an instruction registry. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u
variable (N : WorldRelationNetwork.{u}) (Data : Type u)

def world : WorldRelationNetwork.{u} where
  Support := N.Support × Data
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  Responsibility := N.Responsibility
  Claim := N.Claim
  anchorAt := fun support => N.anchorAt support.1
  incidenceAt := fun support => N.incidenceAt support.1
  lineageAt := fun support => N.lineageAt support.1
  OpenAt := fun support responsibility => N.OpenAt support.1 responsibility
  openClaimAt := fun opened => N.openClaimAt opened
  openProgressBudgetAt := fun opened => N.openProgressBudgetAt opened
  HoldsAt := fun support claim => N.HoldsAt support.1 claim
  ObstructionAt := fun support => N.ObstructionAt support.1
  obstructionClaim := fun obstruction => N.obstructionClaim obstruction
  SemanticChangeAt := fun support before after => N.SemanticChangeAt support.1 before after
  DispositionAt := fun support kind => N.DispositionAt support.1 kind

def liftEntry (support : N.Support) (physical : Data) (entry : OpenResponsibilityAt N support) :
    OpenResponsibilityAt (world N Data) (support, physical) := entry

def lowerEntry (support : N.Support) (physical : Data)
    (entry : OpenResponsibilityAt (world N Data) (support, physical)) :
    OpenResponsibilityAt N support := entry

def translation (physical : Data) : TypedSemanticWorldNetworkTranslationAt N (world N Data) where
  support := ⟨fun support => (support, physical), Prod.fst, fun _ => rfl⟩
  anchor := ⟨id, id, fun _ => rfl⟩
  incidence := ⟨id, id, fun _ => rfl⟩
  lineage := ⟨id, id, fun _ => rfl⟩
  responsibility := ⟨id, id, fun _ => rfl⟩
  claim := ⟨id, id, fun _ => rfl⟩
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun support =>
    ⟨liftEntry N Data support physical, lowerEntry N Data support physical, fun _ => rfl⟩
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

theorem no_new_initial_rows (physical : Data) (support : N.Support)
    (entry : OpenResponsibilityAt (world N Data) (support, physical)) :
    ∃ old : OpenResponsibilityAt N support,
      ((translation N Data physical).oldOpenLedger support).forward old = entry :=
  ⟨entry, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
