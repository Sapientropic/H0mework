import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Projection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

abbrev OldN := Admission.N seed claim
abbrev Unfocused := ExtendedNetwork (Background.world seed) (Gross.law seed claim)

def unfocusedSupport (support : (OldN seed claim).Support) : (Unfocused seed claim).Support :=
  (support.1.1,support.2)

/-- The original support remains intact. Only the active P incidence moves to
its same-identity Family row; BG and G keep their original native meanings. -/
def base : WorldRelationNetwork where
  Support := (OldN seed claim).Support
  Anchor := (Unfocused seed claim).Anchor
  Incidence := (Unfocused seed claim).Incidence
  Lineage := (Unfocused seed claim).Lineage
  Responsibility := (Unfocused seed claim).Responsibility
  Claim := (Unfocused seed claim).Claim
  anchorAt := fun support => (Unfocused seed claim).anchorAt (unfocusedSupport seed claim support)
  incidenceAt := fun support => (Unfocused seed claim).incidenceAt (unfocusedSupport seed claim support)
  lineageAt := fun support => (Unfocused seed claim).lineageAt (unfocusedSupport seed claim support)
  OpenAt := fun support => (Unfocused seed claim).OpenAt (unfocusedSupport seed claim support)
  openClaimAt := fun opened => (Unfocused seed claim).openClaimAt opened
  openProgressBudgetAt := fun opened => (Unfocused seed claim).openProgressBudgetAt opened
  HoldsAt := fun support => (Unfocused seed claim).HoldsAt (unfocusedSupport seed claim support)
  ObstructionAt := fun support => (Unfocused seed claim).ObstructionAt (unfocusedSupport seed claim support)
  obstructionClaim := fun obstruction => (Unfocused seed claim).obstructionClaim obstruction
  SemanticChangeAt := fun support => (Unfocused seed claim).SemanticChangeAt (unfocusedSupport seed claim support)
  DispositionAt := fun support => (OldN seed claim).DispositionAt support

abbrev NewN := ExtendedNetwork (base seed claim) (Responsibility.Family.activationLaw seed.claim)

def forwardSupport (support : (OldN seed claim).Support) : (NewN seed claim).Support :=
  (support,support.1.2.map (projectState seed claim))

def supportRetract : ConstructiveRetract (OldN seed claim).Support (NewN seed claim).Support :=
  ⟨forwardSupport seed claim,Prod.fst,fun _ => rfl⟩

theorem the_original_full_support_is_retained (support : (OldN seed claim).Support) :
    (forwardSupport seed claim support).1 = support := rfl

theorem no_original_productive_coordinate_is_restarted (support : (Background.world seed).Support)
    (shared : Current seed claim) (gross : Option (Gross.law seed claim).DebtState) :
    forwardSupport seed claim ((support,some (.current shared)),gross) =
      (((support,some (.current shared)),gross),some (familyState seed claim shared)) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
