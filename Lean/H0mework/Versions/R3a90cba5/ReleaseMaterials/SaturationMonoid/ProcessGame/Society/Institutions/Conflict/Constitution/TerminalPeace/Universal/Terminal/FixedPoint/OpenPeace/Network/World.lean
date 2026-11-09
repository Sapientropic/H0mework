import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Language

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Old Effect : Type}
  (N : WorldRelationNetwork) (focus : N.Support) (bearer : OpenResponsibilityAt N focus)
  (grammar : Language Old Effect) (observed : Set Effect)

def residual : Set Effect := observed \ grammar.covered

def GapAt (support : N.Support) : Type :=
  PLift (support = focus ∧ ¬ observed ⊆ grammar.covered)

private def semantics (support : N.Support) :
    (N.Claim ⊕ Set Effect) → (N.Claim ⊕ Set Effect) → Type
  | .inl left, .inl right => N.SemanticChangeAt support left right
  | .inl left, .inr right =>
      PLift (support = focus ∧ left = bearer.claim ∧ right = residual grammar observed ∧
        ¬ observed ⊆ grammar.covered)
  | _, _ => PEmpty

private def dispositions (support : N.Support) : WorldDispositionKind → Type
  | .supportSettlement => N.DispositionAt support .supportSettlement
  | .transfer => N.DispositionAt support .transfer
  | .lawSurfaceExtension => N.DispositionAt support .lawSurfaceExtension ⊕ GapAt N focus grammar observed support

/-- The paid scope extends the claim vocabulary at the exact old support.
The complete open responsibility carrier is inherited unchanged. -/
def world : WorldRelationNetwork where
  Support := N.Support
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  Responsibility := N.Responsibility
  Claim := N.Claim ⊕ Set Effect
  anchorAt := N.anchorAt
  incidenceAt := N.incidenceAt
  lineageAt := N.lineageAt
  OpenAt := N.OpenAt
  openClaimAt := fun opened => .inl (N.openClaimAt opened)
  openProgressBudgetAt := N.openProgressBudgetAt
  HoldsAt := fun support claim => match claim with
    | .inl old => N.HoldsAt support old
    | .inr scope => PLift (support = focus ∧ scope ⊆ observed)
  ObstructionAt := fun support => N.ObstructionAt support ⊕ GapAt N focus grammar observed support
  obstructionClaim := fun obstruction => match obstruction with
    | .inl old => .inl (N.obstructionClaim old)
    | .inr _ => .inr (residual grammar observed)
  SemanticChangeAt := semantics N focus bearer grammar observed
  DispositionAt := dispositions N focus grammar observed

local notation "W" => world N focus bearer grammar observed

abbrev inheritedEntry {support : N.Support} (entry : OpenResponsibilityAt N support) :
    OpenResponsibilityAt W support := entry

abbrev inheritedBearer : OpenResponsibilityAt W focus := bearer

def inheritedDisposition {support : N.Support} (kind : WorldDispositionKind)
    (receipt : N.DispositionAt support kind) : (W).DispositionAt support kind := by
  cases kind with
  | supportSettlement => exact receipt
  | transfer => exact receipt
  | lawSurfaceExtension => exact Sum.inl receipt

def translation : TypedSemanticWorldNetworkTranslationAt N W where
  support := ⟨id, id, fun _ => rfl⟩
  anchor := ⟨id, id, fun _ => rfl⟩
  incidence := ⟨id, id, fun _ => rfl⟩
  lineage := ⟨id, id, fun _ => rfl⟩
  responsibility := ⟨id, id, fun _ => rfl⟩
  claim := ⟨Sum.inl, Sum.elim id (fun _ => bearer.claim), fun _ => rfl⟩
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ => ⟨id, id, fun _ => rfl⟩
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ holds => holds
  oldDispositionSurvives := fun _ kind receipt => inheritedDisposition N focus bearer grammar observed kind receipt

def obstruction (novel : ¬ observed ⊆ grammar.covered) : (W).ObstructionAt focus :=
  Sum.inr ⟨rfl, novel⟩

theorem obstruction_claim (novel : ¬ observed ⊆ grammar.covered) :
    (W).obstructionClaim (obstruction N focus bearer grammar observed novel) =
      Sum.inr (residual grammar observed) :=
  rfl

theorem bearer_claim_ne_obstruction (novel : ¬ observed ⊆ grammar.covered) :
    (inheritedBearer N focus bearer grammar observed).claim ≠
      (W).obstructionClaim (obstruction N focus bearer grammar observed novel) := by
  intro equal
  change Sum.inl bearer.claim = Sum.inr (residual grammar observed) at equal
  cases equal

def residualHolds (novel : ¬ observed ⊆ grammar.covered) :
    (W).HoldsAt focus ((W).obstructionClaim (obstruction N focus bearer grammar observed novel)) :=
  ⟨rfl, fun _ found => found.1⟩

def residualChange (novel : ¬ observed ⊆ grammar.covered) :
    (W).SemanticChangeAt focus (inheritedBearer N focus bearer grammar observed).claim
      ((W).obstructionClaim (obstruction N focus bearer grammar observed novel)) :=
  ⟨rfl, rfl, rfl, novel⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
