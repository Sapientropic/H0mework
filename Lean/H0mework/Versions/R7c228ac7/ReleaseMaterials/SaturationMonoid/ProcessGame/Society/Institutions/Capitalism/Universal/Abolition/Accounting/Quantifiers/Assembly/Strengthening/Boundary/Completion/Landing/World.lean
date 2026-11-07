import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev RawSupport := N.Support × Bool
abbrev RowKey := N.Responsibility ⊕ Carrier root boundary

/-- The receipt carries the actual source cut and its complete original row.
It is not an authorization inferred from claim equality. -/
inductive RegistrationAt : RawSupport (N := N) → Type
  | past (cut : Nat) (original : rows root boundary cut) :
      RegistrationAt (root.toAuthoritativeRoot.toRoot.supportAt
        (boundary.history.visitAt cut).current,false)
  | completed (point : Carrier root boundary) (cut : Nat) (original : rows root boundary cut)
      (source_eq : includeRow root boundary cut original = point)
      (budget_attained : original.progressBudget = budget root boundary point) :
      RegistrationAt (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true)

def OpenAt : RawSupport (N := N) → RowKey root boundary → Type
  | support, .inl original => N.OpenAt support.1 original
  | (_, false), .inr _ => PEmpty
  | (support, true), .inr point => PLift (lineage root boundary point = N.lineageAt support)

def rowClaim : {support : RawSupport (N := N)} → {key : RowKey root boundary} →
    OpenAt root boundary support key → N.Claim
  | _, .inl _, opened => N.openClaimAt opened
  | (_, false), .inr _, opened => nomatch opened
  | (_, true), .inr point, _ => claim root boundary point

def rowBudget : {support : RawSupport (N := N)} → {key : RowKey root boundary} →
    OpenAt root boundary support key → Nat
  | _, .inl _, opened => N.openProgressBudgetAt opened
  | (_, false), .inr _, opened => nomatch opened
  | (_, true), .inr point, _ => budget root boundary point

def DispositionAt (support : RawSupport (N := N)) : WorldDispositionKind → Type
  | .transfer => N.DispositionAt support.1 .transfer ⊕ RegistrationAt root boundary support
  | .supportSettlement => N.DispositionAt support.1 .supportSettlement
  | .lawSurfaceExtension => N.DispositionAt support.1 .lawSurfaceExtension

/-- One ledger changes representation at the source's actual boundary.
Its claim type remains the original claim type; old landing rows stay literal. -/
def world : WorldRelationNetwork where
  Support := RawSupport (N := N)
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  Responsibility := RowKey root boundary
  Claim := N.Claim
  anchorAt := fun support => N.anchorAt support.1
  incidenceAt := fun support => N.incidenceAt support.1
  lineageAt := fun support => N.lineageAt support.1
  OpenAt := OpenAt root boundary
  openClaimAt := rowClaim root boundary
  openProgressBudgetAt := rowBudget root boundary
  HoldsAt := fun support => N.HoldsAt support.1
  ObstructionAt := fun support => N.ObstructionAt support.1
  obstructionClaim := N.obstructionClaim
  SemanticChangeAt := fun support => N.SemanticChangeAt support.1
  DispositionAt := DispositionAt root boundary

abbrev W := world root boundary

def oldRow {support : N.Support} (phase : Bool) (original : OpenResponsibilityAt N support) :
    OpenResponsibilityAt (W root boundary) (support,phase) :=
  ⟨.inl original.1,original.2⟩

def landingRow (point : Carrier root boundary)
    (same : lineage root boundary point =
      N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt boundary.current)) :
    OpenResponsibilityAt (W root boundary)
      (root.toAuthoritativeRoot.toRoot.supportAt boundary.current,true) :=
  ⟨.inr point,PLift.up same⟩

theorem old_row_keeps_its_original_claim_and_budget {support : N.Support} (phase : Bool)
    (original : OpenResponsibilityAt N support) :
    (oldRow root boundary phase original).claim = original.claim ∧
      (oldRow root boundary phase original).progressBudget = original.progressBudget :=
  ⟨rfl,rfl⟩

theorem landed_row_keeps_the_original_claim_and_actual_budget
    (point : Carrier root boundary) (same) :
    (landingRow root boundary point same).claim = claim root boundary point ∧
      (landingRow root boundary point same).progressBudget = budget root boundary point :=
  ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
