import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.World
import H0mework.Foundation.Semantics.TheoryEvolution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Old Effect : Type}
  (N : WorldRelationNetwork) (focus : N.Support) (bearer : OpenResponsibilityAt N focus)
  (grammar : Language Old Effect) (observed : Set Effect) (old : TheoryState N)

local notation "W" => world N focus bearer grammar observed
local notation "Scope" => residual grammar observed

/-- A lawful scope can be covered by several independently usable old
codes. Each effect must have its own expression in the installed grammar. -/
def Covers (grammar : Language Old Effect) (scope : Set Effect) : Prop :=
  ∀ effect ∈ scope, ∃ code : grammar.Code, effect ∈ grammar.denotes code

theorem covers_iff (scope : Set Effect) : Covers grammar scope ↔ scope ⊆ grammar.covered :=
  Iff.rfl

theorem residual_not_covered (novel : ¬ observed ⊆ grammar.covered) :
    ¬ Covers grammar Scope := by
  obtain ⟨effect, found, absent⟩ := Set.not_subset.mp novel
  intro covered
  exact absent (covered effect ⟨found, absent⟩)

private def realizationAt {support : (W).Support} : (W).ObstructionAt support → Type
  | .inl original => old.inventory.RealizationAt original
  | .inr _ => PLift (Covers grammar Scope)

private def realizationWithoutAt (deleted : old.inventory.Law ⊕ Unit)
    {support : (W).Support} : (W).ObstructionAt support → Type
  | .inl original => match deleted with
    | .inl law => old.inventory.RealizationWithoutAt law original
    | .inr _ => old.inventory.RealizationAt original
  | .inr _ => match deleted with
    | .inl _ => PLift (Covers grammar Scope)
    | .inr _ => PLift (Scope = ∅)

private def denote {support : (W).Support} :
    old.ExpressionAt support ⊕ grammar.Code → (W).Claim
  | .inl expression => .inl (old.denotes expression)
  | .inr code => .inr (grammar.denotes code)

/-- Install the inherited theory and the exact operational refusal
grammar in the same source. The old law inventory remains available. -/
def theory : TheoryState W where
  inventory := {
    Version := old.inventory.Version × Language Old Effect
    version := (old.inventory.version, grammar)
    Law := old.inventory.Law ⊕ Unit
    RealizationAt := realizationAt N focus bearer grammar observed old
    RealizationWithoutAt := realizationWithoutAt N focus bearer grammar observed old }
  ExpressionAt := fun support => old.ExpressionAt support ⊕ grammar.Code
  denotes := denote N focus bearer grammar observed old
  TheoremAt := fun {support} expression => (W).HoldsAt support (denote N focus bearer grammar observed old expression)
  theoremPresentation := fun _ => ConstructivePresentation.refl _

local notation "Installed" => theory N focus bearer grammar observed old

def theory_conservative : ConservativeTheoryTranslation Installed (TheoryState.rootSemantic W) :=
  ⟨(Installed).denotes, fun _ => rfl⟩

theorem old_expression_denotes (support : (W).Support) (expression : old.ExpressionAt support) :
    (Installed).denotes (Sum.inl expression) = Sum.inl (old.denotes expression) :=
  rfl

theorem refusal_expression_denotes (support : (W).Support) (code : grammar.Code) :
    (Installed).denotes (support := support) (Sum.inr code) = Sum.inr (grammar.denotes code) :=
  rfl

def failure (novel : ¬ observed ⊆ grammar.covered) :
    ActualExpressibilityFailure Installed (obstruction N focus bearer grammar observed novel) where
  notExpressible := ⟨by
    rintro ⟨expression, names⟩
    cases expression with
    | inl inherited =>
        change Sum.inl (old.denotes inherited) = Sum.inr Scope at names
        cases names
    | inr code =>
        change (Sum.inr (grammar.denotes code) : (W).Claim) = Sum.inr Scope at names
        have exactScope := Sum.inr.inj names
        exact residual_not_covered grammar observed novel
          (fun effect found => ⟨code, exactScope.symm ▸ found⟩)⟩
  noLawfulRealization := ⟨fun realized => residual_not_covered grammar observed novel realized.down⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
