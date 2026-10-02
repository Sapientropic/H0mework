import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRestriction.Restriction
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
local notation "B" => MotherArenaHigher.Base rank

private theorem lineage_subsingleton {first last : N.Support}
    (source : OpenResponsibilityAt N first) (target : OpenResponsibilityAt N last) :
    Subsingleton (RootDebtLineageAt N source target) := by
  constructor
  intro left right
  cases left
  cases right
  rfl

private theorem fresh_subsingleton (first : N.Support) {last : N.Support}
    (target : OpenResponsibilityAt N last) : Subsingleton (RootDebtFreshAt N first target) := by
  constructor
  intro left right
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      have same : left = right := by
        funext source lineage
        exact (left source lineage).elim
      cases same
      rfl

abbrev Debt (support : N.Support) {targetSupport : N.Support}
    (target : OpenResponsibilityAt N targetSupport) :=
  (Σ source : OpenResponsibilityAt N support, RootDebtLineageAt N source target) ⊕
    RootDebtFreshAt N support target

/-- The actual old ledger entry and the old/fresh branch tag encode the
whole debt result. All proof-valued identities and fresh exclusions are
retained by their original subsingleton laws. -/
def debtAddress (entry : ∀ support, OpenResponsibilityAt N support ↪ B)
    (support : N.Support) {targetSupport : N.Support}
    (target : OpenResponsibilityAt N targetSupport) : Debt support target ↪ B :=
  MotherArenaObligation.sumEmbedding
    { toFun := fun debt => entry support debt.1
      inj' := by
        intro first last same
        have equal : first.1 = last.1 := (entry support).injective same
        apply Sigma.ext equal
        cases first with
        | mk first firstLineage =>
          cases last with
          | mk last lastLineage =>
            dsimp only at equal
            cases equal
            exact heq_of_eq ((lineage_subsingleton first target).elim firstLineage lastLineage) }
    { toFun := fun _ => MotherArenaHigher.point rank (.inl ())
      inj' := fun first last _ => (fresh_subsingleton support target).elim first last }

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
