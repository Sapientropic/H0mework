import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Past
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.ColimitType

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev rows (n : Nat) := OpenResponsibilityAt N
  (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt n).current)

def step (n : Nat) : rows root boundary n → rows root boundary (n + 1) :=
  root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (boundary.history.next_eq_at_visit n)

/-- The sole original ledger's canonical row restrictions, read from one
already occurred cofinal event. No target carrier or compatible family is input. -/
def diagram : ℕ ⥤ Type :=
  Functor.ofSequence (X := rows root boundary) (fun n => TypeCat.ofHom (step root boundary n))

abbrev Carrier := (diagram root boundary).ColimitType

def includeRow (cut : Nat) (original : rows root boundary cut) : Carrier root boundary :=
  (diagram root boundary).ιColimitType cut original

theorem each_actual_next_is_the_same_completed_standing (cut : Nat) (original : rows root boundary cut) :
    includeRow root boundary (cut + 1) (step root boundary cut original) = includeRow root boundary cut original := by
  have mapped := (diagram root boundary).ιColimitType_map
    (homOfLE (Nat.le_add_right cut 1)) original
  rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right cut 1)) =
    TypeCat.ofHom (step root boundary cut) from Functor.ofSequence_map_homOfLE_succ _ cut] at mapped
  exact mapped

theorem every_completed_standing_has_an_original_actual_source (point : Carrier root boundary) :
    ∃ cut original, includeRow root boundary cut original = point :=
  (diagram root boundary).ιColimitType_jointly_surjective point

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion
