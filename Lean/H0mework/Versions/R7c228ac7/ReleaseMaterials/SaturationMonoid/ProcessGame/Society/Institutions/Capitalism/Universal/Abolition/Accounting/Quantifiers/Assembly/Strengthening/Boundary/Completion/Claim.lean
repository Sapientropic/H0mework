import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Diagram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def claimTransformation : diagram root boundary ⟶ (Functor.const ℕ).obj N.Claim :=
  NatTrans.ofSequence (fun n => TypeCat.ofHom (fun row : rows root boundary n => row.claim)) (by
    intro n
    rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right n 1)) =
      TypeCat.ofHom (step root boundary n) from Functor.ofSequence_map_homOfLE_succ _ n]
    ext original
    exact (the_original_compiler_keeps_the_same_claim_and_never_refills root
      (.finite (boundary.history.visitAt n)) (boundary.history.next_eq_at_visit n) original).1)

def claimCocone : (diagram root boundary).CoconeTypes where
  pt := N.Claim
  ι cut original := original.claim
  ι_naturality := by
    intro i j arrow
    funext original
    exact congrArg (fun h : rows root boundary i ⟶ N.Claim => h original)
      ((claimTransformation root boundary).naturality arrow)

def claim : Carrier root boundary → N.Claim := (diagram root boundary).descColimitType (claimCocone root boundary)

theorem the_completion_reads_each_literal_original_claim (cut : Nat) (original : rows root boundary cut) :
    claim root boundary (includeRow root boundary cut original) = original.claim := rfl

theorem distinct_original_claims_cannot_be_merged_or_erased
    (leftCut rightCut : Nat) (left : rows root boundary leftCut) (right : rows root boundary rightCut)
    (different : left.claim ≠ right.claim) :
    includeRow root boundary leftCut left ≠ includeRow root boundary rightCut right := by
  intro same
  exact different (congrArg (claim root boundary) same)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion
