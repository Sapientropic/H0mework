import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Universal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

private def canonicalReceipt (living : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt living.toAuthoritativeRoot.toLedgerRoot) {after : V.Current}
    (nextEq : (living.toAuthoritativeRoot.toRoot.evolutionAt visit.current).nextCurrent? = some after)
    (row : OpenResponsibilityAt N (living.toAuthoritativeRoot.toRoot.supportAt visit.current)) :
    LedgerEntryEvolutionAt N row (living.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext nextEq row) := by
  generalize chosen : Boundary.continuing living.toAuthoritativeRoot.toLedgerRoot nextEq = actual
  have same : actual.targetCurrent = after := Option.some.inj (actual.next_eq.symm.trans nextEq)
  cases same
  exact (Evolving.nextRow_is_the_canonical_root_destination living visit actual row) ▸
    Evolving.nextReceipt living visit actual row

def actualReceipt (cut : Nat) (original : rows root boundary cut) :
    LedgerEntryEvolutionAt N original (step root boundary cut original) :=
  canonicalReceipt root (.finite (boundary.history.visitAt cut)) (boundary.history.next_eq_at_visit cut) original

def lineageTransformation : diagram root boundary ⟶ (Functor.const ℕ).obj N.Lineage :=
  NatTrans.ofSequence (fun n => TypeCat.ofHom (fun _ : rows root boundary n =>
    N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt n).current))) (by
    intro n
    rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right n 1)) =
      TypeCat.ofHom (step root boundary n) from Functor.ofSequence_map_homOfLE_succ _ n]
    ext original
    exact (actualReceipt root boundary n original).toDebtLineage.lineage_eq.symm)

def lineageCocone : (diagram root boundary).CoconeTypes where
  pt := N.Lineage
  ι cut _ := N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current)
  ι_naturality := by
    intro i j arrow
    funext original
    exact congrArg (fun h : rows root boundary i ⟶ N.Lineage => h original)
      ((lineageTransformation root boundary).naturality arrow)

def lineage : Carrier root boundary → N.Lineage :=
  (diagram root boundary).descColimitType (lineageCocone root boundary)

theorem the_completion_keeps_every_original_source_lineage (cut : Nat) (original : rows root boundary cut) :
    lineage root boundary (includeRow root boundary cut original) =
      N.lineageAt (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
