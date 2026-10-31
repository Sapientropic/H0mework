import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Universal
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

/-- A completion readout of this same actual boundary. This component does
not issue ledger authority or replace the source's landing compiler. -/
def component : SourceNativeProjectionLaw root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Carrier root boundary → N.Claim × Nat
  project := fun _ {_} _ _ point => (claim root boundary point,budget root boundary point)

def recordedRoot := root.withProjectionCoface (component root boundary)

def face : SourceNativeRootSemanticFaceAt (recordedRoot root boundary) (.cofinal boundary) where
  projection := .component PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem the_actual_root_reads_each_original_claim_and_its_attained_budget
    (cut : Nat) (original : rows root boundary cut) :
    (face root boundary).rootRead (includeRow root boundary cut original) =
      (original.claim,minimumBudget root boundary cut original) := rfl

theorem no_completed_root_readout_has_a_fictitious_original_source (point : Carrier root boundary) :
    ∃ cut original, includeRow root boundary cut original = point ∧
      (face root boundary).rootRead point = (original.claim,original.progressBudget) := by
  obtain ⟨cut,original,rfl,attained⟩ :=
    every_completed_budget_is_attained_in_the_original_actual_past root boundary point
  refine ⟨cut,original,rfl,?_⟩
  change (original.claim,budget root boundary (includeRow root boundary cut original)) = _
  exact Prod.ext rfl attained.symm

theorem completion_preserves_the_same_original_event :
    (recordedRoot root boundary).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (.cofinal boundary) =
      root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (.cofinal boundary) := rfl

theorem completion_preserves_the_whole_ledger_write_and_source_next :
    HEq ((recordedRoot root boundary).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.cofinal boundary)).wholeLedgerWriteBack
      ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (.cofinal boundary)).wholeLedgerWriteBack) ∧
    ((recordedRoot root boundary).toAuthoritativeRoot.toRoot.evolutionAt boundary.current).nextCurrent? =
      (root.toAuthoritativeRoot.toRoot.evolutionAt boundary.current).nextCurrent? := ⟨HEq.rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion
