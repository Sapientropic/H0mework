import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Original
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Members

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

abbrev oldOccurrence (cut : Nat) := root.emitted (boundary.history.visitAt cut).current
abbrev Before (cut : Nat) : CompleteLiveLedgerAt N :=
  ⟨root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current⟩
abbrev After (cut : Nat) : CompleteLiveLedgerAt N :=
  ⟨root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt (cut + 1)).current⟩

def imageOld {support : N.Support} (row : OpenResponsibilityAt N support) (original : (Original root).Obligation) :
    (vocabulary root boundary).Obligation :=
  oldObligation root boundary ⟨oldSupport root boundary support,oldRow root boundary false row⟩ original

theorem imageOld_reads_the_original_metadata {support : N.Support}
    (row : OpenResponsibilityAt N support) (original : (Original root).Obligation) :
    originalAdmission root boundary (imageOld root boundary row original).content = some original := rfl

theorem imageOld_is_the_actual_obligation (cut : Nat) {support : N.Support}
    (row : OpenResponsibilityAt N support) :
    (law root boundary).obligationAt (emitted root boundary (.inl cut)) (oldRow root boundary false row) =
      imageOld root boundary row ((oldLaw root).obligationAt (oldOccurrence root boundary cut) row) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
