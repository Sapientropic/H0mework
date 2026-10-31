import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Old

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def addedObligation (row : WorldEntry root boundary) : AdmittedObligation (base root boundary) :=
  (show NativeAdmissionPayload (base root boundary) from {
    sourceEvent := .inr row.1
    content := .added row
    residual := .inr PUnit.unit
    bearer := .inr PUnit.unit
    beneficiary := .inr PUnit.unit
    scope := .inr row.1
    lineage := .inr ((W root boundary).lineageAt row.1)
    anchor_scope_eq := rfl
    anchor_lineage_eq := rfl
    origin := .explicitCommitment (PLift.up rfl)
    authority := PLift.up rfl
    assumption := .accepted (PLift.up rfl)
    dischargeJurisdiction := PLift.up rfl }).toObligation

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
