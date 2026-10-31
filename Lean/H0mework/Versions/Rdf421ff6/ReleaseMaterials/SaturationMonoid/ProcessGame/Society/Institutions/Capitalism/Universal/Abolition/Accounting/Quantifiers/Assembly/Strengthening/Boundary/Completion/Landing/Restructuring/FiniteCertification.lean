import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Split
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Merge

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Alignment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def finiteCertification (cut : Nat) : ExactLedgerRestructuringCertificationAt
    (law root boundary) (emitted root boundary (.inl cut))
    (liftLedger root boundary (originalEvolution root boundary cut)) where
  split := by
    intro left right same
    have oldSame := congrArg (readOld root boundary) same
    cases (originalCertification root boundary cut).split
        (readOld root boundary left) (readOld root boundary right) oldSame with
    | identity equal =>
        exact .identity ((oldRow_readOld root boundary left).symm.trans
          ((congrArg (oldRow root boundary false) equal).trans (oldRow_readOld root boundary right)))
    | split covered =>
        have result := splitCoverage root boundary cut covered
        exact .split (alignSplit (oldRow_readOld root boundary left)
          (oldRow_readOld root boundary right) result)
  merge := by
    intro left right same
    have oldSame := congrArg (readOld root boundary) same
    cases (originalCertification root boundary cut).merge
        (readOld root boundary left) (readOld root boundary right) oldSame with
    | identity equal =>
        exact .identity ((oldRow_readOld root boundary left).symm.trans
          ((congrArg (oldRow root boundary false) equal).trans (oldRow_readOld root boundary right)))
    | merge covered =>
        have result := mergeCoverage root boundary cut covered
        exact .merge (alignMerge (oldRow_readOld root boundary left)
          (oldRow_readOld root boundary right) result)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
