import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

private def successorCertification {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} (law : SourceNativeLedgerRestructuringLaw source)
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {image : SourceNativeLedgerEvolutionAt source occurrence}
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence image)
    (certificate : SourceNativeLedgerRestructuringCertificationAt law image) :
    ExactLedgerRestructuringCertificationAt law occurrence successor.ledgerEvolution := by
  cases image <;> first | exact certificate | exact successor.elim

private def castTargetCertification {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
    {before : N.Support} {after target : N.Support} (same : after = target)
    (evolution : LedgerWriteEvolutionAt N ⟨before⟩ ⟨after⟩)
    (certificate : ExactLedgerRestructuringCertificationAt law occurrence evolution) :
    ExactLedgerRestructuringCertificationAt law occurrence
      (Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt N ⟨before⟩ ⟨support⟩) same) evolution) := by
  cases same
  exact certificate

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def originalCertification (cut : Nat) : ExactLedgerRestructuringCertificationAt (oldLaw root)
    (root.emitted (boundary.history.visitAt cut).current) (originalEvolution root boundary cut) :=
  castTargetCertification (originalTargetSupport root boundary cut) _
    (successorCertification (oldLaw root) (originalSuccessor root boundary cut)
      (root.source.base.restructuringSource.compiler.certifyRestructuring
        (root.emitted (boundary.history.visitAt cut).current)))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
