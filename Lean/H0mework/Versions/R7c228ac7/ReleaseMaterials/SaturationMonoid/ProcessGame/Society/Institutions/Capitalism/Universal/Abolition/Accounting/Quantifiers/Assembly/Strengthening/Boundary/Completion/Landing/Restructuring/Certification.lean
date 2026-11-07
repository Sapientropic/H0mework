import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.FiniteCertification
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def evolutionCertification (current : Current) : ExactLedgerRestructuringCertificationAt
    (law root boundary) (emitted root boundary current) (evolution root boundary current) := by
  cases current with
  | inl cut => exact finiteCertification root boundary cut
  | inr phase =>
      cases phase with
      | zero =>
          exact ExactLedgerRestructuringCertificationAt.ofInjective
            (fun _ _ same => same) (fun _ _ same => same)
      | succ _ =>
          exact ExactLedgerRestructuringCertificationAt.ofInjective
            (fun _ _ same => same) (fun _ _ same => same)

def certification {current : Current}
    (occurrence : (source root boundary).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (law root boundary)
      ((ledgerCompiler root boundary).compile occurrence) := by
  rcases occurrence with ⟨support,event⟩
  cases event with
  | finite cut =>
      change ExactLedgerRestructuringCertificationAt (law root boundary) (emitted root boundary (.inl cut)) _
      rw [eq_of_heq (patch_is_the_complete_source_evolution root boundary (.inl cut))]
      exact evolutionCertification root boundary (.inl cut)
  | landing phase =>
      change ExactLedgerRestructuringCertificationAt (law root boundary) (emitted root boundary (.inr phase)) _
      rw [eq_of_heq (patch_is_the_complete_source_evolution root boundary (.inr phase))]
      exact evolutionCertification root boundary (.inr phase)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
