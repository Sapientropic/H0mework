import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.WholeLedger
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.UniversalRootGrammar
universe u
noncomputable section
variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  (root : SourceNativeLivingRootClosure N V)

/-- A source-owned read of the existing compiler, adjoined before its
emitter. The root's actual occurrence and whole-ledger source remain exact. -/
def reflectedRoot := root.withProjectionCoface
  (law root.toAuthoritativeRoot.toLedgerRoot.source).toProjectionLaw

def recognition : SourceNativeDependentFaceFamilyRecognitionAt (reflectedRoot root) where
  law := law root.toAuthoritativeRoot.toLedgerRoot.source
  installation := SourceNativeProjectionLaw.InstallationAt.componentCoface root.source.base _

theorem the_installed_readout_keeps_the_exact_original_ledger_root :
    (reflectedRoot root).toAuthoritativeRoot.toLedgerRoot = root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem the_installed_readout_keeps_the_exact_original_law_surface :
    (reflectedRoot root).source.base.lawSurface = root.source.base.lawSurface := rfl

theorem the_installed_readout_keeps_every_original_whole_ledger_write
    (current : V.Current) :
    (reflectedRoot root).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

def inheritedCoordinates : SourceNativeProjectionLaw.InstallationAt root.source.base.projectionLaw
    (reflectedRoot root).source.base.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface root.source.base _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition
