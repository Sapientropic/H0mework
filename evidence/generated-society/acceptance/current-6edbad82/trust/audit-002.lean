import H0mework.Papers.GeneratedSocietyRegeneration
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.PeriodicSameOccurrenceRegenerationAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.PeriodicSameOccurrenceRegenerationCertificate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.RepairRenewalAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceCanonicalRegenerationAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceCanonicalRegenerationCertificate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.SameOccurrenceRegenerationCertificate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegenerationAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_certificate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_nextIsNextStep", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration_certificate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameOccurrenceRegenerationRegression.sameOccurrenceCanonicalRegeneration_directConsumer", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Regeneration.ProofCarryingSameOccurrenceRegenerationRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.CanonicalSocietyAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_periodicSameOccurrenceRegeneration", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_rootLawComplete_and_u8Available", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression"),
    ("SaturationMonoid.ProcessGame.Society.M14WholeProgramRegression.canonicalSociety_sameOccurrenceRegeneration", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.M14WholeProgramRegression"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.RootRestrictedRenewalPayloadAt", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.RootRestrictedRenewalPayloadAt.generate", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.RootAnswerAndNextFactorizes", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.componentOutcome_eq_activePayload", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.generate", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.inactive_noInstalledRenewal", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.localFace", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.localFace_sourceSeed", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.operationalAuthority", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.payload", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.rootAnswerAndNext_factorizes", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.rootResponsibilityConsumer", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceInstalledRenewalAt.temporalSelectedRow", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjection", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.distinctRootOccurrences_generate_distinctSourceSeeds", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.ofRootShell", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalProjectionLaw.toProjectionLaw", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt.componentOutcome_heq_rootOutcome", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRecognitionAt.rootProjection", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.SourceNativeRenewalRootShellAt", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.inheritedByRenewal", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.noInstalledComponent_noSourceInstalledRenewal", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.renewalComponent", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Renewal.withRenewalProjection", "H0mework.Versions.AB.Society.Renewal.InstalledRenewalProjection"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.actualNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.answer", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.finitePrefix", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.generate", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.independentConsumerReceipt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.next_erases_to_generated", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.resolution", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.revisionKind", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.revolutionaryTick?", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomyAt.tick", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalRevisionKind", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryResolutionAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.cofaceFactorizationAndFirstWrite", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWrite", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWriteConsumes", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.firstWriteRealization", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.initialFactorization", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.initialFactorization_unique", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.minimalCoface", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.newRowAnswerAndNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.oldRowAnswerAndNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.resumption", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.revisedNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.rootEntry_eq", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.rooted", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.twoRowAnswerAndNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedRevolutionaryTickAt.twoRows_share_generatedNext", "H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Revision.SourceGeneratedInstitutionalDichotomy"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.ExactFailureSameRowConditionalU8At", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.LawfulPresentationNoWriteAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.branch", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.dispositionExact", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.rooted", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedActionWholeLedgerNextAt.worldWriting", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedDebtAdmissionWholeLedgerNextAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.RootedSequentialActionWholeLedgerNextAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt.installedCompilationFace", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceGeneratedObserverConsumerLegislationAt.submission", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.InstalledActionAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.LawfulPresentationBranchAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.RejectedBranchAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.SameOccurrenceU8At", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.WorldWritingBranchAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.action_u8_disjoint", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.exhaustive_fourClasses", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.installedCompilationFace", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.nonrooted_worldWritingBranch_isEmpty", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.outputMismatch_isEmpty", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.presentation_worldWritingBranch_isEmpty", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.rejection_worldWritingBranch_isEmpty", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.rooted_exhaustive", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.worldWritingBranch_iff_action_or_u8", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeCompiledObserverConsumerLegislationAt.worldWritingBranch_implies_rooted", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt.generate", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerLegislationProgramAt.generatedSubmission", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverConsumerSameOccurrenceLegislationAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeObserverLegislationQuery", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeRootLawCompleteAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.SourceNativeU8AvailableAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.TypedRejectionVisibleResidualAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compileSourceNativeObserverConsumerLegislationAt", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.compiledObserverConsumerLegislation_hasNoFifthClass", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.emptyLocalLedger_sameOccurrenceLegislation_isEmpty", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.rich_exhaustive_fourClasses", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeObserverLegislationQuery", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.SourceNativeObserverConsumerLegislationCompiler"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeRootLawComplete", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion"),
    ("SaturationMonoid.ProcessGame.Society.UniversalRootGrammar.sourceNativeU8Available", "H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "e8a6bbe8da4d9f76ada658fdef5c454d73e4a0cc8eea5f39ef98d43a4b6dda47"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
