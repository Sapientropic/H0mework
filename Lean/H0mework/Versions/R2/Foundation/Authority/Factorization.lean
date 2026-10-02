import H0mework.Versions.R2.Foundation.Authority.Representation

/-!
# Faithful subsystem authority factorization

A faithful process presentation recovers the exact emitted root occurrence.
Every installed subsystem outcome and the living successor are then dependent
readouts of that occurrence's canonical answer-and-next evolution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- A faithful process, its installed subsystem face, and its next current all
factor through the same emitted occurrence of the fixed raw living world. -/
theorem SourceNativeLivingRawWorld.faithfulProcess_installedSubsystemAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (raw : SourceNativeLivingRawWorld N V)
    (commuting : SourceNativeLivingRootCommutingAt raw)
    {process : CausalCore.Process
      (raw.toLivingRoot commuting).toAnswerNextCausalWorld}
    (faithful : CausalCore.FaithfulRealization
      (raw.toLivingRoot commuting).toAnswerNextCausalWorld process)
    (visit : SourceNativeTemporalVisitAt
      (raw.toLivingRoot commuting).toAuthoritativeRoot.toLedgerRoot)
    {component : SourceNativeProjectionLaw
      (raw.toLivingRoot commuting).toAuthoritativeRoot.toLedgerRoot.source}
    (installation : SourceNativeProjectionLaw.InstallationAt component
      (raw.toLivingRoot commuting).toAuthoritativeRoot.source.projectionLaw)
    (projection : component.Projection) :
    let root := raw.toLivingRoot commuting
    let current : SourceNativeLivingRootCausalCurrentAt root := ULift.up visit
    (faithful.occurrencePresentation current).invFun
          (process.emitted current) =
        root.toAnswerNextCausalWorld.emitted current ∧
      process.generate current = root.canonicalCausalAnswerAndNext current ∧
      HEq
        ((process.generate current).generated.projectionOutcome
          (installation.embed projection))
        (component.outcomeAt projection (root.emitted visit.current)) ∧
      (process.generate current).nextCurrent =
        root.generatedNextCurrentAt visit := by
  dsimp only
  have occurrence_eq :=
    (raw.toLivingRoot commuting).faithful_emitted_recovers_answerNext_occurrence
      faithful visit
  have generated_eq :=
    raw.process_generate_eq_canonical commuting process visit
  have factorized :=
    (process.generate (ULift.up visit)).installedSubsystemAuthority_factorizes
      installation projection
  exact ⟨occurrence_eq, generated_eq, factorized.2.1, factorized.2.2⟩

/-- A faithful presentation cannot separate two installed faces of one raw
living world.  Their values, common root occurrence, and successor all remain
the image of the same canonical compiler call. -/
theorem SourceNativeLivingRawWorld.faithfulProcess_installedJointSubsystemAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (raw : SourceNativeLivingRawWorld N V)
    (commuting : SourceNativeLivingRootCommutingAt raw)
    {process : CausalCore.Process
      (raw.toLivingRoot commuting).toAnswerNextCausalWorld}
    (faithful : CausalCore.FaithfulRealization
      (raw.toLivingRoot commuting).toAnswerNextCausalWorld process)
    (visit : SourceNativeTemporalVisitAt
      (raw.toLivingRoot commuting).toAuthoritativeRoot.toLedgerRoot)
    {leftComponent rightComponent : SourceNativeProjectionLaw
      (raw.toLivingRoot commuting).toAuthoritativeRoot.toLedgerRoot.source}
    (leftInstallation : SourceNativeProjectionLaw.InstallationAt
      leftComponent
      (raw.toLivingRoot commuting).toAuthoritativeRoot.source.projectionLaw)
    (rightInstallation : SourceNativeProjectionLaw.InstallationAt
      rightComponent
      (raw.toLivingRoot commuting).toAuthoritativeRoot.source.projectionLaw)
    (left : leftComponent.Projection)
    (right : rightComponent.Projection) :
    let root := raw.toLivingRoot commuting
    let current : SourceNativeLivingRootCausalCurrentAt root := ULift.up visit
    (faithful.occurrencePresentation current).invFun
          (process.emitted current) =
        root.toAnswerNextCausalWorld.emitted current ∧
      process.generate current = root.canonicalCausalAnswerAndNext current ∧
      HEq
        ((process.generate current).generated.installedJointFaceReadout
          leftInstallation rightInstallation left right).1
        (leftComponent.outcomeAt left (root.emitted visit.current)) ∧
      HEq
        ((process.generate current).generated.installedJointFaceReadout
          leftInstallation rightInstallation left right).2
        (rightComponent.outcomeAt right (root.emitted visit.current)) ∧
      (process.generate current).nextCurrent =
        root.generatedNextCurrentAt visit := by
  dsimp only
  have occurrence_eq :=
    (raw.toLivingRoot commuting).faithful_emitted_recovers_answerNext_occurrence
      faithful visit
  have generated_eq :=
    raw.process_generate_eq_canonical commuting process visit
  have factorized :=
    (process.generate (ULift.up visit)).installedJointSubsystemAuthority_factorizes
      leftInstallation rightInstallation left right
  exact
    ⟨occurrence_eq, generated_eq, factorized.2.1, factorized.2.2.1,
      factorized.2.2.2⟩

/-- Every faithful executor of one complete source process factors through
the exact process-state occurrence, installed subsystem face, and
source-generated next living current.

This is the process-level authority firewall: changing an executor's event
carrier may change its presentation, but cannot choose a sibling root,
relabel the installed face, or recanonicalize the successor at a later
state. -/
theorem SourceNativeLivingRootProcess.faithfulProcess_installedSubsystemAuthority_factorizes
    {N : WorldRelationNetwork.{u}}
    (sourceProcess : SourceNativeLivingRootProcess N)
    {process : CausalCore.Process sourceProcess.toAnswerNextCausalWorld}
    (faithful : CausalCore.FaithfulRealization
      sourceProcess.toAnswerNextCausalWorld process)
    (state : sourceProcess.State)
    {component : SourceNativeProjectionLaw
      (sourceProcess.stateAt state).root.toAuthoritativeRoot.toLedgerRoot.source}
    (installation : SourceNativeProjectionLaw.InstallationAt component
      (sourceProcess.stateAt state).root.toAuthoritativeRoot.source.projectionLaw)
    (projection : component.Projection) :
    let current : SourceNativeLivingProcessCausalCurrentAt sourceProcess :=
      ULift.up state
    (faithful.occurrencePresentation current).invFun
          (process.emitted current) =
        sourceProcess.toAnswerNextCausalWorld.emitted current ∧
      process.generate current =
        sourceProcess.canonicalCausalAnswerAndNext current ∧
      HEq
        ((process.generate current).generated.projectionOutcome
          (installation.embed projection))
        (component.outcomeAt projection
          ((sourceProcess.stateAt state).root.emitted
            (sourceProcess.stateAt state).visit.current)) ∧
      (process.generate current).nextCurrent =
        sourceProcess.stateAt (sourceProcess.successor state) := by
  dsimp only
  let presentation := faithful.occurrencePresentation (ULift.up state)
  have occurrence_eq :
      presentation.invFun (process.emitted (ULift.up state)) =
        sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state) := by
    calc
      presentation.invFun (process.emitted (ULift.up state)) =
          presentation.invFun
            (presentation.toFun
              (sourceProcess.toAnswerNextCausalWorld.emitted
                (ULift.up state))) := by
            exact congrArg presentation.invFun
              (faithful.emitted_commutes (ULift.up state)).symm
      _ = sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state) :=
        presentation.left_inv
          (sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state))
  have generated_eq :=
    sourceProcess.process_generate_eq_answerAndNext process state
  have factorized :=
    (process.generate (ULift.up state)).installedSubsystemAuthority_factorizes
      installation projection
  exact ⟨occurrence_eq, generated_eq, factorized.2.1, factorized.2.2⟩

/-- Every faithful executor of a complete source process preserves both
installed faces as one exact coface readout at the process-state occurrence.
Neither face, nor a later carrier rechart, can independently select the
successor. -/
theorem SourceNativeLivingRootProcess.faithfulProcess_installedJointSubsystemAuthority_factorizes
    {N : WorldRelationNetwork.{u}}
    (sourceProcess : SourceNativeLivingRootProcess N)
    {process : CausalCore.Process sourceProcess.toAnswerNextCausalWorld}
    (faithful : CausalCore.FaithfulRealization
      sourceProcess.toAnswerNextCausalWorld process)
    (state : sourceProcess.State)
    {leftComponent rightComponent : SourceNativeProjectionLaw
      (sourceProcess.stateAt state).root.toAuthoritativeRoot.toLedgerRoot.source}
    (leftInstallation : SourceNativeProjectionLaw.InstallationAt
      leftComponent
      (sourceProcess.stateAt state).root.toAuthoritativeRoot.source.projectionLaw)
    (rightInstallation : SourceNativeProjectionLaw.InstallationAt
      rightComponent
      (sourceProcess.stateAt state).root.toAuthoritativeRoot.source.projectionLaw)
    (left : leftComponent.Projection)
    (right : rightComponent.Projection) :
    let current : SourceNativeLivingProcessCausalCurrentAt sourceProcess :=
      ULift.up state
    (faithful.occurrencePresentation current).invFun
          (process.emitted current) =
        sourceProcess.toAnswerNextCausalWorld.emitted current ∧
      process.generate current =
        sourceProcess.canonicalCausalAnswerAndNext current ∧
      HEq
        ((process.generate current).generated.installedJointFaceReadout
          leftInstallation rightInstallation left right).1
        (leftComponent.outcomeAt left
          ((sourceProcess.stateAt state).root.emitted
            (sourceProcess.stateAt state).visit.current)) ∧
      HEq
        ((process.generate current).generated.installedJointFaceReadout
          leftInstallation rightInstallation left right).2
        (rightComponent.outcomeAt right
          ((sourceProcess.stateAt state).root.emitted
            (sourceProcess.stateAt state).visit.current)) ∧
      (process.generate current).nextCurrent =
        sourceProcess.stateAt (sourceProcess.successor state) := by
  dsimp only
  let presentation := faithful.occurrencePresentation (ULift.up state)
  have occurrence_eq :
      presentation.invFun (process.emitted (ULift.up state)) =
        sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state) := by
    calc
      presentation.invFun (process.emitted (ULift.up state)) =
          presentation.invFun
            (presentation.toFun
              (sourceProcess.toAnswerNextCausalWorld.emitted
                (ULift.up state))) := by
            exact congrArg presentation.invFun
              (faithful.emitted_commutes (ULift.up state)).symm
      _ = sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state) :=
        presentation.left_inv
          (sourceProcess.toAnswerNextCausalWorld.emitted (ULift.up state))
  have generated_eq :=
    sourceProcess.process_generate_eq_answerAndNext process state
  have factorized :=
    (process.generate (ULift.up state)).installedJointSubsystemAuthority_factorizes
      leftInstallation rightInstallation left right
  exact
    ⟨occurrence_eq, generated_eq, factorized.2.1, factorized.2.2.1,
      factorized.2.2.2⟩

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
