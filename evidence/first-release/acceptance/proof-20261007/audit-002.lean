import H0mework.Papers.SourceProcessCoreHRelease
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
  let roots : List (String × String) := [("SaturationMonoid.PhysicsCore.Stage10.GroundedRealization.source_realization_consumed", "H0mework.Physics.MotherSource.GroundedRealization"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.actualDescription", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.actualHistory", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.actual_current", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.actual_history", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.configuration", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.configuration_original", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.current_history", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.source_description_closed", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.CausalCore.FaithfulRealization", "H0mework.Foundation.Semantics.CausalRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.CausalCore.FaithfulRealization.commutingPresentation", "H0mework.Foundation.Semantics.CausalRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.CausalCore.OperationalFaithfulRealization.commutingPresentation", "H0mework.Foundation.Semantics.CausalRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.firstTick_next_is_not_old_micro_successor", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.firstTick_next_uses_exact_revised_living_root", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.firstTick_resolution_is_revised", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.oneShot_has_no_autonomous_runtime", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.secondTick_is_revised_root_answer", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalInquiryRuntimeRegression.threeTickHistory", "H0mework.Checks.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationWorld.DebtActivationLaw", "H0mework.Foundation.Responsibility.DebtWorld"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationWorld.activeInventoryPresentation", "H0mework.Foundation.Responsibility.DebtWorldReadback"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationWorld.active_debt_row_unique", "H0mework.Foundation.Responsibility.DebtWorldReadback"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationWorld.extendedNetwork", "H0mework.Foundation.Responsibility.DebtWorld"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationWorld.inactiveInventoryPresentation", "H0mework.Foundation.Responsibility.DebtWorldReadback"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.compiled_next", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.event_eq_emitted", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.grounded_iff_represented_difference", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.recover_eq_generated", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.recovered_projection", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.source_generates_faithful_realization", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.GroundedFaithfulRealization.source_generates_unique_comparison", "H0mework.Realization.SourceComparison.GroundedRealization"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockNativeConsumer.native_field_factorizes", "H0mework.Fock.Cofinal.OperationNative"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockNativeConsumer.native_readout_is_original_write_target", "H0mework.Fock.Cofinal.OperationNative"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOccurrenceDebtU7LivingRoot.recurrenceMinimalCoface", "H0mework.Arithmetic.FockResponsibility.DebtU7LivingRoot"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOccurrenceDebtU7LivingRoot.rootedRecurrenceFailure", "H0mework.Arithmetic.FockResponsibility.DebtU7LivingRoot"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation.stageDerivation", "H0mework.Fock.Cofinal.OperationDerivation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation.stage_derivation_factorizes", "H0mework.Fock.Cofinal.OperationDerivation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation.stage_state_from_derivation", "H0mework.Fock.Cofinal.OperationDerivation"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics.extendWitness", "H0mework.Fock.Cofinal.DynamicsWitness"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics.extension_factorizes", "H0mework.Fock.Cofinal.DynamicsWitness"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix.completion_word_factorizes", "H0mework.Fock.Cofinal.OperationPrefix"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.Actuality", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.Law", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.LowerCurrent", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.LowerRoot", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.OpenState", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.compiled", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.compiledAuditAt", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.compiled_disposition_eq_source", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.generateObstructionAudit", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.liveDebtEntry_budget", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.liveDebtEntry_claim", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.lowerOccurrence_eq_actualitySource", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.no_ordinary_installation", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.oldU7Calculus", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.open_step_isEmpty_of_residual", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.open_supportTerminal_isEmpty", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.source", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityDirectResponsibility.translatedDispositionAt", "H0mework.Arithmetic.FockResponsibility.DirectResponsibility"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityTargetSixActionDebt.positive", "H0mework.Arithmetic.FockResponsibility.TargetSixActionDebt"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityTargetSixActionDebt.source", "H0mework.Arithmetic.FockResponsibility.TargetSixActionDebt"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityTargetSixActionDebt.targetSixWholeLedgerTerminal", "H0mework.Arithmetic.FockResponsibility.TargetSixActionDebt"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockPrimePairActualityTargetSixActionDebt.wholeLedgerStep", "H0mework.Arithmetic.FockResponsibility.TargetSixActionDebt"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.GeneratedMinimalCofaceAt.oldTheoremSurvival", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.GeneratedMinimalCofaceAt.translation", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.GeneratedMinimalCofaceAt.worldNetwork", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.RelativeExpressiveCapacity.compose_embed_associates", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.minimal_coface_factorization_unique", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.minimal_coface_initial", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ObstructionGeneratedMinimalCoface.root_obstruction_generates_minimal_coface", "H0mework.Foundation.Inquiry.MinimalCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedCausalResidualAudit.siblingOrigin_isEmpty", "H0mework.Realization.JointEffect.AuditTransitionRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationDirect.CompiledResultAt", "H0mework.Foundation.Responsibility.DebtCompiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationDirect.OccurrenceIndexedSourceAt", "H0mework.Foundation.Responsibility.DebtCompiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationDirect.OccurrenceIndexedSourceAt.liveLedger", "H0mework.Foundation.Responsibility.DebtCompiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationDirect.compile", "H0mework.Foundation.Responsibility.DebtCompiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedResidualAdmission.claimLift_unique", "H0mework.Foundation.Inquiry.ResidualCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedResidualAdmission.extendedNetwork", "H0mework.Foundation.Inquiry.ResidualCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedResidualAdmission.residualFailure", "H0mework.Foundation.Inquiry.ResidualCoface"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt.eq_tick", "H0mework.Foundation.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.State.tick", "H0mework.Foundation.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.initialState", "H0mework.Foundation.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.stateAt", "H0mework.Foundation.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryRuntime.stateAt_succ_activation", "H0mework.Foundation.Runtime.Inquiry"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryU8CompletionRegression.generatedCompletion", "H0mework.Checks.Runtime.U8Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryU8CompletionRegression.generatedRevisionCore", "H0mework.Checks.Runtime.U8Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryU8CompletionRegression.generatedTypedRevision", "H0mework.Checks.Runtime.U8Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryU8CompletionRegression.process", "H0mework.Checks.Runtime.U8Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryU8CompletionRegression.public_old_new_rows_generate_same_next", "H0mework.Checks.Runtime.U8Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.SourceGeneratedPassiveResidualAuditTransitionAt.causal_transition_mouth", "H0mework.Realization.JointEffect.AuditTransition"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.generatedPassiveCausalAudit_rejects_sibling_origin", "H0mework.Realization.JointEffect.AuditTransitionRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.installedAuthority_factorizes", "H0mework.Realization.JointEffect.PassiveController"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.selectedResidual?", "H0mework.Realization.JointEffect.Residual"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootLawDependentJointPassiveEffect.settlePassiveEffect", "H0mework.Realization.JointEffect.PassiveController"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootProcessTotalReality.isTotal", "H0mework.Foundation.Semantics.RootReality"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootProcessTotalReality.registeredCurrent_ne_of_ne", "H0mework.Foundation.Semantics.RootReality"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootTotalReality.isTotal", "H0mework.Foundation.Semantics.RootReality"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeBinary.joint", "H0mework.Realization.Operations.BinaryInputs"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeBinary.lift", "H0mework.Realization.Operations.BinaryInputs"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeBinary.pushJoint", "H0mework.Realization.Operations.BinaryInputs"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeLivingRootClosure.generatedNextCurrentAt_lawSurface_eq", "H0mework.Foundation.Cofinal.TemporalAnswer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeLivingRootProcess.generateHistory", "H0mework.Foundation.Runtime.AnswerHistory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeLivingRootProcess.successor_difference_reflects_current", "H0mework.Foundation.Runtime.AnswerHistory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeLivingRootProcess.successor_eq", "H0mework.Foundation.Runtime.AnswerHistory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeLivingRootProcess.successor_lawSurface_eq", "H0mework.Foundation.Runtime.AnswerHistory"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeNoetherianDebtClosureLaw.generatedHistory", "H0mework.Foundation.Responsibility.NoetherianClosure"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeNoetherianDebtClosureLaw.generatedReceipt", "H0mework.Foundation.Responsibility.NoetherianClosure"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativeNoetherianDebtClosureLaw.generatedSettlement", "H0mework.Foundation.Responsibility.NoetherianClosure"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativePaidRootDebtMacroContinuationAt.ofPayment", "H0mework.Foundation.Responsibility.NoetherianClosure"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceNativePaidRootDebtMacroContinuationAt.strictDebit", "H0mework.Foundation.Responsibility.NoetherianClosure"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Field.nativeReadWitness", "H0mework.Realization.Operations.FieldInputs"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Field.nextWitness", "H0mework.Realization.Operations.FieldInputs"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.observer_unique", "H0mework.Realization.Operations.NativeState"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.point_factorizes", "H0mework.Realization.Operations.NativeState"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.sourceAction", "H0mework.Realization.Operations.NativeState"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.statePoint_injective", "H0mework.Realization.Operations.NativeState"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.completion_fibre_generated", "H0mework.Realization.Operations.RuntimeRelations"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.dropFirst", "H0mework.Realization.Operations.RuntimeSuccessor"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.stageInventory_next_old", "H0mework.Realization.Operations.RuntimeEvolution"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.stageRead_next_old", "H0mework.Realization.Operations.RuntimeEvolution"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.successor", "H0mework.Realization.Operations.RuntimeSuccessor"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.successor_fibre_generated", "H0mework.Realization.Operations.RuntimeRelations"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationRuntime.successor_old_eq_old_add_effect", "H0mework.Realization.Operations.RuntimeEvolution"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.TypedSemanticWorldNetworkU8.GeneratedTypedSemanticWorldNetworkRevisionAt.factorizesThroughInitialCoface", "H0mework.Foundation.Inquiry.SemanticRevision"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.TypedSemanticWorldNetworkU8.GeneratedTypedSemanticWorldNetworkRevisionAt.successiveWholeNetworkCapacities", "H0mework.Foundation.Inquiry.SemanticRevision"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.TypedSemanticWorldNetworkU8Recovery.factorizesThroughInitialCofaceAnswerAndNext", "H0mework.Foundation.Inquiry.RevisionRecovery"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.generated_noetherianDebtSettlementReceipt", "H0mework.Foundation.Responsibility.NoetherianClosureRegression"),
    ("SaturationMonoid.ResponsibilityLifecycle.NativeResponsibilityProcess.Edge.disappears_implies_obligationTerminal", "H0mework.Foundation.Responsibility.Lifecycle"),
    ("SaturationMonoid.ResponsibilityLifecycle.NativeResponsibilityProcess.Edge.freshlyAllocated_implies_admitted", "H0mework.Foundation.Responsibility.Lifecycle"),
    ("SaturationMonoid.ResponsibilityLifecycle.NativeResponsibilityProcess.Edge.newlyLive_implies_admitted_or_reopened", "H0mework.Foundation.Responsibility.Lifecycle"),
    ("SaturationMonoid.ResponsibilityLifecycle.NativeResponsibilityProcess.GeneratedState.history_eq", "H0mework.Foundation.Responsibility.Lifecycle"),
    ("SaturationMonoid.ResponsibilityLifecycle.NativeResponsibilityProcess.Run.history_eq", "H0mework.Foundation.Responsibility.Lifecycle"),
    ("SaturationMonoid.SourceOperationDerivations.Controls.actual_increment_changes_generated_relation_range", "H0mework.Checks.Realization.OperationDerivations"),
    ("SaturationMonoid.SourceOperationDerivations.Controls.generated_square_add_readback", "H0mework.Checks.Realization.OperationDerivations"),
    ("SaturationMonoid.SourceOperationDerivations.Derivation.normalize", "H0mework.Realization.Operations.DerivationReduction"),
    ("SaturationMonoid.SourceOperationDynamics.Controls.ScalarWord", "H0mework.Checks.Realization.QuantifiedUpdate"),
    ("SaturationMonoid.SourceOperationDynamics.Controls.actual_joint_witnesses_branch_from_one_old_scope", "H0mework.Checks.Realization.QuantifiedUpdate"),
    ("SaturationMonoid.SourceOperationDynamics.Controls.equal_middle_shadows_do_not_supply_a_single_history_source", "H0mework.Checks.Realization.QuantifiedUpdate"),
    ("SaturationMonoid.SourceOperationDynamics.Controls.variableWord", "H0mework.Checks.Realization.QuantifiedUpdate"),
    ("SaturationMonoid.SourceOperationEffects.Expr.effect", "H0mework.Realization.Operations.Effects"),
    ("SaturationMonoid.SourceOperationEffects.Expr.eval_update", "H0mework.Realization.Operations.Effects"),
    ("SaturationMonoid.SourceOperationEffects.Expr.eval_update_mixedTerms", "H0mework.Realization.Operations.MixedTrace"),
    ("SaturationMonoid.SourceOperationScalarInventoryLift.evaluation_liftMap", "H0mework.Realization.Operations.InventoryLift"),
    ("SaturationMonoid.SourceOperationScalarInventoryLift.pairEnvironment", "H0mework.Realization.Operations.InventoryLift"),
    ("SaturationMonoid.SourceOperationScalarPresentation.inventory_fibre_generated", "H0mework.Realization.Operations.ScalarExact"),
    ("SaturationMonoid.SourceOperationScalarPresentation.normalizationCertificate", "H0mework.Realization.Operations.ScalarPresentation"),
    ("SaturationMonoid.SourceOperationScalarPresentation.presentationComplex_exact", "H0mework.Realization.Operations.ScalarExact"),
    ("SaturationMonoid.SourceOperationScalarPresentation.relation_range_eq_kernel", "H0mework.Realization.Operations.ScalarPresentation")]
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
    ("token", toJson "c41823f35ea469243fa67e69c1177f56c0e249432c8c7ea22b071538f99de1f5"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
