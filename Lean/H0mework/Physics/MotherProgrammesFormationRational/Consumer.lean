import H0mework.Physics.MotherProgrammesFormationRational.Assembly

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision StageNineEnrichedProofFreeSource StageNineHolonomicField
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineGravityBianchi
open StageNineDiracDualFormNativeJointResidualCarrier StageNineCClassicalWorldAcceptance
open StageNineDiracDualFormNativeMotherAction MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

theorem assembled_normal (visit : MotherVisit) :
    assembledSource visit = assembledSource (SpinPair.visit (10 + codeOf visit)) := by
  have samples : sampleSource visit = sampleSource (SpinPair.visit (10 + codeOf visit)) := by
    funext slot
    rw [sample_source_readback, sample_source_readback]
    simp only [address, code_at]
  unfold assembledSource sampleTrace
  rw [samples]

/-- The original root advances the bundle address. Each child address still
reads its own complete instruction calculation inside the generated prefix. -/
theorem assembled_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    assembledSource (targetVisit visit) = assembledSource (SpinPair.visit (10 + (codeOf visit + 1))) := by
  rw [assembled_normal (targetVisit visit), code_next visit afterOrigin]

theorem sample_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (slot : Fin 66) :
    sampleSource (targetVisit visit) slot = toSource (materialAt (unpack 66 (codeOf visit + 1) slot)) := by
  rw [sample_source_readback, address, code_next visit afterOrigin]

def fieldAtVisit (visit : MotherVisit) : StageNineHolonomicConfiguration :=
  materialField (assembledSource visit)

def actionAtVisit (visit : MotherVisit) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (assembledSource visit) chart point
    (toContinuumPointField (fieldAtVisit visit) point)

theorem complete_physical_generated (visit : MotherVisit) :
    (fieldAtVisit visit).Smooth ∧ (fieldAtVisit visit).Nondegenerate ∧
      GravityConnectionLorentzAdmissible (fieldAtVisit visit) ∧
      DiracDualFormNativeJointZeroFiber (assembledSource visit) (fieldAtVisit visit) ∧
      DynamicScalarSourceContactAtOrigin (assembledSource visit) (fieldAtVisit visit) :=
  ArbitrarySourceFormation.material_realization _

theorem field_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    fieldAtVisit (targetVisit visit) = materialField (assembledSource (SpinPair.visit (10 + (codeOf visit + 1)))) :=
  congrArg materialField (assembled_next visit afterOrigin)

theorem action_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (chart : StageNineChart) (point : BasePoint) :
    actionAtVisit (targetVisit visit) chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
        (assembledSource (SpinPair.visit (10 + (codeOf visit + 1)))) chart point
        (toContinuumPointField
          (materialField (assembledSource (SpinPair.visit (10 + (codeOf visit + 1))))) point) := by
  unfold actionAtVisit fieldAtVisit
  rw [assembled_next visit afterOrigin]

theorem native_formation (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (chart : StageNineChart) (point : BasePoint) :
    (successor visit).targetCurrent = (targetVisit visit).current ∧
      (successor visit).ledgerEvolution =
        (SpinPair.generatedPatch (Recognition.generated visit).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit (targetVisit visit)) = targetVisit visit ∧
      codeOf (targetVisit visit) = codeOf visit + 1 ∧
      (∀ slot : Fin 66,
        codeOf (sampleVisit (targetVisit visit) slot) = unpack 66 (codeOf visit + 1) slot ∧
        temporalDepth (sampleVisit (targetVisit visit) slot).history ≤ temporalDepth (targetVisit visit).history) ∧
      assembledSource (targetVisit visit) = assembledSource (SpinPair.visit (10 + (codeOf visit + 1))) ∧
      fieldAtVisit (targetVisit visit) =
        materialField (assembledSource (SpinPair.visit (10 + (codeOf visit + 1)))) ∧
      ((fieldAtVisit (targetVisit visit)).Smooth ∧ (fieldAtVisit (targetVisit visit)).Nondegenerate ∧
        GravityConnectionLorentzAdmissible (fieldAtVisit (targetVisit visit)) ∧
        DiracDualFormNativeJointZeroFiber (assembledSource (targetVisit visit)) (fieldAtVisit (targetVisit visit)) ∧
        DynamicScalarSourceContactAtOrigin (assembledSource (targetVisit visit)) (fieldAtVisit (targetVisit visit))) ∧
      actionAtVisit (targetVisit visit) chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
          (assembledSource (SpinPair.visit (10 + (codeOf visit + 1)))) chart point
          (toContinuumPointField
            (materialField (assembledSource (SpinPair.visit (10 + (codeOf visit + 1))))) point) := by
  refine ⟨rfl, target_patch visit, finite_readback _, code_next visit afterOrigin, ?_,
    assembled_next visit afterOrigin, field_next visit afterOrigin, complete_physical_generated _,
    action_next visit afterOrigin chart point⟩
  intro slot
  refine ⟨?_, sample_depth_le _ _⟩
  rw [sample_code, address, code_next visit afterOrigin]

theorem every_rational_source_realized (source : SmoothUnifiedSource)
    (coframe : ∀ direction row column, ∃ value : ℚ,
      (value : ℝ) = source.stageEight.coframeLinearCoefficient direction row column)
    (contact : ∃ value : ℚ, (value : ℝ) = source.continuousContactResidual)
    (chart : StageNineChart) (point : BasePoint) :
    ∃ code,
      assembledSource (SpinPair.visit (10 + code)) = source ∧
      fieldAtVisit (SpinPair.visit (10 + code)) = materialField source ∧
      DiracDualFormNativeJointZeroFiber source (fieldAtVisit (SpinPair.visit (10 + code))) ∧
      actionAtVisit (SpinPair.visit (10 + code)) chart point =
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
          (toContinuumPointField (materialField source) point) := by
  obtain ⟨code, generated⟩ := every_rational_source_generated source coframe contact
  refine ⟨code, generated, congrArg materialField generated, ?_, ?_⟩
  · rw [fieldAtVisit, generated]
    exact ArbitrarySourceFormation.material_joint_zero source
  · unfold actionAtVisit fieldAtVisit
    rw [generated]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RationalSourceFormation
