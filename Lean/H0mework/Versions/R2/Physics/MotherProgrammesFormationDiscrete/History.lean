import H0mework.Versions.R2.Physics.MotherProgrammesFormationDiscrete.Code
import H0mework.Versions.R2.Physics.SourceFormation.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision StageNineEnrichedProofFreeSource StageNineHolonomicField
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineGravityBianchi
open StageNineDiracDualFormNativeJointResidualCarrier StageNineCClassicalWorldAcceptance
open StageNineDiracDualFormNativeMotherAction MotherFamilyOccurrence

noncomputable section

def codeOf (visit : MotherVisit) : ℕ := temporalDepth visit.history - originDepth

/-- The original causal trace supplies an address for a finite material
calculation. The decoded instruction word does not replace that causal trace. -/
def sourceAtVisit (visit : MotherVisit) : SmoothUnifiedSource := toSource (materialAt (codeOf visit))

theorem code_at (code : ℕ) : codeOf (SpinPair.visit (10+code)) = code := by
  rw [codeOf, visit_depth, origin_depth]
  omega

theorem code_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    codeOf (targetVisit visit) = codeOf visit + 1 := by
  have depth : temporalDepth (targetVisit visit).history = temporalDepth visit.history + 1 :=
    temporalDepth_next visit.history (successor visit).next_eq
  rw [codeOf, depth, codeOf]
  omega

theorem native_program_next (visit : MotherVisit)
    (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    (successor visit).targetCurrent = (targetVisit visit).current ∧
      (successor visit).ledgerEvolution =
        (SpinPair.generatedPatch (Recognition.generated visit).occurrence).toLedgerWriteEvolution ∧
      SourceNativeTemporalVisitAt.finite (finiteVisit (targetVisit visit)) = targetVisit visit ∧
      sourceAtVisit (targetVisit visit) =
        toSource (execute (programAt (codeOf visit+1)) neutralOrigin) := by
  refine ⟨rfl, target_patch visit, finite_readback _, ?_⟩
  rw [sourceAtVisit, code_next visit afterOrigin]
  rfl

theorem complete_discrete_read (visit : MotherVisit) :
    readMaterial (sourceAtVisit visit) = execute (programAt (codeOf visit)) neutralOrigin :=
  full_material_recovered _

def retainReferenceContinuous (source : SmoothUnifiedSource) : SmoothUnifiedSource :=
  { source with
    stageEight := { source.stageEight with coframeLinearCoefficient := Runtime.source.stageEight.coframeLinearCoefficient }
    continuousContactResidual := Runtime.source.continuousContactResidual }

theorem source_reassembled (source : SmoothUnifiedSource) :
    toSource (readMaterial source) = retainReferenceContinuous source := rfl

/-- Every full discrete material occurs in this history-addressed unit
program family. Only the two explicitly retained continuous fields are fixed. -/
theorem every_source_discrete_generated (source : SmoothUnifiedSource) :
    ∃ code, sourceAtVisit (SpinPair.visit (10+code)) = retainReferenceContinuous source := by
  obtain ⟨code, generated⟩ := every_material_at_code (readMaterial source)
  refine ⟨code, ?_⟩
  rw [sourceAtVisit, code_at, generated, source_reassembled]

theorem original_source_generated : ∃ code, sourceAtVisit (SpinPair.visit (10+code)) = Runtime.source :=
  every_source_discrete_generated Runtime.source

def fieldAtVisit (visit : MotherVisit) : StageNineHolonomicConfiguration :=
  materialField (sourceAtVisit visit)

def actionAtVisit (visit : MotherVisit) (chart : StageNineChart) (point : BasePoint) : ℝ :=
  sourceGeneratedDiracDualFormNativeUnifiedLocalDensity (sourceAtVisit visit) chart point
    (toContinuumPointField (fieldAtVisit visit) point)

theorem complete_physical_generated (visit : MotherVisit) :
    (fieldAtVisit visit).Smooth ∧ (fieldAtVisit visit).Nondegenerate ∧
      GravityConnectionLorentzAdmissible (fieldAtVisit visit) ∧
      DiracDualFormNativeJointZeroFiber (sourceAtVisit visit) (fieldAtVisit visit) ∧
      DynamicScalarSourceContactAtOrigin (sourceAtVisit visit) (fieldAtVisit visit) :=
  ArbitrarySourceFormation.material_realization _

theorem action_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history)
    (chart : StageNineChart) (point : BasePoint) :
    actionAtVisit (targetVisit visit) chart point =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
        (toSource (execute (programAt (codeOf visit+1)) neutralOrigin)) chart point
        (toContinuumPointField
          (materialField (toSource (execute (programAt (codeOf visit+1)) neutralOrigin))) point) := by
  unfold actionAtVisit fieldAtVisit sourceAtVisit
  rw [code_next visit afterOrigin]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.StageEightDiscreteFormation
