import H0mework.Foundation.Arithmetic.RootIncidence
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootCoreRepresentationRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticIncidenceRegression

open ArithmeticGeneration
open RootArithmeticIncidence
open SourceNativeLedgerCompilerRegression
open SourceNativeRootAuthorityRegression
open RootCoreRepresentationRegression

def leftHistory : UnitHistory := UnitHistory.generate 2
def rightHistory : UnitHistory := UnitHistory.generate 3

/-- Parallel incidence is exact while joint incidence exposes the missing
sixth unit as a generated mismatch. -/
def material : RootArithmeticMaterialAt where
  whole := leftHistory.parallel rightHistory
  left := leftHistory
  right := rightHistory

def materialLaw : SourceNativeRootArithmeticMaterialLaw
    livingQuestionWorld.toAuthoritativeRoot.toLedgerRoot.source :=
  .create fun _occurrence => material

def materialAuthority : SourceNativeAuthoritySource N V where
  restructuringSource := livingQuestionWorld.source.base.restructuringSource
  eventInventoryAdmission := livingQuestionWorld.source.base.eventInventoryAdmission
  lawSurface := livingQuestionWorld.source.base.lawSurface
  projectionLaw := materialLaw.toProjectionLaw

def materialLivingSource : SourceNativeLivingAuthoritySource N V where
  base := materialAuthority
  terminalHandoff := materialAuthority.emptyFaithfulTerminalHandoff
    (fun _current => by
      change IsEmpty PEmpty
      infer_instance)

def materialRoot : SourceNativeLivingRootClosure N V where
  source := materialLivingSource
  emitted := livingQuestionWorld.emitted
  compiler_commutes := livingQuestionWorld.compiler_commutes

def materialVisit : SourceNativeTemporalVisitAt
    materialRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite materialRoot.toAuthoritativeRoot.toRoot.initialVisit

def recognition :
    SourceNativeRootArithmeticIncidenceRecognitionAt materialRoot where
  materialLaw := materialLaw
  installation := SourceNativeProjectionLaw.InstallationAt.refl
    materialLaw.toProjectionLaw

def step : RootArithmeticIncidenceStepAt recognition materialVisit :=
  recognition.generateStepAt materialVisit

def nextMaterialVisit : SourceNativeTemporalVisitAt
    materialRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (materialRoot.toAuthoritativeRoot.toRoot.initialVisit.next rfl)

def nextStep : RootArithmeticIncidenceStepAt recognition nextMaterialVisit :=
  recognition.generateStepAt nextMaterialVisit

def materialHistory : ProductiveFiniteRootHistoryAt
    materialRoot.toAuthoritativeRoot.toLedgerRoot where
  currentAt := fun _index => ()
  initial_eq := rfl
  next_eq := fun _index => rfl

def generatedPrefix : RootGeneratedArithmeticPrefixAt
    recognition materialHistory 3 :=
  generateRootArithmeticPrefixAt recognition materialHistory 3

def ParallelIsExact
    {Provenance : Sort _} {provenance : Provenance}
  {material : RootArithmeticMaterialAt}
    (normal : ParallelIncidenceNormalFormAt provenance material) : Prop :=
  match normal with
  | .exact _ _ => True
  | .generatedResidual _ => False

def JointIsResidual
    {Provenance : Sort _} {provenance : Provenance}
  {material : RootArithmeticMaterialAt}
    (normal : JointIncidenceNormalFormAt provenance material) : Prop :=
  match normal with
  | .exact _ _ => False
  | .generatedResidual _ => True

theorem step_material_eq : step.material = material :=
  rfl

theorem parallel_incidence_is_generated_exact :
    ParallelIsExact step.parallelNormalForm := by
  change ParallelIsExact (normalizeParallel step material)
  have commutes : material.whole = material.left.parallel material.right := rfl
  rw [normalizeParallel, dif_pos commutes]
  trivial

theorem joint_mismatch_generates_typed_residual :
    JointIsResidual step.jointNormalForm := by
  change JointIsResidual (normalizeJoint step material)
  have mismatch : material.whole ≠ material.left.joint material.right := by
    decide
  rw [normalizeJoint, dif_neg mismatch]
  trivial

theorem material_is_same_occurrence_installed_face :
    HEq
      (materialRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit)
        step.generated.occurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.generated.occurrence) :=
  step.installedMaterial_factorizes

theorem step_uses_exact_whole_ledger :
    HEq step.wholeLedgerWriteBack
      (materialRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        materialVisit.current) :=
  HEq.rfl

theorem residual_cannot_select_next :
    step.nextCurrent = materialRoot.generatedNextCurrentAt materialVisit :=
  step.nextCurrent_eq

def generatedJointResidual : GeneratedJointResidualAt step step.material :=
  match normal : step.jointNormalForm with
  | .exact _ commutes =>
      False.elim ((by decide :
        material.whole ≠ material.left.joint material.right) commutes)
  | .generatedResidual residual => residual

/-- Even definitionally identical arithmetic material cannot lend one
occurrence's residual to its source-generated successor occurrence. -/
theorem sibling_visit_residual_cannot_replay : True := by
  fail_if_success
    exact (generatedJointResidual :
      GeneratedJointResidualAt nextStep nextStep.material)
  trivial

theorem prefix_row_is_exact_incidence_step (index : Fin 3) :
    generatedPrefix index = recognition.generateStepAt
      (.finite (materialHistory.visitAt index.val)) :=
  rfl

theorem prefix_row_index_is_history_shadow (index : Fin 3) :
    (generatedPrefix index).finiteArithmeticHistory.cardinalShadow =
      index.val :=
  generatedRootArithmeticPrefixAt_shadow_eq
    recognition materialHistory 3 index

theorem prefix_row_reuses_same_ledger_and_next (index : Fin 3) :
    HEq (generatedPrefix index).wholeLedgerWriteBack
        (materialRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (materialHistory.visitAt index.val).current) ∧
      (generatedPrefix index).nextCurrent =
        materialRoot.generatedNextCurrentAt
          (.finite (materialHistory.visitAt index.val)) :=
  ⟨HEq.rfl, rfl⟩

theorem caller_cannot_construct_root_incidence_step : True := by
  fail_if_success
    exact (⟨⟩ : RootArithmeticIncidenceStepAt recognition materialVisit)
  trivial

#print axioms UnitHistory.cardinalShadow_parallel
#print axioms UnitHistory.cardinalShadow_joint
#print axioms UnitHistory.eq_of_cardinalShadow_eq
#print axioms RootArithmeticIncidenceStepAt.installedMaterial_factorizes
#print axioms RootArithmeticIncidenceStepAt.nextCurrent_eq
#print axioms parallel_incidence_is_generated_exact
#print axioms joint_mismatch_generates_typed_residual
#print axioms step_uses_exact_whole_ledger
#print axioms residual_cannot_select_next
#print axioms sibling_visit_residual_cannot_replay
#print axioms generatedRootArithmeticPrefixAt_shadow_eq
#print axioms prefix_row_reuses_same_ledger_and_next

end RootArithmeticIncidenceRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
