import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticCompletionRegression
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootArithmeticProcessKernel

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticProcessRegression

open ArithmeticProcess
open RootArithmeticCompletion
open RootArithmeticCompletionRegression
open RootArithmeticIncidence
open RootArithmeticIncidenceRegression
open RootArithmeticProcess

def process : RootGeneratedArithmeticProcessAt completion :=
  sourceGeneratedRootArithmeticProcess completion

def normalFormFace : RootArithmeticProcessNormalFormAt process :=
  process.normalFormFace

theorem closure_history_is_actual_extension :
    normalFormFace.closureHistory =
      [.base, .extend] :=
  rfl

theorem derived_history_ends_in_ledger_debit :
    normalFormFace.stageHistory.getLast? =
      some ArithmeticProcessStage.ledgerDebit :=
  process.derivedProcess.history_getLast?

theorem normal_form_is_generated_material_process :
    normalFormFace.readout =
      .ledgerDebit
        (.jointInteraction
          (.material step.material.left)
          (.material step.material.right))
        (.material step.material.whole) :=
  rfl

theorem process_folding_is_lossless :
    normalFormFace.readout.toOccurrence =
      completion.derivedOccurrence.occurrence :=
  normalFormFace.readout_toOccurrence

theorem process_preserves_euler_shadow :
    normalFormFace.readout.eulerShadow = -1 := by
  decide

theorem process_has_five_generated_local_stages :
    normalFormFace.stageHistory.length = 5 :=
  rfl

theorem process_preserves_whole_ledger_and_next :
    HEq normalFormFace.wholeLedgerWriteBack
        completion.wholeLedgerWriteBack ∧
      normalFormFace.nextCurrent = completion.nextCurrent :=
  ⟨HEq.rfl, rfl⟩

def nextJointResidual :
    GeneratedJointResidualAt nextStep nextStep.material :=
  match normal : nextStep.jointNormalForm with
  | .exact _ commutes =>
      False.elim ((by decide :
        material.whole ≠ material.left.joint material.right) commutes)
  | .generatedResidual residual => residual

def nextDirection : GeneratedArithmeticClosureDirectionAt nextStep :=
  .joint nextJointResidual

def nextCompletion :
    RootArithmeticCompletionReceiptAt nextStep nextDirection :=
  sourceGeneratedMinimalClosure nextDirection

def nextProcess : RootGeneratedArithmeticProcessAt nextCompletion :=
  sourceGeneratedRootArithmeticProcess nextCompletion

theorem caller_cannot_construct_root_process : True := by
  fail_if_success
    exact (⟨⟩ : RootGeneratedArithmeticProcessAt completion)
  trivial

theorem caller_cannot_construct_normal_form_face : True := by
  fail_if_success
    exact (⟨⟩ : RootArithmeticProcessNormalFormAt process)
  trivial

theorem sibling_visit_process_cannot_replay : True := by
  fail_if_success
    exact (process : RootGeneratedArithmeticProcessAt nextCompletion)
  trivial

#print axioms ArithmeticProcess.normalize_toOccurrence
#print axioms ArithmeticProcess.normalize_injective
#print axioms ArithmeticProcess.normalize_eulerShadow
#print axioms ArithmeticProcess.normalize_determinantShadow
#print axioms ArithmeticProcess.historyCost_cardinalShadow
#print axioms ArithmeticProcess.SourceGeneratedArithmeticProcessAt.unique
#print axioms ArithmeticProcess.SourceGeneratedFreeClosureProcessAt.unique
#print axioms RootGeneratedArithmeticProcessAt.unique
#print axioms RootArithmeticProcessNormalFormAt.unique
#print axioms RootArithmeticProcessNormalFormAt.readout_toOccurrence
#print axioms RootGeneratedArithmeticProcessAt.nextCurrent_eq
#print axioms process_folding_is_lossless
#print axioms process_preserves_euler_shadow
#print axioms process_preserves_whole_ledger_and_next
#print axioms sibling_visit_process_cannot_replay

end RootArithmeticProcessRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
