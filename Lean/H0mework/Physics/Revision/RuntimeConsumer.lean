import H0mework.Physics.Revision.InquiryRuntime

/-! The named inquiry runtime consumes the four whole-field equations and
the actual action descent on its generated target. Coverage retains the old
source's whole-ledger write and its own native next, while the macro action
continues to the material root's separately generated next. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageTenPhysicalRoot

noncomputable section

set_option linter.defProp false in
/-- Consume the named facade's exact old occurrence/ledger coverage and the
installed inquiry compiler in the same proof. Neither next is substituted
for the other. -/
def firstAssembly_action_compilation_factorizes :=
  let coverage := physicalRuntimeFacade.readoutAt_factorizes
    physicalRuntimeAfterGravity RootProjectionCoordinate.cartanAction
  let compiled := cartanInquiryPresentation.state.generatedCompilation_factorizes PUnit.unit
  And.intro coverage compiled

def firstAssembly_activated_cartan_receipt :
    CartanFirstWriteReceiptAt firstAssemblyActionSourceEvent
      Material.firstAssemblyCartanActual :=
  firstAssemblyInquiryTick.receipt.2

theorem firstMaterialInquiryTick_answer :
    firstMaterialInquiryTick.answer = Material.firstAssemblyCartanActual :=
  rfl

theorem firstMaterialInquiryTick_four_channels (point : BasePoint) :
    let residual := diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      firstMaterialInquiryTick.answer point
    residual.gravityMultiplier = 0 ∧ residual.gravityAuxiliary = 0 ∧
      residual.p286GaugeAuxiliary = 0 ∧ residual.lorentzConnection = 0 :=
  ⟨firstAssembly_activated_cartan_receipt.gravityMultiplier point,
    firstAssembly_activated_cartan_receipt.gravityAuxiliary point,
    firstAssembly_activated_cartan_receipt.p286Auxiliary point,
    firstAssembly_activated_cartan_receipt.lorentzConnection point⟩

/-- The actual configuration after the first material step is the root's
computed P286/Cartan write, not a future-state field in the inquiry. -/
theorem firstMaterialInquiryTick_next_configuration :
    materialConfiguration (materialCurrentSupport (materialVisit 2).current) =
      (Reduction.p286CartanStateNext 0 materialInitialState).current :=
  rfl

theorem firstMaterialInquiryTick_active_action_nonpositive :
    Reduction.actualRelativeAction positiveSmoothUnifiedSource
      firstMaterialInquiryTick.answer
      (materialConfiguration (materialCurrentSupport (materialVisit 2).current)) ≤ 0 :=
  Reduction.p286CartanStateNext_action_nonpositive 0 materialInitialState
    Material.firstAssemblyCartanActual_idempotent

theorem materialNativeNext_no_nontrivial_twoCycle
    (returns :
      materialConfiguration (materialCurrentSupport (materialVisit 3).current) =
        firstMaterialInquiryTick.answer) :
    materialConfiguration (materialCurrentSupport (materialVisit 2).current) =
      firstMaterialInquiryTick.answer :=
  Reduction.p286CartanStateNext_no_nontrivial_twoCycle 0 materialInitialState
    Material.firstAssemblyCartanActual_idempotent returns

/-- Six exact activations include the original three writes, the Cartan
action, and two source-native material writes. Fuel is only an observation. -/
def physicalInquirySixActivations :
    SourceNativeInquiryRuntime.HistoryAt physicalInquiryRuntime 6
      physicalInquiryRuntime.initialState :=
  physicalInquiryRuntime.run 6

theorem physicalInquirySixActivations_target :
    (physicalInquiryRuntime.stateAt 6).engine.node.erase =
      (materialInquiryPresentation 2).erase :=
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision
