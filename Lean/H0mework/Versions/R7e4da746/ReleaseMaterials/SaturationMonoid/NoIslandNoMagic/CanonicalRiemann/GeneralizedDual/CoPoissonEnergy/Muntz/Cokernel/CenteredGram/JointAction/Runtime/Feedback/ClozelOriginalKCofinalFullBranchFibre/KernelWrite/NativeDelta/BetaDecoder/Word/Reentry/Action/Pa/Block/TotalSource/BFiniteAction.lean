import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialSemantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteAction
open SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open scoped InnerProductSpace

namespace BF
export OriginalKBFiniteCalculation
  (Value Var E Base code coordinate reader result sourceEnvironment boundaryInputCode jumpCode fixedShift)
end BF
private def retarget {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    {environment : Env Value Var} {raw endpoint : Expr Value Var ()} {value : Value ()}
    (actual : Trace environment raw endpoint) (same : endpoint = .const value) :
    Trace environment raw (.const value) :=
  Eq.mp (congrArg (fun terminal => Trace environment raw terminal) same) actual

private theorem complete_endpoint {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    {environment : Env Value Var} {raw endpoint : Expr Value Var ()} {value : Value ()}
    (actual : Trace environment raw endpoint) (paid : actual.length = remaining raw)
    (read : raw.eval environment = value) : endpoint = .const value := by
  have account := actual.remaining_eq
  have terminal : remaining endpoint = 0 := by omega
  cases endpoint with
  | const result => exact congrArg Expr.const (actual.sound.symm.trans read)
  | var => simp only [remaining] at terminal; omega
  | add => simp only [remaining] at terminal; omega
  | linear => simp only [remaining] at terminal; omega
  | bilinear => simp only [remaining] at terminal; omega

namespace Split
variable (c : BurnolCompletedMellinCoordinate) (h : ℝ)
variable {environment : Env BF.Value BF.Var} {total : BurnolL2}
variable (actual : Trace environment (BF.code c h) (.const total))

def cut := Trace.splitAdd actual
def inputCut := Trace.splitLinear (cut c h actual).leftTrace

def rReceipt : Trace.SourceReceipt actual
    (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom (BF.boundaryInputCode c h)) :=
  ⟨(cut c h actual).leftValue, (cut c h actual).leftTrace, .left (cut c h actual) (.refl _)⟩

def inputReceipt : Trace.SourceReceipt actual (BF.boundaryInputCode c h) :=
  ⟨(inputCut c h actual).input, (inputCut c h actual).trace,
    .left (cut c h actual) (.linear (inputCut c h actual) (.refl _))⟩

def jumpReceipt : Trace.SourceReceipt actual (BF.jumpCode c h) :=
  ⟨(cut c h actual).rightValue, (cut c h actual).rightTrace, .right (cut c h actual) (.refl _)⟩

theorem actual_action :
    (rReceipt c h actual).value = burnolDirectRightResolventCLM c (inputReceipt c h actual).value := by
  have outer := (cut c h actual).leftTrace.sound
  have inner := (inputCut c h actual).trace.sound
  change burnolDirectRightResolventCLM c ((BF.boundaryInputCode c h).eval environment) =
    (cut c h actual).leftValue at outer
  change (BF.boundaryInputCode c h).eval environment = (inputCut c h actual).input at inner
  rw [inner] at outer
  exact outer.symm

theorem actual_sum :
    total = (rReceipt c h actual).value + (jumpReceipt c h actual).value :=
  (cut c h actual).total_eq

theorem source_addresses :
    (rReceipt c h actual).retained.address = [0] ∧
    (inputReceipt c h actual).retained.address = [0, 2] ∧
    (jumpReceipt c h actual).retained.address = [1] := ⟨rfl, rfl, rfl⟩

theorem actual_history :
    actual.length = (inputReceipt c h actual).trace.length +
      (jumpReceipt c h actual).trace.length + 2 := by
  change actual.length = (inputCut c h actual).trace.length +
    (cut c h actual).rightTrace.length + 2
  calc
    actual.length = (cut c h actual).leftTrace.length + (cut c h actual).rightTrace.length + 1 :=
      (cut c h actual).length_eq
    _ = ((inputCut c h actual).trace.length + 1) + (cut c h actual).rightTrace.length + 1 := by
      exact congrArg (fun count => count + (cut c h actual).rightTrace.length + 1)
        (inputCut c h actual).length_eq
    _ = _ := by omega

theorem source_input {total : BurnolL2}
    (actual : Trace BF.sourceEnvironment (BF.code c h) (.const total)) :
    (inputReceipt c h actual).value =
      OriginalKSourceFiniteUpdate.OriginalBFiniteRAction.calculatedBoundaryInput c h := by
  have input := (inputReceipt c h actual).trace.sound
  change (BF.boundaryInputCode c h).eval BF.sourceEnvironment =
    (inputReceipt c h actual).value at input
  exact input.symm.trans (OriginalKBFiniteCalculation.Semantics.boundary_input_code_eval _ _)

theorem source_action {total : BurnolL2}
    (actual : Trace BF.sourceEnvironment (BF.code c h) (.const total)) :
    (rReceipt c h actual).value = burnolDirectRightResolventCLM c
      (OriginalKSourceFiniteUpdate.OriginalBFiniteRAction.calculatedBoundaryInput c h) :=
  (actual_action c h actual).trans
    (congrArg (burnolDirectRightResolventCLM c) (source_input c h actual))

end Split

namespace Source
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
variable {current : CanonicalUnitArithmeticRoot.V.Current}
variable (occurrence : BF.Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)
abbrev sourceResult := BF.result observation nontrivial half occurrence
abbrev sourceCoordinate := BF.coordinate observation nontrivial half occurrence
local notation "material" => sourceResult observation nontrivial half occurrence
local notation "c" => sourceCoordinate observation nontrivial half occurrence

/-- Normalize the endpoint of the given paid trace; no execution is selected. -/
def actualTrace : Trace BF.sourceEnvironment (BF.code c BF.fixedShift) (.const material.2.2.1) :=
  let endpoint := complete_endpoint material.2.1.2
    (OriginalKBFiniteCalculation.result_history observation nontrivial half occurrence)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value BF.Base
      (BF.reader observation nontrivial half) occurrence).symm
  retarget material.2.1.2 endpoint

def rReceipt := Split.rReceipt c BF.fixedShift (actualTrace observation nontrivial half occurrence)
def inputReceipt := Split.inputReceipt c BF.fixedShift (actualTrace observation nontrivial half occurrence)
def jumpReceipt := Split.jumpReceipt c BF.fixedShift (actualTrace observation nontrivial half occurrence)

theorem actual_input :
    (inputReceipt observation nontrivial half occurrence).value =
      OriginalKSourceFiniteUpdate.OriginalBFiniteRAction.calculatedBoundaryInput c BF.fixedShift := by
  exact Split.source_input c BF.fixedShift (actualTrace observation nontrivial half occurrence)

theorem actual_action :
    (rReceipt observation nontrivial half occurrence).value =
      burnolDirectRightResolventCLM c
        (OriginalKSourceFiniteUpdate.OriginalBFiniteRAction.calculatedBoundaryInput c BF.fixedShift) :=
  Split.source_action c BF.fixedShift (actualTrace observation nontrivial half occurrence)

theorem actual_sum :
    material.2.2.1 = (rReceipt observation nontrivial half occurrence).value +
      (jumpReceipt observation nontrivial half occurrence).value :=
  Split.actual_sum _ _ _

end Source
end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

