import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcedInverseSourceFields
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKOutsideCorrectionChildSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution

namespace C
export OriginalKCombReceiptFeedback (Value Var receipt forcedSourceBinding)
end C
namespace P
export OriginalKForcedInverseSourceCalculation
  (Value Var forcingCode correctionRawCode opposite atCoordinate actual_correction_raw_code)
end P
namespace F
export OriginalKForcedInverseSourceWriteback (actualForcing native_environment_source)
end F

private def extract {Y : Unit → Type} (c : BurnolCompletedMellinCoordinate) (side : Fin 2)
    (binding : ∀ target, P.Var target → Expr P.Value Y target)
    {environment : Env P.Value Y} {result : BurnolL2}
    (actual : Trace environment ((P.forcingCode c side).subst binding) (.const result)) :
    Σ point : BurnolL2,
      Trace environment ((P.correctionRawCode (P.opposite side)).subst binding) (.const point) := by
  let outer := Trace.splitAdd actual
  let third := Trace.splitAdd outer.leftTrace
  let second := Trace.splitAdd third.leftTrace
  let first := Trace.splitAdd second.leftTrace
  let subtraction := Trace.splitAdd first.leftTrace
  let negative := originalInput subtraction.rightTrace
  let scaled := originalInput negative.2.1
  let transformed := originalInput scaled.2.1
  exact ⟨transformed.1, transformed.2.1⟩

private theorem split_fourier_equation {Y : Unit → Type} {environment : Env P.Value Y}
    {left right : Expr P.Value Y ()} {result : BurnolL2}
    (actual : Trace environment
      (.add left (.linear fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.toAddMonoidHom right))
      (.const result)) :
    result = (Trace.splitAdd actual).leftValue +
      fourierL2 (originalInput (Trace.splitAdd actual).rightTrace).1 :=
  (Trace.splitAdd actual).total_eq.trans
    (congrArg (fun point => (Trace.splitAdd actual).leftValue + point)
      (originalInput (Trace.splitAdd actual).rightTrace).2.2.down.symm)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "binding" => C.forcedSourceBinding observation nontrivial depth half
private abbrev receiptEnvironment := (C.receipt observation nontrivial depth half).1.environment
local notation "env" => receiptEnvironment observation nontrivial half depth

abbrev motherOccurrence := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
abbrev motherResult := runtimeForcedInverseCalculationResultAt observation nontrivial depth half

def childCode (forcingSide : Fin 2) : Expr C.Value C.Var () :=
  (P.correctionRawCode (P.opposite forcingSide)).subst binding

/-- This is the existing forcing child's history, including a zero scalar multiplier. -/
def actualChild (forcingSide : Fin 2) :
    Σ point : BurnolL2, Trace env
      (childCode observation nontrivial half depth forcingSide) (.const point) :=
  extract c forcingSide binding (F.actualForcing observation nontrivial half depth forcingSide).2

def actualPair (forcingSide : Fin 2) :=
  Trace.splitAdd (actualChild observation nontrivial half depth forcingSide).2

def actualSecond (forcingSide : Fin 2) :=
  originalInput (actualPair observation nontrivial half depth forcingSide).rightTrace

theorem actual_first_binding (forcingSide : Fin 2) :
    (actualPair observation nontrivial half depth forcingSide).leftValue =
      (motherResult observation nontrivial half depth).1.environment () (P.opposite forcingSide,5) :=
  (actualPair observation nontrivial half depth forcingSide).leftTrace.sound.symm

theorem actual_second_binding (forcingSide : Fin 2) :
    (actualSecond observation nontrivial half depth forcingSide).1 =
      (motherResult observation nontrivial half depth).1.environment () (P.opposite forcingSide,6) :=
  (actualSecond observation nontrivial half depth forcingSide).2.1.sound.symm

theorem actual_child_equation (forcingSide : Fin 2) :
    (actualChild observation nontrivial half depth forcingSide).1 =
      (actualPair observation nontrivial half depth forcingSide).leftValue +
        fourierL2 (actualSecond observation nontrivial half depth forcingSide).1 :=
  split_fourier_equation (actualChild observation nontrivial half depth forcingSide).2

theorem actual_child_value (forcingSide : Fin 2) :
    (actualChild observation nontrivial half depth forcingSide).1 =
      OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw
        (P.atCoordinate c (P.opposite forcingSide)) := by
  have value := (actualChild observation nontrivial half depth forcingSide).2.sound.symm
  change (actualChild observation nontrivial half depth forcingSide).1 =
    ((P.correctionRawCode (P.opposite forcingSide)).subst binding).eval env at value
  rw [Expr.eval_subst] at value
  change (actualChild observation nontrivial half depth forcingSide).1 =
    (P.correctionRawCode (P.opposite forcingSide)).eval
      (motherResult observation nontrivial half depth).1.environment at value
  exact value.trans
    ((congrArg (fun originalEnvironment : Env P.Value P.Var =>
      (P.correctionRawCode (P.opposite forcingSide)).eval originalEnvironment)
        (F.native_environment_source observation nontrivial half depth)).trans
      (P.actual_correction_raw_code c _ _ (P.opposite forcingSide)))

/-- Side one of the original forcing supplies the un-conjugated complete correction. -/
def originalChild := actualChild observation nontrivial half depth 1

theorem original_value : (originalChild observation nontrivial half depth).1 =
    OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c :=
  actual_child_value observation nontrivial half depth 1

def conjugateChild := actualChild observation nontrivial half depth 0

theorem conjugate_value : (conjugateChild observation nontrivial half depth).1 =
    OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw
      (OriginalPrimitiveRankBalance.conjugateCoordinate c) :=
  actual_child_value observation nontrivial half depth 0

end OriginalKOutsideCorrectionChildSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
