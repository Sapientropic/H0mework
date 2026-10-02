import H0mework.Versions.R2.Realization.JointEffect.PassiveController

/-!
# Exact rooted passive residual

The passive controller has four negative constructors.  This kernel exposes
only the result selected by `settlePassiveEffect`; terminal and all-generated
branches return no residual.  A low-universe canonical token keeps the full
high-universe residual in its type index, so later generic world machinery can
adjoin one exact coordinate without erasing its provenance or lifting the
whole world universe.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointPassiveEffect

open RootLawDependentJointStateController
open RootLawDependentJointTransition

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def IsPassiveResidualDispositionAt
    {step : StepAt recognition visit} :
    PassiveEffectDispositionAt step → Prop
  | .generatorResidual .. => True
  | .relationResidual .. => True
  | .pairingShapeResidual .. => True
  | .jointResidual .. => True
  | .terminal .. => False
  | .allGenerated .. => False

/-- Exact negative image of the already fixed passive controller. -/
structure RootedPassiveResidualAt
    (step : StepAt recognition visit) : Type (u + 2) where
  private mk ::
  disposition : PassiveEffectDispositionAt step
  exact : disposition = settlePassiveEffect step
  isResidual : IsPassiveResidualDispositionAt disposition

/-- The only public selector.  It runs the canonical controller rather than
accepting a residual constructor from a caller. -/
noncomputable def selectedResidual?
    (step : StepAt recognition visit) :
    Option (RootedPassiveResidualAt step) :=
  match exact : settlePassiveEffect step with
  | .terminal _ => none
  | .generatorResidual successor stepExact coordinate =>
      some ⟨.generatorResidual successor stepExact coordinate,
        exact.symm, True.intro⟩
  | .relationResidual successor stepExact compatible coordinate =>
      some ⟨.relationResidual successor stepExact compatible coordinate,
        exact.symm, True.intro⟩
  | .pairingShapeResidual successor stepExact transition coordinate =>
      some ⟨.pairingShapeResidual successor stepExact transition coordinate,
        exact.symm, True.intro⟩
  | .allGenerated _ _ _ => none
  | .jointResidual successor stepExact transition alignment coordinate
      treeExact coordinateMem =>
      some ⟨.jointResidual successor stepExact transition alignment coordinate
          treeExact coordinateMem,
        exact.symm, True.intro⟩

def RootedPassiveResidualAt.support
    {step : StepAt recognition visit}
    (_residual : RootedPassiveResidualAt step) : N.Support :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (root.emitted visit.current)

theorem RootedPassiveResidualAt.wholeLedger_rooted
    {step : StepAt recognition visit}
    (_residual : RootedPassiveResidualAt step) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.wholeLedgerWriteBack_eq_root

theorem RootedPassiveResidualAt.next_rooted
    {step : StepAt recognition visit}
    (_residual : RootedPassiveResidualAt step) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.nextCurrent_eq_root

/-- Every passive negative constructor is nonterminal and therefore carries
the exact compiler successor selected at this root step. -/
def RootedPassiveResidualAt.successor
    {step : StepAt recognition visit}
    (residual : RootedPassiveResidualAt step) :
    RootLawDependentJointTransition.StepLedgerSuccessorAt step := by
  rcases residual with ⟨disposition, _exact, isResidual⟩
  cases disposition with
  | terminal => exact False.elim isResidual
  | generatorResidual successor => exact successor
  | relationResidual successor => exact successor
  | pairingShapeResidual successor => exact successor
  | allGenerated => exact False.elim isResidual
  | jointResidual successor => exact successor

theorem RootedPassiveResidualAt.successor_exact
    {step : StepAt recognition visit}
    (residual : RootedPassiveResidualAt step) :
    RootLawDependentJointTransition.stepSuccessor? step =
      some residual.successor := by
  rcases residual with ⟨disposition, _exact, isResidual⟩
  cases disposition with
  | terminal => exact False.elim isResidual
  | generatorResidual _ exact _ => exact exact
  | relationResidual _ exact _ _ => exact exact
  | pairingShapeResidual _ exact _ _ => exact exact
  | allGenerated => exact False.elim isResidual
  | jointResidual _ exact _ _ _ _ _ => exact exact

/-- Low-universe coordinate whose index retains the entire exact residual. -/
inductive RootedPassiveResidualTokenAt
    {step : StepAt recognition visit}
    (residual : RootedPassiveResidualAt step) : Type u
  | canonical

namespace RootedPassiveResidualTokenAt

instance instSubsingleton
    {step : StepAt recognition visit}
    (residual : RootedPassiveResidualAt step) :
    Subsingleton (RootedPassiveResidualTokenAt residual) :=
  ⟨by intro left right; cases left; cases right; rfl⟩

def generate
    {step : StepAt recognition visit}
    (residual : RootedPassiveResidualAt step) :
    RootedPassiveResidualTokenAt residual :=
  .canonical

end RootedPassiveResidualTokenAt

end

end RootLawDependentJointPassiveEffect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
