import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.ActionSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open OriginalRSourceJointContact OriginalKFiniteOrderRelease.UnitPowerJordanSource
namespace C
export CompletedSourceRCalculation (Slot Value Var)
end C
namespace A
export BornRCanonicalMethodRuntime (W X)
end A
namespace Lower
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end Lower
namespace Feed
export SourceInventoryExecutionFeed (Inventory Request receipt receipt_cost)
export SourceInventoryExecutionFeed.AdmissionReceipt (GeneratorOccurrence generatorRequest generator_request_member generatorReceipt)
end Feed
local instance levelGroups (n : Nat) : ∀ s, AddCommGroup (Lower.Value A.W n s) :=
  Lower.groups A.W n

private def firstDelta : BurnolL2 →+ C.Value .branches where
  toFun := fun value => ((value,0),(0,0))
  map_zero' := rfl
  map_add' := by intro left right; simp only [Prod.mk_add_mk,zero_add]
private def secondDelta : BurnolL2 →+ C.Value .branches where
  toFun := fun value => ((0,value),(0,0))
  map_zero' := rfl
  map_add' := by intro left right; simp only [Prod.mk_add_mk,zero_add]
private def firstSource : BurnolL2 →+ C.Value .branches where
  toFun := fun value => ((0,0),(value,0))
  map_zero' := rfl
  map_add' := by intro left right; simp only [Prod.mk_add_mk,zero_add]
private def secondSource : BurnolL2 →+ C.Value .branches where
  toFun := fun value => ((0,0),(0,value))
  map_zero' := rfl
  map_add' := by intro left right; simp only [Prod.mk_add_mk,zero_add]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
variable {input : C.Value .branches}

/-- These are the two actual operations before any pairing or bill equality is read. -/
def coactionNode (data : ActionMaterial observation nontrivial half input) : Expr C.Value C.Var .physical :=
  Expr.linear (s := .physical) (sourceStep c).toLinearMap.toAddMonoidHom (.const data.cotest)
def stockNode (data : ActionMaterial observation nontrivial half input) : Expr C.Value C.Var .physical :=
  Expr.linear (s := .physical) (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom (.const data.native.source.1.1)

def expression (data : ActionMaterial observation nontrivial half input) : Expr C.Value C.Var .branches :=
  .add
    (Expr.linear (s := .physical) firstDelta (.add (coactionNode observation nontrivial half data)
      (Expr.linear (s := .physical) (-AddMonoidHom.id BurnolL2) (.const data.cotest))))
    (.add
      (Expr.linear (s := .physical) secondDelta (.add (stockNode observation nontrivial half data)
        (Expr.linear (s := .physical) (-AddMonoidHom.id BurnolL2) (.const data.native.source.1.1))))
      (.add (Expr.linear (s := .physical) firstSource (.const data.cotest))
        (Expr.linear (s := .physical) secondSource (.const data.native.source.1.1))))

theorem expression_positions (data : ActionMaterial observation nontrivial half input) :
    expression observation nontrivial half data =
    .add (Expr.linear (s := .physical) firstDelta (.add
      (Expr.linear (s := .physical) (sourceStep c).toLinearMap.toAddMonoidHom (.const data.cotest))
      (Expr.linear (s := .physical) (-AddMonoidHom.id BurnolL2) (.const data.cotest))))
    (.add (Expr.linear (s := .physical) secondDelta (.add
      (Expr.linear (s := .physical) (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom (.const data.native.source.1.1))
      (Expr.linear (s := .physical) (-AddMonoidHom.id BurnolL2) (.const data.native.source.1.1))))
    (.add (Expr.linear (s := .physical) firstSource (.const data.cotest)) (Expr.linear (s := .physical) secondSource (.const data.native.source.1.1)))) := rfl

theorem expression_read (data : ActionMaterial observation nontrivial half input) (environment : Env C.Value C.Var) :
    (expression observation nontrivial half data).eval environment =
      ((sourceStep c data.cotest - data.cotest,
        burnolDirectRightResolventCLM c data.native.source.1.1 - data.native.source.1.1),
       (data.cotest,data.native.source.1.1)) := by
  simp only [expression,coactionNode,stockNode,Expr.eval,firstDelta,secondDelta,firstSource,secondSource,
    AddMonoidHom.coe_mk,ZeroHom.coe_mk,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,
    Prod.mk_add_mk,zero_add,add_zero,sub_eq_add_neg]
  rfl

theorem material_actions (data : ActionMaterial observation nontrivial half input) :
    sourceStep c data.cotest = data.nextCotest ∧
    burnolDirectRightResolventCLM c data.native.source.1.1 = data.native.fullR.1.1 := by
  constructor
  · rw [data.cotest_source,data.next_source,gammaField]
  · exact data.native.physical.whole_actual.symm.trans data.native.physical_R

def atGrade (data : ActionMaterial observation nontrivial half input) :
    (n : Nat) → Expr (Lower.Value A.W n) A.X .branches
  | 0 => liftExpr (expression observation nontrivial half data)
  | n+1 => @liftExpr C.Slot (Lower.Value A.W n) A.X (Lower.groups A.W n) .branches (atGrade data n)

private theorem lift_read {V Y : C.Slot → Type} [∀ s, AddCommGroup (V s)]
    {s : C.Slot} (term : Expr V Y s) (environment : Env (PairValue V) Y) :
    ((liftExpr term).eval environment).1 = term.eval (fun t name => (environment t name).1) := by
  exact congrArg Prod.fst (eval_liftExpr term
    (fun t name => (environment t name).1) (fun t name => (environment t name).2))

theorem atGrade_read (data : ActionMaterial observation nontrivial half input)
    (n : Nat) (environment : Env (Lower.Value A.W n) A.X) :
    BornRSealedMethodHistory.wholeProjection n ((atGrade observation nontrivial half data n).eval environment) =
      ((sourceStep c data.cotest - data.cotest,
        burnolDirectRightResolventCLM c data.native.source.1.1 - data.native.source.1.1),
       (data.cotest,data.native.source.1.1)) := by
  induction n with
  | zero => exact (lift_read _ environment).trans (expression_read observation nontrivial half data _)
  | succ n previous =>
    change BornRSealedMethodHistory.wholeProjection n
      (((@liftExpr C.Slot (Lower.Value A.W n) A.X (Lower.groups A.W n) .branches
        (atGrade observation nontrivial half data n)).eval environment).1) = _
    exact (congrArg (BornRSealedMethodHistory.wholeProjection n)
      (lift_read (V := Lower.Value A.W n) (atGrade observation nontrivial half data n) environment)).trans
      (previous _)

private theorem lift_remaining {V Y : C.Slot → Type} [∀ s, AddCommGroup (V s)]
    {s : C.Slot} (term : Expr V Y s) : remaining (liftExpr term) = remaining term := by
  induction term with
  | var name => rfl
  | const value => rfl
  | add left right ihLeft ihRight => simp only [liftExpr,remaining,ihLeft,ihRight]
  | linear operation argument previous => simp only [liftExpr,remaining,previous]
  | bilinear operation left right ihLeft ihRight => simp only [liftExpr,remaining,ihLeft,ihRight]

theorem atGrade_cost (data : ActionMaterial observation nontrivial half input) (n : Nat) :
    remaining (atGrade observation nontrivial half data n) = 13 := by
  induction n with
  | zero => exact (lift_remaining (expression observation nontrivial half data)).trans rfl
  | succ n previous => exact (lift_remaining (V := Lower.Value A.W n)
      (atGrade observation nontrivial half data n)).trans previous

def inventory (data : ActionMaterial observation nontrivial half input) (n : Nat) :
    Feed.Inventory (V := Lower.Value A.W n) (X := A.X) (s := .branches) :=
  .zero (.generator (atGrade observation nontrivial half data n))

def occurrence (data : ActionMaterial observation nontrivial half input) (n : Nat) :
    Feed.GeneratorOccurrence (inventory observation nontrivial half data n) :=
  ⟨[],atGrade observation nontrivial half data n,[],rfl⟩

end CountedPaInitial.BornRNativeGammaInstall.ActionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
