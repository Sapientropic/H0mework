import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Installation.ActionIncrement
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovationFactory
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Factory.Collapse

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation

open SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationInquiry.Context.Installation
  (executedEnvironmentIncrement executed_increment_eq_difference next_raw_environment_from_executed_increment)

variable {K : Type u} [NormedAddCommGroup K]

namespace Collapse
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
  (collapseValueAddHom collapseValue)
end Collapse

local instance sourceLevelGroups (grade : Nat) (target : J.Slot) :
    AddCommGroup (L.Value (W K) grade target) := L.groups (W K) grade target

private def jointRead (read : J.Orbit →ₗ[ℤ] K) : PairValue (Original K) .joint →+ K :=
  let component : J.Orbit × K →+ K :=
    read.toAddMonoidHom.comp (AddMonoidHom.fst _ _) + AddMonoidHom.snd _ _
  let total : PairValue (Original K) .joint →+ Original K .joint :=
    AddMonoidHom.fst _ _ + AddMonoidHom.snd _ _
  component.comp total

/-- The actual column's measurement consumes the original two grade collapses. -/
def columnRead (read : J.Orbit →ₗ[ℤ] K) (grade : Nat) :
    PairValue (L.Value (W K) grade) .joint →+ K :=
  let collapseBase : PairValue (W K) .joint →+ PairValue (Original K) .joint :=
    Collapse.collapseValueAddHom (W := Original K) 2 .joint
  (jointRead read).comp (collapseBase.comp (Collapse.collapseValueAddHom (W := W K) grade .joint))

private theorem column_read_total (read : J.Orbit →ₗ[ℤ] K) (grade : Nat)
    (old effect : L.Value (W K) grade .joint) :
    columnRead read grade (old,effect) = columnRead read grade (old+effect,0) := by
  cases grade with
  | zero =>
    change W K .joint at old effect
    exact congrArg
      (fun total : W K .joint => jointRead read (Collapse.collapseValue (W := Original K) 1 total))
      (add_zero (old+effect)).symm
  | succ grade =>
    change PairValue (L.Value (W K) grade) .joint at old effect
    exact congrArg
      (fun total : PairValue (L.Value (W K) grade) .joint =>
        jointRead read (Collapse.collapseValue (W := Original K) 2
          (Collapse.collapseValue (W := W K) grade total)))
      (add_zero (old+effect)).symm

variable (read : J.Orbit →ₗ[ℤ] K) (grade : Nat) (frame : Frame (K := K) grade)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current := current))

/-- The located request reads the whole graded source and its effect in the same actual material. -/
def columnActionValue (index : Index grade frame) : PairValue (L.Value (W K) grade) .joint :=
  let request := (requests grade frame).get index
  let material := I.materialAt frame supplied
  let environment := pairEnvironment material.raw.environment (executedEnvironmentIncrement frame supplied)
  (liftExpr request.expression).eval environment

theorem actual_column_action_value (index : Index grade frame) :
    let request := (requests grade frame).get index
    let material := I.materialAt frame supplied
    let before := material.raw.environment
    let increment := executedEnvironmentIncrement frame supplied
    columnActionValue grade frame supplied index =
      (request.expression.eval before,request.expression.effect before increment) := by
  dsimp only [columnActionValue]
  rw [eval_liftExpr]

/-- The original read consumes the old value and generated effect on their own faces. -/
def columnAction (index : Index grade frame) : K × K :=
  let request := (requests grade frame).get index
  let written := columnActionValue grade frame supplied index
  (request.coefficient • columnRead read grade (written.1,0),
   request.coefficient • columnRead read grade (0,written.2))

theorem actual_column_action_components (index : Index grade frame) :
    let request := (requests grade frame).get index
    let material := I.materialAt frame supplied
    let before := material.raw.environment
    let increment := executedEnvironmentIncrement frame supplied
    columnAction read grade frame supplied index =
      (request.coefficient • columnRead read grade (request.expression.eval before,0),
       request.coefficient • columnRead read grade (0,request.expression.effect before increment)) := by
  dsimp only [columnAction]
  rw [actual_column_action_value]

theorem actual_column_from_action (index : Index grade frame) :
    columns read grade frame supplied index =
      (columnAction read grade frame supplied index).1+(columnAction read grade frame supplied index).2 := by
  let request := (requests grade frame).get index
  let material := I.materialAt frame supplied
  let written := columnActionValue grade frame supplied index
  let original := (liftExpr request.expression).eval
    (pairEnvironment material.raw.environment (material.nextRaw.environment-material.raw.environment))
  let measure := columnRead read grade
  have action : original = written := by
    dsimp only [original,written,columnActionValue]
    rw [executed_increment_eq_difference]
  change request.coefficient • measure original =
    request.coefficient • measure (written.1,0)+request.coefficient • measure (0,written.2)
  have split : (written.1,0)+(0,written.2) = written := by
    rw [Prod.mk_add_mk,add_zero,zero_add]
  rw [action,← smul_add,← map_add,split]

/-- The very same located request is evaluated at the literal next source environment. -/
theorem actual_column_reads_next (index : Index grade frame) :
    let request := (requests grade frame).get index
    let material := I.materialAt frame supplied
    columns read grade frame supplied index =
      request.coefficient • columnRead read grade (request.expression.eval material.nextRaw.environment,0) := by
  dsimp only
  let request := (requests grade frame).get index
  let material := I.materialAt frame supplied
  let before := material.raw.environment
  let after := material.nextRaw.environment
  let delta := executedEnvironmentIncrement frame supplied
  have emitted : after = before+delta := next_raw_environment_from_executed_increment frame supplied
  have actualDelta : delta = after-before := executed_increment_eq_difference frame supplied
  change request.coefficient • columnRead read grade
      ((liftExpr request.expression).eval (pairEnvironment before (after-before))) =
    request.coefficient • columnRead read grade (request.expression.eval after,0)
  rw [← actualDelta,eval_liftExpr,column_read_total,← Expr.eval_update,← emitted]

end PaidSourceContentEnvironment.GradedInnovation
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
