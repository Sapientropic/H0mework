import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.Relation.Write
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace E
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullRBlockRelationWrite
 (npAction pnAction npSource pnSource np_action_source pn_action_source)
end E

abbrev Value (initial : Nat) := PairValue (PairValue (CodeValue initial))
local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (BaseValue initial t) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (DR.L.Value (BaseValue initial) 2 t) :=
 DR.L.groups (BaseValue initial) 2
local instance codeGroups (initial : Nat) : ∀ t, AddCommGroup (CodeValue initial t) :=
 DR.L.groups (BaseValue initial) 3
local instance valueGroups (initial : Nat) : ∀ t, AddCommGroup (Value initial t) :=
 DR.L.groups (BaseValue initial) 5
local instance valueAddZeroClass (initial : Nat) (t : Unit) : AddZeroClass (Value initial t) :=
 (valueGroups initial t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (initial : Nat) (t : Unit) : AddZero (Value initial t) :=
 (valueAddZeroClass initial t).toAddZero

def liftAction {initial : Nat} (action : CodeValue initial () →+ CodeValue initial ()) :
 Value initial () →+ Value initial () :=
 pairLinear (Value := PairValue (CodeValue initial))
  (pairLinear (Value := CodeValue initial) action)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)

abbrev r := liftAction (DR.completeRSourceAction observation nontrivial half initial 2 0)
abbrev p := liftAction (P.sourcePaLift initial 2 0)
abbrev n := liftAction (P.sourceNonPaLift initial 2 0)
abbrev u := liftAction (E.npSource observation nontrivial half initial)
abbrev v := liftAction (E.pnSource observation nontrivial half initial)

variable (body : Expr (CodeValue initial) C.Var ())

def input : Expr (Value initial) C.Var () := liftExpr (liftExpr body)
def paCode : Expr (Value initial) C.Var () :=
 .linear (s := ()) (t := ()) (r observation nontrivial half initial)
  (.linear (s := ()) (t := ()) (p initial) (input initial body))
def nonPaCode : Expr (Value initial) C.Var () :=
 .linear (s := ()) (t := ()) (r observation nontrivial half initial)
  (.linear (s := ()) (t := ()) (n initial) (input initial body))
def code : Expr (Value initial) C.Var () :=
 .add (paCode observation nontrivial half initial body) (nonPaCode observation nontrivial half initial body)

theorem split_sum (value : Value initial ()) : p initial value + n initial value = value := by
 exact Prod.ext
  (Prod.ext (P.source_lift_split_sum initial 2 0 value.1.1)
   (P.source_lift_split_sum initial 2 0 value.1.2))
  (Prod.ext (P.source_lift_split_sum initial 2 0 value.2.1)
   (P.source_lift_split_sum initial 2 0 value.2.2))

theorem np_source (value : Value initial ()) :
 n initial (r observation nontrivial half initial (p initial value)) = u observation nontrivial half initial value :=
 Prod.ext
  (Prod.ext (DFunLike.congr_fun (E.np_action_source observation nontrivial half initial) value.1.1)
   (DFunLike.congr_fun (E.np_action_source observation nontrivial half initial) value.1.2))
  (Prod.ext (DFunLike.congr_fun (E.np_action_source observation nontrivial half initial) value.2.1)
   (DFunLike.congr_fun (E.np_action_source observation nontrivial half initial) value.2.2))

theorem pn_source (value : Value initial ()) :
 p initial (r observation nontrivial half initial (n initial value)) = v observation nontrivial half initial value :=
 Prod.ext
  (Prod.ext (DFunLike.congr_fun (E.pn_action_source observation nontrivial half initial) value.1.1)
   (DFunLike.congr_fun (E.pn_action_source observation nontrivial half initial) value.1.2))
  (Prod.ext (DFunLike.congr_fun (E.pn_action_source observation nontrivial half initial) value.2.1)
   (DFunLike.congr_fun (E.pn_action_source observation nontrivial half initial) value.2.2))

theorem code_read (environment : Env (Value initial) C.Var) :
 (code observation nontrivial half initial body).eval environment =
 r observation nontrivial half initial ((input initial body).eval environment) := by
 change r observation nontrivial half initial (p initial _) + r observation nontrivial half initial (n initial _) = _
 rw [← map_add, split_sum]

variable (environment : Env (Value initial) C.Var) (total : Value initial ())
variable (actual : Trace environment (code observation nontrivial half initial body) (.const total))

/-- The two R operands are recovered from this exact paid trace. -/
structure TwoAt where
 split : Trace.AddSplit actual
 pa : Trace.LinearSplit split.leftTrace
 nonPa : Trace.LinearSplit split.rightTrace
 paInput : Trace.LinearSplit pa.trace
 nonPaInput : Trace.LinearSplit nonPa.trace

def twoAt : TwoAt observation nontrivial half initial body environment total actual :=
 let split := actual.splitAdd
 let pa := split.leftTrace.splitLinear
 let nonPa := split.rightTrace.splitLinear
 ⟨split,pa,nonPa,pa.trace.splitLinear,nonPa.trace.splitLinear⟩

namespace TwoAt
variable (receipts : TwoAt observation nontrivial half initial body environment total actual)
def paValue := receipts.split.leftValue
def nonPaValue := receipts.split.rightValue
def npValue := n initial receipts.paValue
def pnValue := p initial receipts.nonPaValue

theorem pa_action : receipts.paValue =
 r observation nontrivial half initial (p initial ((input initial body).eval environment)) :=
 completed_trace_value environment receipts.split.leftTrace
theorem nonPa_action : receipts.nonPaValue =
 r observation nontrivial half initial (n initial ((input initial body).eval environment)) :=
 completed_trace_value environment receipts.split.rightTrace

include actual in
theorem full_action : total = r observation nontrivial half initial ((input initial body).eval environment) :=
 (completed_trace_value environment actual).trans (code_read observation nontrivial half initial body environment)
theorem np_unit : receipts.npValue = u observation nontrivial half initial ((input initial body).eval environment) := by
 rw [npValue,receipts.pa_action]
 exact np_source observation nontrivial half initial _
theorem pn_inverse : receipts.pnValue = v observation nontrivial half initial ((input initial body).eval environment) := by
 rw [pnValue,receipts.nonPa_action]
 exact pn_source observation nontrivial half initial _

def pa_retained : Trace.Subtrace actual receipts.split.leftTrace := .left receipts.split (.refl _)
def nonPa_retained : Trace.Subtrace actual receipts.split.rightTrace := .right receipts.split (.refl _)
def pa_input_retained : Trace.Subtrace actual receipts.paInput.trace :=
 .left receipts.split (.linear receipts.pa (.linear receipts.paInput (.refl _)))
def nonPa_input_retained : Trace.Subtrace actual receipts.nonPaInput.trace :=
 .right receipts.split (.linear receipts.nonPa (.linear receipts.nonPaInput (.refl _)))
theorem pa_input_value : receipts.paInput.input = (input initial body).eval environment :=
 completed_trace_value environment receipts.paInput.trace
theorem nonPa_input_value : receipts.nonPaInput.input = (input initial body).eval environment :=
 completed_trace_value environment receipts.nonPaInput.trace
theorem source_occurrences_distinct : receipts.pa_input_retained.address ≠ receipts.nonPa_input_retained.address := by
 change ([0,2,2] : List Nat) ≠ [1,2,2]
 decide
theorem native_length : actual.length = receipts.split.leftTrace.length + receipts.split.rightTrace.length + 1 :=
 receipts.split.length_eq
end TwoAt
end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
