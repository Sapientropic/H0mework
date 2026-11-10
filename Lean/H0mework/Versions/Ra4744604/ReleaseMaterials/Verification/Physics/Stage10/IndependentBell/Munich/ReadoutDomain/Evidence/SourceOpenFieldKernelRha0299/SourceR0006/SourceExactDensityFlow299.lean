import H0mework.Versions.R10c4592e.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceNativeKrausWindowRha0292.SourceR0002.SourceNativeKrausWindow292
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Mul

/-! Exact original-source double-leg cells from the Banach linear IVP.
Capture recycling is retained; no Hilbert--Schmidt contraction or completed
flow is an input. The same raw action word acts on the full initial operator.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set
open scoped BigOperators Topology
namespace SourceOpenFieldKernel299
open SourceKrausSurvival285 SourceHiddenWordFlow286 SourceNativeKrausWindow292
open SaturationMonoid.PhysicsCore.StageNineDiracMatterGalerkinEvolution

namespace BanachOperatorFlow

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

private def leftAction (action : B →L[ℂ] B) :
    (B →L[ℂ] B) →L[ℝ] (B →L[ℂ] B) :=
  (ContinuousLinearMap.compL ℂ B B B action).restrictScalars ℝ

omit [CompleteSpace B] in
private theorem leftAction_continuous (action : ℝ → B →L[ℂ] B)
    (continuous : Continuous action) : Continuous (fun time => leftAction (action time)) :=
  (ContinuousLinearMap.restrictScalarsIsometry ℂ
    (B →L[ℂ] B) (B →L[ℂ] B) ℝ ℝ).continuous.comp
    ((ContinuousLinearMap.compL ℂ B B B).continuous.comp continuous)

/-- The existing Banach IVP generates complex-operator flow from identity. -/
def operatorFlow (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) (time : ℝ) : B →L[ℂ] B :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun r => leftAction (action r)) (leftAction_continuous action continuous)
    (1 : B →L[ℂ] B) start finish ordered).choose time

theorem operatorFlow_initial (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) :
    operatorFlow action continuous start finish ordered start = 1 :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun r => leftAction (action r)) (leftAction_continuous action continuous)
    (1 : B →L[ℂ] B) start finish ordered).choose_spec.1

theorem operatorFlow_derivative (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) (time : ℝ) (inside : time ∈ Icc start finish) :
    HasDerivWithinAt (operatorFlow action continuous start finish ordered)
      ((action time).comp (operatorFlow action continuous start finish ordered time))
      (Icc start finish) time :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun r => leftAction (action r)) (leftAction_continuous action continuous)
    (1 : B →L[ℂ] B) start finish ordered).choose_spec.2 time inside

theorem operatorFlow_continuous (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) :
    ContinuousOn (operatorFlow action continuous start finish ordered) (Icc start finish) :=
  fun time inside =>
    (operatorFlow_derivative action continuous start finish ordered time inside).continuousWithinAt

theorem applied_flow_derivative (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) (value : B)
    (time : ℝ) (inside : time ∈ Icc start finish) :
    HasDerivWithinAt (fun r => operatorFlow action continuous start finish ordered r value)
      (action time (operatorFlow action continuous start finish ordered time value))
      (Icc start finish) time := by
  let evaluation : (B →L[ℂ] B) →L[ℝ] B :=
    (ContinuousLinearMap.apply ℂ B value).restrictScalars ℝ
  have derivative :=
    (evaluation.hasFDerivAt (x := operatorFlow action continuous start finish ordered time)).comp_hasDerivWithinAt
      time (operatorFlow_derivative action continuous start finish ordered time inside)
  exact derivative

theorem operatorFlow_unique (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (start finish : ℝ) (ordered : start ≤ finish) (curve : ℝ → B →L[ℂ] B)
    (initial : curve start = 1)
    (evolution : ∀ time ∈ Icc start finish, HasDerivWithinAt curve
      ((action time).comp (curve time)) (Icc start finish) time) :
    EqOn curve (operatorFlow action continuous start finish ordered) (Icc start finish) :=
  galerkinLinearCoefficientCurve_eqOn_Icc
    (fun r => leftAction (action r)) (leftAction_continuous action continuous)
    curve (operatorFlow action continuous start finish ordered) 1 start finish ordered initial
    (operatorFlow_initial action continuous start finish ordered) evolution
    (operatorFlow_derivative action continuous start finish ordered)

end BanachOperatorFlow

abbrev AtomicOperator := AtomicHilbert →L[ℂ] AtomicHilbert
abbrev DensityAction := AtomicOperator →L[ℂ] AtomicOperator

-- Select the existing normed additive/scalar topology without the ring search branch.
private instance densityActionTopologicalAddGroup : IsTopologicalAddGroup DensityAction :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup (E := DensityAction)

private instance densityActionContinuousAdd : ContinuousAdd DensityAction :=
  densityActionTopologicalAddGroup.toContinuousAdd

private instance densityActionContinuousSMulReal : ContinuousSMul ℝ DensityAction := by
  let _ : IsBoundedSMul ℝ DensityAction :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := DensityAction)
  exact IsBoundedSMul.continuousSMul (α := ℝ) (β := DensityAction)

section ExactPrimitiveCell

/-- The scalar exponent is raw source syntax, including its actual retarded offset. -/
structure RawExponential where
  realQuadratic : ℚ
  realLinear : ℚ
  realConstant : ℚ
  imaginaryLinear : ℚ
  imaginaryConstant : ℚ

def RawExponential.value (raw : RawExponential) (time : ℝ) : ℂ :=
  Complex.exp (((raw.realQuadratic : ℂ) * (time : ℂ)^2 +
    (raw.realLinear : ℂ) * (time : ℂ) + (raw.realConstant : ℂ)) +
      Complex.I * ((raw.imaginaryLinear : ℂ) * (time : ℂ) +
        (raw.imaginaryConstant : ℂ)))

theorem RawExponential.continuous (raw : RawExponential) : Continuous raw.value := by
  unfold RawExponential.value
  fun_prop

inductive RawScalar where
  | literal : ComplexLiteral → RawScalar
  | amplitude : NonnegativeRate → RawScalar
  | exponential : RawExponential → RawScalar
  | product : RawScalar → RawScalar → RawScalar
  | conjugate : RawScalar → RawScalar

def RawScalar.value : RawScalar → ℝ → ℂ
  | .literal raw, _ => complexValue raw
  | .amplitude rate, _ => rateAmplitude rate
  | .exponential raw, time => raw.value time
  | .product left right, time => left.value time * right.value time
  | .conjugate raw, time => star (raw.value time)

theorem RawScalar.continuous (raw : RawScalar) : Continuous raw.value := by
  induction raw with
  | literal => exact continuous_const
  | amplitude => exact continuous_const
  | exponential exponent => exact exponent.continuous
  | product left right hl hr => exact hl.mul hr
  | conjugate raw h => exact continuous_star.comp h

structure RawAtomicTerm where
  side : Fin 2
  operator : SparseAtom
  adjoint : Bool
  coefficient : RawScalar

def RawAtomicTerm.value (raw : RawAtomicTerm) (time : ℝ) : AtomicOperator :=
  raw.coefficient.value time •
    (if raw.adjoint then
      (Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)
        (embed raw.side (atomMatrix raw.operator))).adjoint
    else Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)
      (embed raw.side (atomMatrix raw.operator)))

theorem RawAtomicTerm.continuous (raw : RawAtomicTerm) : Continuous raw.value :=
  raw.coefficient.continuous.smul continuous_const

abbrev RawJumpTerms := List RawAtomicTerm

def rawJump (terms : RawJumpTerms) (time : ℝ) : AtomicOperator :=
  (terms.map fun term => term.value time).sum

theorem rawJump_continuous (terms : RawJumpTerms) : Continuous (rawJump terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons term rest h => exact term.continuous.add h

/-- These are precisely the primitive coefficient lists, never completed maps. -/
structure RawCell where
  survivalTerms : List RawAtomicTerm
  survivalIdentity : ℚ
  recycledJumps : List RawJumpTerms

def RawCell.survival (cell : RawCell) (time : ℝ) : AtomicOperator :=
  rawJump cell.survivalTerms time + (cell.survivalIdentity : ℂ) • 1

theorem RawCell.survival_continuous (cell : RawCell) : Continuous cell.survival :=
  (rawJump_continuous cell.survivalTerms).add continuous_const

def bilateral (left right : AtomicOperator) : DensityAction :=
  ((ContinuousLinearMap.compL ℂ AtomicHilbert AtomicHilbert AtomicHilbert).flip
    right.adjoint).comp
      (ContinuousLinearMap.compL ℂ AtomicHilbert AtomicHilbert AtomicHilbert left)

theorem bilateral_apply (left right density : AtomicOperator) :
    bilateral left right density = left * density * right.adjoint := rfl

theorem bilateral_positive (action density : AtomicOperator)
    (positive : density.IsPositive) : (bilateral action action density).IsPositive := by
  change (action.comp (density.comp action.adjoint)).IsPositive
  exact positive.conj_adjoint action

def RawCell.generator (cell : RawCell) (time : ℝ) : DensityAction :=
  bilateral (cell.survival time) 1 + bilateral 1 (cell.survival time) +
    (cell.recycledJumps.map fun terms => bilateral (rawJump terms time) (rawJump terms time)).sum

theorem RawCell.generator_apply (cell : RawCell) (time : ℝ) (density : AtomicOperator) :
    cell.generator time density = cell.survival time * density +
      density * (cell.survival time).adjoint +
        (cell.recycledJumps.map fun terms =>
          rawJump terms time * density * (rawJump terms time).adjoint).sum := by
  have recycled (rows : List RawJumpTerms) :
      (rows.map fun terms => bilateral (rawJump terms time) (rawJump terms time)).sum density =
        (rows.map fun terms =>
          rawJump terms time * density * (rawJump terms time).adjoint).sum := by
    induction rows with
    | nil => rfl
    | cons head rest h =>
      simpa only [List.map_cons, List.sum_cons, add_apply,
        bilateral_apply] using congrArg (fun tail : AtomicOperator =>
          rawJump head time * density * (rawJump head time).adjoint + tail) h
  simp only [RawCell.generator, add_apply, bilateral_apply,
    ContinuousLinearMap.adjoint_one, mul_one, one_mul, recycled]

theorem RawCell.generator_continuous (cell : RawCell) : Continuous cell.generator := by
  have one (left right : ℝ → AtomicOperator) (hl : Continuous left) (hr : Continuous right) :
      Continuous (fun time => bilateral (left time) (right time)) := by
    let compose := ContinuousLinearMap.compL ℂ AtomicHilbert AtomicHilbert AtomicHilbert
    have post : Continuous (fun time => compose.flip (right time).adjoint) :=
      compose.flip.continuous.comp
        ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := AtomicHilbert)
          (F := AtomicHilbert)).continuous.comp hr)
    have pre : Continuous (fun time => compose (left time)) := compose.continuous.comp hl
    exact ((ContinuousLinearMap.compL ℂ AtomicOperator AtomicOperator AtomicOperator).continuous.comp
      post).clm_apply pre
  apply ((one cell.survival (fun _ => 1) cell.survival_continuous continuous_const).add
    (one (fun _ => 1) cell.survival continuous_const cell.survival_continuous)).add
  induction cell.recycledJumps with
  | nil => exact continuous_const
  | cons head rest h =>
    exact (one (rawJump head) (rawJump head) (rawJump_continuous head)
      (rawJump_continuous head)).add h

/-- A raw double-leg generator acts on a Banach space; it is not a Kraus-window input. -/
def RawCell.flow (cell : RawCell) (start finish : ℝ) (ordered : start ≤ finish)
    (time : ℝ) : DensityAction :=
  BanachOperatorFlow.operatorFlow (B := AtomicOperator)
    cell.generator cell.generator_continuous start finish ordered time

theorem RawCell.flow_initial (cell : RawCell) (start finish : ℝ) (ordered : start ≤ finish) :
    cell.flow start finish ordered start = 1 :=
  BanachOperatorFlow.operatorFlow_initial (B := AtomicOperator)
    cell.generator cell.generator_continuous start finish ordered

theorem RawCell.flow_derivative (cell : RawCell) (start finish : ℝ)
    (ordered : start ≤ finish) (time : ℝ) (inside : time ∈ Icc start finish) :
    HasDerivWithinAt (cell.flow start finish ordered)
      ((cell.generator time).comp (cell.flow start finish ordered time))
      (Icc start finish) time :=
  BanachOperatorFlow.operatorFlow_derivative (B := AtomicOperator)
    cell.generator cell.generator_continuous start finish ordered time inside

theorem RawCell.applied_flow_derivative (cell : RawCell) (start finish : ℝ)
    (ordered : start ≤ finish) (density : AtomicOperator) (time : ℝ)
    (inside : time ∈ Icc start finish) :
    HasDerivWithinAt (fun r => cell.flow start finish ordered r density)
      (cell.generator time (cell.flow start finish ordered time density))
      (Icc start finish) time := by
  exact BanachOperatorFlow.applied_flow_derivative (B := AtomicOperator)
    cell.generator cell.generator_continuous start finish ordered density time inside

theorem RawCell.flow_unique (cell : RawCell) (start finish : ℝ) (ordered : start ≤ finish)
    (curve : ℝ → DensityAction) (initial : curve start = 1)
    (evolution : ∀ time ∈ Icc start finish, HasDerivWithinAt curve
      ((cell.generator time).comp (curve time)) (Icc start finish) time) :
    EqOn curve (cell.flow start finish ordered) (Icc start finish) :=
  BanachOperatorFlow.operatorFlow_unique (B := AtomicOperator)
    cell.generator cell.generator_continuous start finish ordered curve initial evolution

theorem RawCell.zero_width (cell : RawCell) (time : ℝ) :
    cell.flow time time le_rfl time = 1 := cell.flow_initial time time le_rfl

end ExactPrimitiveCell

section OriginalActionProgramme

structure RawAtomicFrame where
  omega : Fin 2 → ℚ
  origin : Fin 2 → ℚ
  physicalTimes : Fin 2 → ℝ
  direction : ℤ
  isD2 : AtomIndex → Bool

def RawAtomicFrame.operator (frame : RawAtomicFrame) : AtomicOperator :=
  Matrix.toEuclideanCLM (n := JointIndex) (𝕜 := ℂ)
    (Matrix.diagonal fun coordinate : JointIndex =>
      Complex.exp (Complex.I * (frame.direction : ℂ) *
        ∑ side : Fin 2, (frame.omega side : ℂ) *
          ((frame.physicalTimes side - (frame.origin side : ℝ) : ℝ) : ℂ) *
          (if frame.isD2 (if side = 0 then coordinate.1 else coordinate.2) then 1 else 0)))

inductive RawNode where
  | flow : (cell : RawCell) → (start finish : ℝ) → start ≤ finish → RawNode
  | leftCreation : RawJumpTerms → ℝ → RawNode
  | rightCreation : RawJumpTerms → ℝ → RawNode
  | detector : List RawJumpTerms → ℝ → RawNode
  | birth : List RawJumpTerms → ℝ → RawNode
  | frame : RawAtomicFrame → RawNode
  | weight : NonnegativeRate → RawNode
  | zero : RawNode

def RawNode.action : RawNode → DensityAction
  | .flow cell start finish ordered => cell.flow start finish ordered finish
  | .leftCreation terms time => bilateral (rawJump terms time) 1
  | .rightCreation terms time => bilateral 1 (rawJump terms time)
  | .detector jumps time => (jumps.map fun terms => bilateral (rawJump terms time) (rawJump terms time)).sum
  | .birth jumps time => (jumps.map fun terms => bilateral (rawJump terms time) (rawJump terms time)).sum
  | .frame rawFrame => bilateral rawFrame.operator rawFrame.operator
  | .weight rate => (rate.value : ℂ) • 1
  | .zero => 0

/-- Composition is performed on the still-open full initial operator slot. -/
def run : List RawNode → DensityAction
  | [] => 1
  | node :: rest => (run rest).comp node.action

theorem run_append (before after : List RawNode) :
    run (before ++ after) = (run after).comp (run before) := by
  induction before with
  | nil => ext density; rfl
  | cons node rest h => simp [run, h, ContinuousLinearMap.comp_assoc]

def sameSourceKernel (programme : List RawNode) (density : AtomicOperator) : AtomicOperator :=
  run programme density

theorem sameSourceKernel_add (programme : List RawNode) (left right : AtomicOperator) :
    sameSourceKernel programme (left+right) =
      sameSourceKernel programme left + sameSourceKernel programme right :=
  map_add (run programme) left right

theorem sameSourceKernel_smul (programme : List RawNode) (c : ℂ) (density : AtomicOperator) :
    sameSourceKernel programme (c • density) = c • sameSourceKernel programme density :=
  map_smul (run programme) c density

theorem sameSourceKernel_next (before after : List RawNode) (density : AtomicOperator) :
    sameSourceKernel (before ++ after) density =
      run after (sameSourceKernel before density) :=
  congrArg (fun action : DensityAction => action density) (run_append before after)

end OriginalActionProgramme

end SourceOpenFieldKernel299
