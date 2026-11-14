import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Source
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKAction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Program
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre.KernelWrite
namespace K
export BoundaryNativeKAction (Grade total)
export BoundaryNativeKAction.Program (lift decode lift_total)
end K
namespace Inverse
local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "w" => (Math.weight : ℂ)
local notation "h" => Math.shift

def loop : End := (w⁻¹*w⁻¹) • Math.dilation (-(2*h))

private theorem loop_bound : ‖loop‖ < 1 := by
  have wn : ‖w‖ = Math.weight := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Math.weight_pos]
  have coefficient : ‖w⁻¹*w⁻¹‖ = (Math.weight⁻¹)^2 := by rw [norm_mul, norm_inv, wn]; ring
  have bound : ‖Math.dilation (-(2*h))‖ ≤ 1 :=
    (burnolMultiplicativeDilation (-(2*h))).toLinearIsometry.norm_toContinuousLinearMap_le
  have below : Math.weight⁻¹ < 1 := (inv_lt_one₀ Math.weight_pos).2 Math.weight_gt_one
  have positive : 0 < Math.weight⁻¹ := inv_pos.mpr Math.weight_pos
  have small : ‖loop‖ ≤ (Math.weight⁻¹)^2 := by
    rw [loop, norm_smul, coefficient]
    nlinarith
  exact lt_of_le_of_lt small (by nlinarith)

def unit : Endˣ := Units.oneSub loop loop_bound
def forward : End := w • Math.dilation h
def backward : End := w⁻¹ • Math.dilation (-h)
def operator : End := (↑(unit⁻¹) : End)*backward

private theorem leading_inverse : backward*forward=1 ∧ forward*backward=1 := by
  have nonzero : w ≠ 0 := Complex.ofReal_ne_zero.mpr Math.weight_pos.ne'
  constructor
  · ext1 value
    change w⁻¹ • burnolMultiplicativeDilation (-h) (w • burnolMultiplicativeDilation h value) = value
    rw [map_smul, smul_smul, burnolMultiplicativeDilation_add, neg_add_cancel,
      burnolMultiplicativeDilation_zero, inv_mul_cancel₀ nonzero, one_smul]
  · ext1 value
    change w • burnolMultiplicativeDilation h (w⁻¹ • burnolMultiplicativeDilation (-h) value) = value
    rw [map_smul, smul_smul, burnolMultiplicativeDilation_add, add_neg_cancel,
      burnolMultiplicativeDilation_zero, mul_inv_cancel₀ nonzero, one_smul]

theorem factor : Math.action = forward*(unit : End) := by
  have nonzero : w ≠ 0 := Complex.ofReal_ne_zero.mpr Math.weight_pos.ne'
  ext1 value
  change w • burnolMultiplicativeDilation h value-w⁻¹ • burnolMultiplicativeDilation (-h) value =
    w • burnolMultiplicativeDilation h (value-(w⁻¹*w⁻¹) • burnolMultiplicativeDilation (-(2*h)) value)
  rw [map_sub, map_smul, smul_sub, smul_smul, burnolMultiplicativeDilation_add,
    show h+ -(2*h)= -h by ring, ← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]

theorem two_sided : operator*Math.action=1 ∧ Math.action*operator=1 := by
  constructor
  · rw [operator, factor, mul_assoc, ← mul_assoc backward forward, leading_inverse.1, one_mul]
    exact Units.inv_mul unit
  · rw [operator, factor, mul_assoc, ← mul_assoc (unit : End), Units.mul_inv, one_mul]
    exact leading_inverse.2

theorem recover (value : BurnolL2) : operator (Math.action value)=value :=
  congrArg (fun map : End => map value) two_sided.1
end Inverse

local instance groups (grade : Nat) : ∀ slot, AddCommGroup (K.Grade grade slot) :=
  L.groups (PairValue C.Value) grade
variable (coordinate : BurnolCompletedMellinCoordinate) (n grade : Nat)
local notation "V" => K.Grade grade

def start : Expr (PairValue V) C.Var () := .linear (K.decode coordinate n grade) (.var ())

def branch (h : ℝ) (coefficient : ℂ) : Expr (PairValue V) C.Var () :=
  .linear (K.lift grade (coefficient • ContinuousLinearMap.id ℂ BurnolL2))
    (.linear (K.lift grade (Math.dilation h)) (start coordinate n grade))

def code : Expr (PairValue V) C.Var () :=
  .add (branch coordinate n grade Math.shift Math.weight)
    (.linear (-AddMonoidHom.id _) (branch coordinate n grade (-Math.shift) (Math.weight : ℂ)⁻¹))

theorem budget : remaining (code coordinate n grade) = 10 := rfl

theorem branch_total (h : ℝ) (coefficient : ℂ) (environment : Env (PairValue V) C.Var) :
    K.total (grade+1) ((branch coordinate n grade h coefficient).eval environment) =
      coefficient • Math.dilation h (K.total (grade+1) (K.decode coordinate n grade (environment () ()))) := by
  change K.total (grade+1) (K.lift grade (coefficient • ContinuousLinearMap.id ℂ BurnolL2)
    (K.lift grade (Math.dilation h) (K.decode coordinate n grade (environment () ())))) = _
  rw [K.lift_total, K.lift_total]
  rfl

theorem code_total (environment : Env (PairValue V) C.Var) :
    K.total (grade+1) ((code coordinate n grade).eval environment) =
      Math.action (K.total (grade+1) (K.decode coordinate n grade (environment () ()))) := by
  simp only [code, Expr.eval, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, map_add, map_neg, branch_total]
  change _ = (Math.weight : ℂ) • Math.dilation Math.shift _ -
    (Math.weight : ℂ)⁻¹ • Math.dilation (-Math.shift) _
  exact (sub_eq_add_neg _ _).symm

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Program
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
