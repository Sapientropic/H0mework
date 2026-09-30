import Mathlib.Analysis.InnerProductSpace.l2Space
import H0mework.Realization.HilbertTransfer.Transfer
import H0mework.Probability.Source.Field

/-! The native successor acts on the whole square-summable source inventory. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.SourceShift

open scoped InnerProductSpace

noncomputable section

abbrev H := lp (fun _ : Nat => ℂ) 2

def place (index : Nat) : ℂ →ₗᵢ[ℂ] H where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : Nat => ℂ) 2 index
  norm_map' value := lp.norm_single (E := fun _ : Nat => ℂ) (p := 2) (by norm_num) index value

def basis (index : Nat) : H := lp.single 2 index 1

theorem successor_orthogonal :
    OrthogonalFamily ℂ (fun _ : Nat => ℂ) (fun index => place (index + 1)) := by
  intro left right distinct a b
  change ⟪lp.single (E := fun _ : Nat => ℂ) 2 (left + 1) a,
    lp.single (E := fun _ : Nat => ℂ) 2 (right + 1) b⟫_ℂ = 0
  rw [lp.inner_single_left]
  simp [lp.single_apply, distinct]

def shift : H →ₗᵢ[ℂ] H := successor_orthogonal.linearIsometry

theorem shift_single (index : Nat) (value : ℂ) :
    shift (lp.single 2 index value) = lp.single 2 (index + 1) value :=
  successor_orthogonal.linearIsometry_apply_single value

theorem shift_basis (index : Nat) : shift (basis index) = basis (index + 1) :=
  shift_single index 1

theorem shift_zero_coordinate (value : H) : shift value 0 = 0 := by
  have vanishes : (lp.evalCLM ℂ (fun _ : Nat => ℂ) 2 0).comp shift.toContinuousLinearMap = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro index
    apply ContinuousLinearMap.ext
    intro scalar
    change shift (lp.single 2 index scalar) 0 = 0
    rw [shift_single]
    simp [lp.single_apply]
  exact DFunLike.congr_fun vanishes value

theorem adjoint_basis_zero :
    IsometricRetainedTransfer.transfer shift (basis 0) = 0 := by
  apply ext_inner_left ℂ
  intro value
  change ⟪value, shift.toContinuousLinearMap.adjoint (basis 0)⟫_ℂ = ⟪value, (0 : H)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪shift value, lp.single 2 0 1⟫_ℂ = _
  rw [lp.inner_single_right, shift_zero_coordinate]
  simp

theorem basis_zero_ne_zero : basis 0 ≠ 0 := by
  intro vanished
  have coordinate := congrArg (fun value : H => value 0) vanished
  simp [basis, lp.single_apply] at coordinate

theorem residual_basis_zero : IsometricRetainedTransfer.residual shift (basis 0) = basis 0 := by
  change basis 0 - shift (IsometricRetainedTransfer.transfer shift (basis 0)) = basis 0
  rw [adjoint_basis_zero, map_zero, sub_zero]

def wordRead : Carrier Nat →ₗ[ℤ] H := observation basis

theorem wordRead_point (state : Nat) : wordRead (sourcePoint state) = basis state :=
  observation_point basis state

theorem wordRead_coordinate (word : Carrier Nat) (index : Nat) : wordRead word index = (word index : ℂ) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add source scalar word notMem nonzero inductionHypothesis =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, Int.cast_add, inductionHypothesis]
      congr 1
      simp [wordRead, observation, basis, lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem wordRead_injective : Function.Injective wordRead := by
  intro left right equality
  apply Finsupp.ext
  intro index
  have coordinate := congrArg (fun value : H => value index) equality
  rw [wordRead_coordinate, wordRead_coordinate] at coordinate
  exact Int.cast_inj.mp coordinate

theorem wordRead_source_action (word : Carrier Nat) :
    wordRead (sourceAction Nat.succ word) = shift (wordRead word) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero inductionHypothesis =>
      simp only [map_add, inductionHypothesis]
      congr 1
      simp [wordRead, sourceAction, observation, Finsupp.linearCombination_single,
        ← shift_basis]

end
end SourceOwnedObservationHistory.SourceShift
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
