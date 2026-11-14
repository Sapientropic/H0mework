import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.FiniteInverseWord
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedError

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedWord

open BurnolPhysicalState
open private damping compensation index_pos margin_bound damping_nonzero
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private right_quarter
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "E" => BoundaryCountedContinuousInverse.finiteEquiv
local notation "clock" => BoundaryCountedGenerator.clock
local notation "relative" => SourceGeneratedFiniteInverseWord.relative

private def scale (coordinate : ℂ) (n : Nat) : ℂ :=
  damping coordinate (I coordinate n)

private def tail (coordinate : ℂ) (n : Nat) : End :=
  compensation (I coordinate n) (index_pos coordinate n)

/-- This word applies only the actual counted compensation, scalar multiplication and finite sums. -/
def word (coordinate : ℂ) (n length : Nat) : End :=
  SourceGeneratedFiniteInverseWord.word (scale coordinate n) (tail coordinate n) length

private def gap (coordinate : ℂ) : ℝ := (coordinate.re-1/4)/2

private def loss (coordinate : ℂ) (n : Nat) : ℝ :=
  gap coordinate / ‖scale coordinate n‖

private theorem gap_pos (coordinate : ℂ) (right : 1/4 < coordinate.re) : 0 < gap coordinate := by
  unfold gap
  linarith

private theorem scale_norm_pos (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) :
    0 < ‖scale coordinate n‖ :=
  norm_pos_iff.mpr (damping_nonzero coordinate right n)

private theorem loss_pos (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) :
    0 < loss coordinate n :=
  div_pos (gap_pos coordinate right) (scale_norm_pos coordinate right n)

private theorem relative_bound (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat) :
    ‖relative (scale coordinate n) (tail coordinate n)‖ ≤ 1-loss coordinate n := by
  let β := scale coordinate n
  have positive := scale_norm_pos coordinate right n
  have margin : ‖tail coordinate n‖ + gap coordinate ≤ ‖β‖ :=
    (margin_bound coordinate right n).trans (Complex.re_le_norm β)
  unfold SourceGeneratedFiniteInverseWord.relative loss
  rw [norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv,
    show (1 : ℝ) = ‖β‖/‖β‖ from (div_self positive.ne').symm, ← sub_div]
  exact (div_le_div_iff_of_pos_right positive).mpr (by linarith only [margin])

/-- The omitted action has an exact source equation at every truncation length. -/
theorem clock_residual (coordinate : ℂ) (right : 1/4 < coordinate.re) (n length : Nat) (value : BurnolL2) :
    clock coordinate (I coordinate n) (index_pos coordinate n) (word coordinate n length value) - value =
      -((relative (scale coordinate n) (tail coordinate n))^length) value := by
  have paid := SourceGeneratedFiniteInverseWord.clock_word (scale coordinate n)
    (damping_nonzero coordinate right n) (tail coordinate n) length
  have read := congrArg (fun op : End => op value) paid
  change clock coordinate (I coordinate n) (index_pos coordinate n) (word coordinate n length value) =
    value - ((relative (scale coordinate n) (tail coordinate n))^length) value at read
  rw [read]
  abel

private theorem inverse_residual (coordinate : ℂ) (right : 1/4 < coordinate.re) (n length : Nat) (value : BurnolL2) :
    (E coordinate right n).symm value - word coordinate n length value =
      ((relative (scale coordinate n) (tail coordinate n))^length) ((E coordinate right n).symm value) := by
  let x := (E coordinate right n).symm value
  have paid := SourceGeneratedFiniteInverseWord.word_clock (scale coordinate n)
    (damping_nonzero coordinate right n) (tail coordinate n) length
  have read := congrArg (fun op : End => op x) paid
  change word coordinate n length (clock coordinate (I coordinate n) (index_pos coordinate n) x) =
    x - ((relative (scale coordinate n) (tail coordinate n))^length) x at read
  rw [← BoundaryCountedContinuousInverse.finiteEquiv_source coordinate right n,
    show E coordinate right n x = value from ContinuousLinearEquiv.apply_symm_apply _ _] at read
  change x - word coordinate n length value = _
  rw [read, sub_sub_cancel]

/-- The source cell margin pays the discarded word on the complete field. -/
theorem inverse_word_bound (coordinate : ℂ) (right : 1/4 < coordinate.re) (n length : Nat) (value : BurnolL2) :
    ‖(E coordinate right n).symm value - word coordinate n length value‖ ≤
      (1-loss coordinate n)^length * ((gap coordinate)⁻¹ * ‖value‖) := by
  let q := relative (scale coordinate n) (tail coordinate n)
  let x := (E coordinate right n).symm value
  have ratio := relative_bound coordinate right n
  have qPower : ‖q^length‖ ≤ ‖q‖^length := by
    cases length with
    | zero =>
      simp only [pow_zero]
      change ‖ContinuousLinearMap.id ℂ BurnolL2‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ m => exact norm_pow_le' q m.succ_pos
  have bound : ‖q^length‖ ≤ (1-loss coordinate n)^length :=
    qPower.trans (pow_le_pow_left₀ (norm_nonneg q) ratio length)
  rw [inverse_residual]
  calc
    _ ≤ ‖q^length‖ * ‖x‖ := (q^length).le_opNorm x
    _ ≤ _ := mul_le_mul bound (BoundaryCountedContinuousInverse.inverse_bound coordinate right n value)
      (norm_nonneg x) ((norm_nonneg _).trans bound)

/-- Truncation length is computed from source damping, count and the complete actual input. -/
def lengthFor (coordinate : ℂ) (n : Nat) (value : BurnolL2) (tolerance : ℝ) : Nat :=
  SourceGeneratedFiniteInverseWord.cutoff (loss coordinate n) ((gap coordinate)⁻¹ * ‖value‖) tolerance

theorem inverse_word_accuracy (coordinate : ℂ) (right : 1/4 < coordinate.re) (n : Nat)
    (value : BurnolL2) (tolerance : ℝ) (positive : 0 < tolerance) :
    ‖(E coordinate right n).symm value - word coordinate n (lengthFor coordinate n value tolerance) value‖ <
      tolerance := by
  have lossLe : loss coordinate n ≤ 1 := sub_nonneg.mp
    ((norm_nonneg _).trans (relative_bound coordinate right n))
  have price : 0 ≤ (gap coordinate)⁻¹ * ‖value‖ :=
    mul_nonneg (inv_nonneg.mpr (gap_pos coordinate right).le) (norm_nonneg _)
  exact (inverse_word_bound coordinate right n _ value).trans_lt
    (SourceGeneratedFiniteInverseWord.cutoff_pays _ _ _ (loss_pos coordinate right n) lossLe price positive)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

/-- Both cutoffs are paid before the original physical projections or the literal next are read. -/
theorem actual_word_accuracy (ordinal : Nat) (tolerance : ℝ) (positive : 0 < tolerance) :
    let n := ⌈BoundaryCountedError.budget c * ‖raw ordinal‖ / (tolerance/2)⌉₊
    let length := lengthFor ((c).value/2) n (raw (ordinal+1)) (tolerance/2)
    let field := -word ((c).value/2) n length (raw (ordinal+1))
    ‖field - raw (ordinal+2)‖ < tolerance := by
  let z := (c).value/2
  let n := ⌈BoundaryCountedError.budget c * ‖raw ordinal‖ / (tolerance/2)⌉₊
  let current := raw (ordinal+1)
  let w := word z n (lengthFor z n current (tolerance/2)) current
  let inverse := (E z (right_quarter c) n).symm current
  have halfPos : 0 < tolerance/2 := by positivity
  have counting : ‖-inverse - raw (ordinal+2)‖ < tolerance/2 :=
    BoundaryCountedError.actual_accuracy observation nontrivial half depth ordinal (tolerance/2) halfPos
  have finite : ‖inverse-w‖ < tolerance/2 :=
    inverse_word_accuracy z (right_quarter c) n current (tolerance/2) halfPos
  change ‖-w - raw (ordinal+2)‖ < tolerance
  rw [show -w - raw (ordinal+2) = (inverse-w) + (-inverse-raw (ordinal+2)) by abel]
  exact (norm_add_le _ _).trans_lt ((add_lt_add finite counting).trans_eq (by ring))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedWord
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
