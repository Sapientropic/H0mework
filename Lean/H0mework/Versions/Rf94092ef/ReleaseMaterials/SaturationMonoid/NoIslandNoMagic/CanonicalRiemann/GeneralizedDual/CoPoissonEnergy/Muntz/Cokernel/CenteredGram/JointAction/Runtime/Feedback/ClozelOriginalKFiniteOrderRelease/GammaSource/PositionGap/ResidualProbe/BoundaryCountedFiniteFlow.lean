import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedFiniteFlow

open BurnolPhysicalState
open scoped BigOperators

open private index_pos damping_nonzero compensation
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private finite_clock_error cellError amplitude amplitude_pos resolvent_bound literal_next
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedError
open private transportSpeed
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
open private scale gap gap_pos loss loss_pos scale_norm_pos
  from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
open private right_quarter
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "R" => burnolDirectRightResolventCLM
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "relative" => SourceGeneratedFiniteInverseWord.relative
local notation "meshTail" => BoundaryCountedMassMesh.meshTail

private def tail (coordinate : ℂ) (n mesh : Nat) : End := meshTail (I coordinate n) mesh

private def clock (coordinate : ℂ) (n mesh : Nat) : End :=
  scale coordinate n • (1 : End) - tail coordinate n mesh

private def q (coordinate : ℂ) (n mesh : Nat) : End :=
  relative (scale coordinate n) (tail coordinate n mesh)

def word (coordinate : ℂ) (n mesh length : Nat) : End :=
  SourceGeneratedFiniteInverseWord.word (scale coordinate n) (tail coordinate n mesh) length

private theorem relative_bound (coordinate : ℂ) (right : 1/4 < coordinate.re) (n mesh : Nat) (meshPos : 0 < mesh) :
    ‖q coordinate n mesh‖ ≤ 1-loss coordinate n := by
  let β := scale coordinate n
  have positive := scale_norm_pos coordinate right n
  have margin : ‖tail coordinate n mesh‖ + gap coordinate ≤ ‖β‖ :=
    (BoundaryCountedMassMesh.mesh_margin coordinate right n mesh meshPos).trans (Complex.re_le_norm β)
  unfold q SourceGeneratedFiniteInverseWord.relative loss
  rw [norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv,
    show (1 : ℝ) = ‖β‖/‖β‖ from (div_self positive.ne').symm, ← sub_div]
  exact (div_le_div_iff_of_pos_right positive).mpr (by linarith only [margin])

private theorem power_bound (op : End) (m : Nat) : ‖op^m‖ ≤ ‖op‖^m := by
  cases m with
  | zero =>
    simp only [pow_zero]
    change ‖ContinuousLinearMap.id ℂ BurnolL2‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ m => exact norm_pow_le' op m.succ_pos

private theorem bounded_powers (coordinate : ℂ) (right : 1/4 < coordinate.re)
    (n mesh : Nat) (meshPos : 0 < mesh) (m : Nat) :
    ‖q coordinate n mesh ^ m‖ ≤ (1-loss coordinate n)^m :=
  (power_bound _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (relative_bound coordinate right n mesh meshPos) m)

/-- The fully finite word has the same uniform bound paid by the original mass margin. -/
theorem word_bound (coordinate : ℂ) (right : 1/4 < coordinate.re) (n mesh length : Nat) (meshPos : 0 < mesh) :
    ‖word coordinate n mesh length‖ ≤ (gap coordinate)⁻¹ := by
  let β := scale coordinate n
  let ρ := 1-loss coordinate n
  have betaPos := scale_norm_pos coordinate right n
  have nonneg : 0 ≤ ρ := (norm_nonneg _).trans (relative_bound coordinate right n mesh meshPos)
  have contract : ρ < 1 := sub_lt_self _ (loss_pos coordinate right n)
  have geom : ∑ j ∈ Finset.range length, ρ^j ≤ (loss coordinate n)⁻¹ := by
    rw [← Nat.Ico_zero_eq_range]
    have paid := geom_sum_Ico_le_of_lt_one (m := 0) (n := length) nonneg contract
    simpa only [pow_zero, ρ, sub_sub_cancel, one_div] using paid
  unfold word SourceGeneratedFiniteInverseWord.word
  rw [norm_smul, norm_inv]
  calc
    _ ≤ ‖β‖⁻¹ * ∑ j ∈ Finset.range length, ‖q coordinate n mesh ^ j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr betaPos.le)
    _ ≤ ‖β‖⁻¹ * ∑ j ∈ Finset.range length, ρ^j :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => bounded_powers coordinate right n mesh meshPos j))
        (inv_nonneg.mpr betaPos.le)
    _ ≤ ‖β‖⁻¹ * (loss coordinate n)⁻¹ := mul_le_mul_of_nonneg_left geom (inv_nonneg.mpr betaPos.le)
    _ = _ := by
      change ‖β‖⁻¹ * (gap coordinate / ‖β‖)⁻¹ = _
      rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ betaPos.ne', one_mul]

theorem clock_residual (coordinate : ℂ) (right : 1/4 < coordinate.re) (n mesh length : Nat) (value : BurnolL2) :
    clock coordinate n mesh (word coordinate n mesh length value)-value =
      -((q coordinate n mesh)^length) value := by
  have proof := SourceGeneratedFiniteInverseWord.clock_word (scale coordinate n)
    (damping_nonzero coordinate right n) (tail coordinate n mesh) length
  have paid := congrArg (fun op : End => op value) proof
  change clock coordinate n mesh (word coordinate n mesh length value) =
    value - ((q coordinate n mesh)^length) value at paid
  rw [paid]
  abel

private theorem field_error (coordinate : ℂ) (right : 1/4 < coordinate.re) (n mesh length : Nat)
    (meshPos : 0 < mesh) (value x : BurnolL2) :
    ‖x-word coordinate n mesh length value‖ ≤ (gap coordinate)⁻¹*‖clock coordinate n mesh x-value‖ +
      (1-loss coordinate n)^length*‖x‖ := by
  let w := word coordinate n mesh length
  let e := clock coordinate n mesh
  let p := (q coordinate n mesh)^length
  have proof := SourceGeneratedFiniteInverseWord.word_clock (scale coordinate n)
    (damping_nonzero coordinate right n) (tail coordinate n mesh) length
  have paid := congrArg (fun op : End => op x) proof
  change w (e x) = x-p x at paid
  have recovery : x-w value = w (e x-value)+p x := by
    rw [map_sub, paid]
    abel
  change ‖x-w value‖ ≤ _
  rw [recovery]
  have first := (w.le_opNorm (e x-value)).trans
    (mul_le_mul_of_nonneg_right (word_bound coordinate right n mesh length meshPos) (norm_nonneg (e x-value)))
  have second := (p.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (bounded_powers coordinate right n mesh meshPos length) (norm_nonneg x))
  exact (norm_add_le _ _).trans (add_le_add first second)

private def meshBudget (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  (gap (coordinate.value/2))⁻¹ * transportSpeed coordinate

private theorem original_error (coordinate : BurnolCompletedMellinCoordinate) (previous : BurnolL2)
    (n mesh length : Nat) (meshPos : 0 < mesh) :
    let z := coordinate.value/2
    let current := R coordinate previous
    ‖-word z n mesh length current - R coordinate current‖ ≤
      BoundaryCountedError.budget coordinate * ‖previous‖ / (I z n : ℝ) +
      meshBudget coordinate * ‖current‖ / (mesh : ℝ) +
      (1-loss z n)^length * (amplitude coordinate * ‖current‖) := by
  let z := coordinate.value/2
  let current := R coordinate previous
  let N := I z n
  let x := -(R coordinate current)
  let w := word z n mesh length
  let e := clock z n mesh
  let actual := BoundaryCountedGenerator.clock z N (index_pos z n)
  have right : 1/4 < z.re := right_quarter coordinate
  have xBorn : x = R coordinate (-current) := (map_neg _ _).symm
  have comp := BoundaryCountedMassMesh.mesh_error coordinate (-current) N mesh (index_pos z n) meshPos
  rw [← xBorn, norm_neg] at comp
  have counting : ‖actual x-current‖ ≤ cellError coordinate * ‖previous‖ / (N : ℝ) :=
    finite_clock_error coordinate previous N (index_pos z n)
  have joined : e x-current = (actual x-current)+(compensation N (index_pos z n) x-meshTail N mesh x) := by
    change (scale z n • x-meshTail N mesh x)-current =
      ((scale z n • x-compensation N (index_pos z n) x)-current)+
        (compensation N (index_pos z n) x-meshTail N mesh x)
    abel
  have clockError := (norm_add_le (actual x-current) (compensation N (index_pos z n) x-meshTail N mesh x)).trans
    (add_le_add counting comp)
  rw [← joined] at clockError
  have field := field_error z right n mesh length meshPos current x
  have xBound : ‖x‖ ≤ amplitude coordinate * ‖current‖ := by
    rw [show x = -(R coordinate current) by rfl, norm_neg]
    exact resolvent_bound coordinate current
  have powerNonneg : 0 ≤ (1-loss z n)^length :=
    (norm_nonneg _).trans (bounded_powers z right n mesh meshPos length)
  change ‖-w current - R coordinate current‖ ≤ _
  rw [show -w current - R coordinate current = x-w current by dsimp only [x]; abel]
  calc
    _ ≤ (gap z)⁻¹*‖e x-current‖ + (1-loss z n)^length*‖x‖ := field
    _ ≤ (gap z)⁻¹*(cellError coordinate*‖previous‖/(N : ℝ) +
        transportSpeed coordinate*‖current‖/(mesh : ℝ)) +
        (1-loss z n)^length*(amplitude coordinate*‖current‖) :=
      add_le_add (mul_le_mul_of_nonneg_left clockError (inv_nonneg.mpr (gap_pos z right).le))
        (mul_le_mul_of_nonneg_left xBound powerNonneg)
    _ = _ := by unfold BoundaryCountedError.budget meshBudget gap; dsimp only [z,N]; ring

private def countFor (coordinate : BurnolCompletedMellinCoordinate) (previous : BurnolL2) (tolerance : ℝ) : Nat :=
  ⌈BoundaryCountedError.budget coordinate*‖previous‖/(tolerance/3)⌉₊

private def meshFor (coordinate : BurnolCompletedMellinCoordinate) (current : BurnolL2) (tolerance : ℝ) : Nat :=
  ⌈meshBudget coordinate*‖current‖/(tolerance/3)⌉₊+1

private def lengthFor (coordinate : BurnolCompletedMellinCoordinate) (current : BurnolL2)
    (n : Nat) (tolerance : ℝ) : Nat :=
  SourceGeneratedFiniteInverseWord.cutoff (loss (coordinate.value/2) n)
    (amplitude coordinate*‖current‖) (tolerance/3)

/-- The complete field is computed by a finite weighted dilation word followed by the finite power word. -/
def program (coordinate : BurnolCompletedMellinCoordinate) (previous current : BurnolL2) (tolerance : ℝ) : BurnolL2 :=
  let n := countFor coordinate previous tolerance
  let mesh := meshFor coordinate current tolerance
  let length := lengthFor coordinate current n tolerance
  show BurnolL2 from -(word (coordinate.value/2) n mesh length current)

private theorem ceiling_pays (budget tolerance : ℝ) (positive : 0 < tolerance) {n : Nat}
    (larger : ⌈budget/tolerance⌉₊ < n) : budget/(n : ℝ) < tolerance := by
  have cutoff : budget/tolerance < (n : ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast larger)
  have indexPositive : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le _).trans_lt larger
  exact (div_lt_iff₀ indexPositive).mpr (by simpa only [mul_comm] using (div_lt_iff₀ positive).mp cutoff)

theorem source_accuracy (coordinate : BurnolCompletedMellinCoordinate) (previous : BurnolL2)
    (tolerance : ℝ) (positive : 0 < tolerance) :
    ‖program coordinate previous (R coordinate previous) tolerance - R coordinate (R coordinate previous)‖ <
      tolerance := by
  let z := coordinate.value/2
  let current := R coordinate previous
  let n := countFor coordinate previous tolerance
  let mesh := meshFor coordinate current tolerance
  let length := lengthFor coordinate current n tolerance
  have right : 1/4 < z.re := right_quarter coordinate
  have third : 0 < tolerance/3 := by positivity
  have meshPos : 0 < mesh := Nat.succ_pos _
  have first : BoundaryCountedError.budget coordinate*‖previous‖/(I z n : ℝ) < tolerance/3 := by
    apply ceiling_pays _ _ third
    change n < I z n
    unfold BoundaryCountedContinuousInverse.index
    omega
  have second : meshBudget coordinate*‖current‖/(mesh : ℝ) < tolerance/3 :=
    ceiling_pays _ _ third (Nat.lt_succ_self _)
  have lossLe : loss z n ≤ 1 := sub_nonneg.mp ((norm_nonneg _).trans (relative_bound z right n mesh meshPos))
  have budgetNonneg : 0 ≤ amplitude coordinate*‖current‖ :=
    mul_nonneg (amplitude_pos coordinate).le (norm_nonneg current)
  have last : (1-loss z n)^length * (amplitude coordinate*‖current‖) < tolerance/3 :=
    SourceGeneratedFiniteInverseWord.cutoff_pays _ _ _ (loss_pos z right n) lossLe budgetNonneg third
  change ‖-(word z n mesh length current) - R coordinate current‖ < tolerance
  exact (original_error coordinate previous n mesh length meshPos).trans_lt
    ((add_lt_add (add_lt_add first second) last).trans_eq (by ring))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth

/-- A complete finite word approaches the literal next on the original cofinal R history. -/
theorem actual_accuracy (ordinal : Nat) (tolerance : ℝ) (positive : 0 < tolerance) :
    ‖program c (raw ordinal) (raw (ordinal+1)) tolerance - raw (ordinal+2)‖ < tolerance := by
  rw [show ordinal+2 = (ordinal+1)+1 by omega,
    literal_next observation nontrivial half depth (ordinal+1), literal_next observation nontrivial half depth ordinal]
  exact source_accuracy c (raw ordinal) tolerance positive

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedFiniteFlow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
