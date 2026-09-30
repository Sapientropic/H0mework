import H0mework.NavierStokes.Accumulation.WholeReceiptKineticTimeModulus

/-!
# Whole-restart block kinetic ledger

The signed endpoint row in the exact whole-tangent balance must be folded
before any time-modulus estimate is accumulated.  This module performs that
fold on the actual selected prefix receipts.  Intermediate restart masses
cancel exactly, so a finite block pays the physical boundary only once.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartDualSquareCeiling
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

noncomputable section

def wholeRestartPrefixTangentSquare
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : Real :=
  puncturedEuclideanSpaceTimeSquare
    (run initial stage).nextContact.prefixReceipt.wholeTangent

def wholeRestartPrefixCubicAction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : Real :=
  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
    (wholeRestartCoefficientCeiling (run initial stage).contact ^ 3 *
      (run initial stage).nextContact.time.1)

def wholeRestartCubicFourthCoefficient (nu : Viscosity) : Real :=
  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) /
    (2 * sourceOwnedWholeStateBarrierSeventhCoefficient nu)

theorem wholeRestartPrefixTangentSquare_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    0 ≤ wholeRestartPrefixTangentSquare initial stage := by
  unfold wholeRestartPrefixTangentSquare
    puncturedEuclideanSpaceTimeSquare
  positivity

theorem wholeRestartPrefixCubicAction_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    0 ≤ wholeRestartPrefixCubicAction initial stage := by
  unfold wholeRestartPrefixCubicAction
  apply mul_nonneg
  · positivity
  · exact mul_nonneg
      (pow_nonneg
        (wholeRestartCoefficientCeiling_pos
          (run initial stage).contact).le _)
      (run initial stage).nextContact.time_pos.le

theorem wholeRestartCubicFourthCoefficient_nonneg
    (nu : Viscosity) :
    0 ≤ wholeRestartCubicFourthCoefficient nu := by
  unfold wholeRestartCubicFourthCoefficient
  apply div_nonneg
  · positivity
  · exact mul_nonneg (by norm_num)
      (sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu).le

/-- The seventh-order source barrier cancels the cubic tangent cost and
leaves a fourth-power reciprocal scale payment on every actual prefix. -/
theorem wholeRestartPrefixCubicAction_le_fourthPower
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    wholeRestartPrefixCubicAction initial stage ≤
      wholeRestartCubicFourthCoefficient nu /
        wholeRestartCoefficientCeiling (run initial stage).contact ^ 4 := by
  let current := run initial stage
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let seventh := sourceOwnedWholeStateBarrierSeventhCoefficient nu
  let cubic :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have ceilingPos : 0 < ceiling :=
    wholeRestartCoefficientCeiling_pos current.contact
  have seventhPos : 0 < seventh := by
    dsimp only [seventh]
    exact sourceOwnedWholeStateBarrierSeventhCoefficient_pos nu
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier current
  have timeLe : current.nextContact.time.1 ≤
      1 / (2 * (seventh * ceiling ^ 7 + 1)) :=
    current.nextContact.time.2.2.trans durationLe
  have basePos : 0 < seventh * ceiling ^ 7 := by positivity
  have denominatorLe :
      2 * (seventh * ceiling ^ 7) ≤
        2 * (seventh * ceiling ^ 7 + 1) := by nlinarith
  have reciprocalLe :
      1 / (2 * (seventh * ceiling ^ 7 + 1)) ≤
        1 / (2 * (seventh * ceiling ^ 7)) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) basePos) denominatorLe
  have timeBaseLe : current.nextContact.time.1 ≤
      1 / (2 * (seventh * ceiling ^ 7)) :=
    timeLe.trans reciprocalLe
  have cubicNonneg : 0 ≤ cubic := by
    dsimp only [cubic]
    positivity
  have scaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left timeBaseLe (pow_nonneg ceilingPos.le 3))
    cubicNonneg
  unfold wholeRestartPrefixCubicAction
    wholeRestartCubicFourthCoefficient
  dsimp only [current, ceiling, seventh, cubic] at scaled ⊢
  calc
    ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (wholeRestartCoefficientCeiling (run initial stage).contact ^ 3 *
          (run initial stage).nextContact.time.1) ≤
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
        (wholeRestartCoefficientCeiling (run initial stage).contact ^ 3 *
          (1 / (2 *
            (sourceOwnedWholeStateBarrierSeventhCoefficient nu *
              wholeRestartCoefficientCeiling
                (run initial stage).contact ^ 7)))) := scaled
    _ =
      (((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) /
        (2 * sourceOwnedWholeStateBarrierSeventhCoefficient nu)) /
          wholeRestartCoefficientCeiling
            (run initial stage).contact ^ 4 := by
      field_simp [seventhPos.ne', ceilingPos.ne']

theorem sum_wholeRestartPrefixCubicAction_le_fourthPower
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        wholeRestartPrefixCubicAction initial stage) ≤
      wholeRestartCubicFourthCoefficient nu *
        ∑ stage ∈ Finset.range length,
          1 / wholeRestartCoefficientCeiling
            (run initial stage).contact ^ 4 := by
  calc
    (∑ stage ∈ Finset.range length,
        wholeRestartPrefixCubicAction initial stage) ≤
      ∑ stage ∈ Finset.range length,
        wholeRestartCubicFourthCoefficient nu /
          wholeRestartCoefficientCeiling
            (run initial stage).contact ^ 4 := by
      apply Finset.sum_le_sum
      intro stage _stageMem
      exact wholeRestartPrefixCubicAction_le_fourthPower initial stage
    _ = wholeRestartCubicFourthCoefficient nu *
        ∑ stage ∈ Finset.range length,
          1 / wholeRestartCoefficientCeiling
            (run initial stage).contact ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro stage _stageMem
      ring

/-- One actual selected prefix retains the signed endpoint mass row. -/
theorem wholeRestartPrefixTangentSquare_add_massBoundary_le_cubicAction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    wholeRestartPrefixTangentSquare initial stage +
        nu.coeff *
          (wholeVorticityEuclideanMass
              (run initial (stage + 1)).contact.physicalState -
            wholeVorticityEuclideanMass
              (run initial stage).contact.physicalState) ≤
      wholeRestartPrefixCubicAction initial stage := by
  let current := run initial stage
  let receipt := current.nextContact.prefixReceipt
  let ceiling := wholeRestartCoefficientCeiling current.contact
  have fullMassAE :=
    generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
      (generatedWholeRestartCanonicalReplay current.contact)
  have fullPathEq := current.nextReceipt.wholePath_eq_transverse_ae
  have fullTransverseMassAE :
      ∀ᵐ time ∂(commonTimeMeasure
          (wholeRestartDuration current.contact)),
        wholeVorticityEuclideanMass
            (current.nextReceipt.transverseLimit time).1 ≤ ceiling := by
    filter_upwards [fullMassAE, fullPathEq] with time massLe pathEq
    rw [← pathEq]
    exact massLe
  have prefixTransverseMassAE :=
    prefixReceipt_transverseCoefficientMass_ae_le
      current.nextContact fullTransverseMassAE
  have pathEq := receipt.wholePath_eq_transverse_ae
  have prefixPathMassAE :
      ∀ᵐ time ∂(commonTimeMeasure current.nextContact.time.1),
        wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling := by
    filter_upwards [prefixTransverseMassAE, pathEq] with time massLe pathEq
    rw [pathEq]
    exact massLe
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      receipt prefixPathMassAE
  have viscousNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState receipt) := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  have terminalEq :
      receipt.wholePath
          ⟨current.nextContact.time.1,
            ⟨current.nextContact.time_pos.le, le_rfl⟩⟩ =
        current.nextContact.physicalState :=
    current.nextContact_prefix_terminal
  have nextStateEq :
      (run initial (stage + 1)).contact.physicalState =
        current.nextContact.physicalState := by
    rw [run_succ, next_contact]
    rfl
  dsimp only [receipt, ceiling] at signed terminalEq
  rw [terminalEq] at signed
  unfold wholeRestartPrefixTangentSquare
    wholeRestartPrefixCubicAction
  rw [nextStateEq]
  dsimp only [current]
  nlinarith

/-- Exact finite-block fold.  Every intermediate restart mass cancels; only
the block endpoints remain. -/
theorem sum_wholeRestartPrefixTangentSquare_add_massBoundary_le_sum_cubicAction
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        wholeRestartPrefixTangentSquare initial stage) +
        nu.coeff *
          (wholeVorticityEuclideanMass
              (run initial length).contact.physicalState -
            wholeVorticityEuclideanMass
              (run initial 0).contact.physicalState) ≤
      ∑ stage ∈ Finset.range length,
        wholeRestartPrefixCubicAction initial stage := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      have edge :=
        wholeRestartPrefixTangentSquare_add_massBoundary_le_cubicAction
          initial length
      simp only [Finset.sum_range_succ]
      linarith

/-- Source-only block upper: after the exact endpoint cancellation, dropping
the nonnegative terminal mass costs the initial mass only once. -/
theorem sum_wholeRestartPrefixTangentSquare_le_sum_cubicAction_add_initialMass
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        wholeRestartPrefixTangentSquare initial stage) ≤
      (∑ stage ∈ Finset.range length,
        wholeRestartPrefixCubicAction initial stage) +
      nu.coeff * wholeVorticityEuclideanMass
        (run initial 0).contact.physicalState := by
  have folded :=
    sum_wholeRestartPrefixTangentSquare_add_massBoundary_le_sum_cubicAction
      initial length
  have terminalNonneg :
      0 ≤ wholeVorticityEuclideanMass
        (run initial length).contact.physicalState :=
    wholeVorticityEuclideanMass_nonneg _
  have viscosityNonneg : 0 ≤ nu.coeff := nu.coeff_pos.le
  nlinarith

def wholeRestartVelocityAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState
    (run initial stage).contact.physicalState

def wholeRestartSelectedPrefixTimeSum
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) : Real :=
  ∑ stage ∈ Finset.range length,
    (run initial stage).nextContact.time.1

theorem wholeRestartSelectedPrefixTimeSum_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    0 ≤ wholeRestartSelectedPrefixTimeSum initial length := by
  unfold wholeRestartSelectedPrefixTimeSum
  exact Finset.sum_nonneg fun stage _stageMem =>
    (run initial stage).nextContact.time_pos.le

/-- The selected-prefix block clock is exactly the existing elapsed-time
ledger with its finite initial contact removed. -/
theorem wholeRestartSelectedPrefixTimeSum_eq_elapsedTime_sub_initial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ length : Nat,
      wholeRestartSelectedPrefixTimeSum initial length =
        elapsedTime initial (length + 1) - initial.contact.time.1
  | 0 => by
      rw [show (0 : Nat) + 1 = 1 by omega, elapsedTime_succ]
      simp [wholeRestartSelectedPrefixTimeSum, elapsedTime]
  | length + 1 => by
      have inductionHypothesis :=
        wholeRestartSelectedPrefixTimeSum_eq_elapsedTime_sub_initial
          initial length
      unfold wholeRestartSelectedPrefixTimeSum at inductionHypothesis
      rw [wholeRestartSelectedPrefixTimeSum,
        Finset.sum_range_succ, inductionHypothesis]
      have contactEq :
          (run initial length).nextContact.time.1 =
            (run initial (length + 1)).contact.time.1 := by
        rw [run_succ, next_contact]
      have elapsedSucc := elapsedTime_succ initial (length + 1)
      rw [contactEq, elapsedSucc]
      ring

/-- One selected prefix converts its already-folded tangent square into the
actual adjacent velocity displacement. -/
theorem wholeRestartVelocityAt_succ_sub_sq_le_prefixTangentSquare
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    ‖wholeRestartVelocityAt initial (stage + 1) -
        wholeRestartVelocityAt initial stage‖ ^ 2 ≤
      3 * (run initial stage).nextContact.time.1 *
        wholeRestartPrefixTangentSquare initial stage := by
  let current := run initial stage
  let receipt := current.nextContact.prefixReceipt
  let zeroTime : Icc (0 : Real) current.nextContact.time.1 :=
    ⟨0, ⟨le_rfl, current.nextContact.time_pos.le⟩⟩
  let terminal : Icc (0 : Real) current.nextContact.time.1 :=
    ⟨current.nextContact.time.1,
      ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
  have displacement :=
    receipt_wholeBiotSavartVelocity_sub_norm_sq_le_wholeTangent
      receipt zeroTime terminal current.nextContact.time_pos.le
  have tangentLe := receiptWholeTangentSquare_le_euclideanSquare receipt
  have scaledTangentLe :
      3 * current.nextContact.time.1 * ‖receipt.wholeTangent‖ ^ 2 ≤
        3 * current.nextContact.time.1 *
          puncturedEuclideanSpaceTimeSquare receipt.wholeTangent :=
    mul_le_mul_of_nonneg_left tangentLe
      (mul_nonneg (by norm_num) current.nextContact.time_pos.le)
  have sourceEq : receipt.wholePath zeroTime =
      current.contact.physicalState := receipt.wholePath_initial
  have targetEq : receipt.wholePath terminal =
      current.nextContact.physicalState :=
    current.nextContact_prefix_terminal
  have nextEq :
      (run initial (stage + 1)).contact.physicalState =
        current.nextContact.physicalState := by
    rw [run_succ, next_contact]
    rfl
  unfold wholeRestartVelocityAt wholeRestartPrefixTangentSquare
  rw [nextEq]
  dsimp only [current]
  rw [sourceEq, targetEq] at displacement
  norm_num [zeroTime, terminal] at displacement
  exact displacement.trans scaledTangentLe

theorem wholeRestartVelocityAt_succ_sub_norm_le_prefixBudget
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    ‖wholeRestartVelocityAt initial (stage + 1) -
        wholeRestartVelocityAt initial stage‖ ≤
      Real.sqrt
        (3 * (run initial stage).nextContact.time.1 *
          wholeRestartPrefixTangentSquare initial stage) := by
  have squareBound :=
    wholeRestartVelocityAt_succ_sub_sq_le_prefixTangentSquare initial stage
  have rightNonneg :
      0 ≤ 3 * (run initial stage).nextContact.time.1 *
        wholeRestartPrefixTangentSquare initial stage :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (run initial stage).nextContact.time_pos.le)
      (wholeRestartPrefixTangentSquare_nonneg initial stage)
  exact (Real.le_sqrt (norm_nonneg _) rightNonneg).2 squareBound

/-- Before Cauchy--Schwarz is applied, the exact block displacement is the
sum of its compiler-owned adjacent prefix budgets. -/
theorem wholeRestartVelocityAt_sub_norm_le_sum_prefixBudget
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    ‖wholeRestartVelocityAt initial length -
        wholeRestartVelocityAt initial 0‖ ≤
      ∑ stage ∈ Finset.range length,
        Real.sqrt
          (3 * (run initial stage).nextContact.time.1 *
            wholeRestartPrefixTangentSquare initial stage) := by
  have telescope :
      (∑ stage ∈ Finset.range length,
          (wholeRestartVelocityAt initial (stage + 1) -
            wholeRestartVelocityAt initial stage)) =
        wholeRestartVelocityAt initial length -
          wholeRestartVelocityAt initial 0 := by
    simpa using Finset.sum_range_sub
      (fun stage : Nat => wholeRestartVelocityAt initial stage) length
  calc
    ‖wholeRestartVelocityAt initial length -
        wholeRestartVelocityAt initial 0‖ =
        ‖∑ stage ∈ Finset.range length,
          (wholeRestartVelocityAt initial (stage + 1) -
            wholeRestartVelocityAt initial stage)‖ := by rw [telescope]
    _ ≤ ∑ stage ∈ Finset.range length,
          ‖wholeRestartVelocityAt initial (stage + 1) -
            wholeRestartVelocityAt initial stage‖ := norm_sum_le _ _
    _ ≤ ∑ stage ∈ Finset.range length,
        Real.sqrt
          (3 * (run initial stage).nextContact.time.1 *
            wholeRestartPrefixTangentSquare initial stage) := by
      apply Finset.sum_le_sum
      intro stage _stageMem
      exact wholeRestartVelocityAt_succ_sub_norm_le_prefixBudget
        initial stage

theorem sum_sqrt_prefixTime_mul_sqrt_tangentSquare_sq_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        Real.sqrt (3 * (run initial stage).nextContact.time.1) *
          Real.sqrt (wholeRestartPrefixTangentSquare initial stage)) ^ 2 ≤
      3 * wholeRestartSelectedPrefixTimeSum initial length *
        (∑ stage ∈ Finset.range length,
          wholeRestartPrefixTangentSquare initial stage) := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range length)
    (fun stage =>
      Real.sqrt (3 * (run initial stage).nextContact.time.1))
    (fun stage =>
      Real.sqrt (wholeRestartPrefixTangentSquare initial stage))
  have timeSq : ∀ stage : Nat,
      Real.sqrt (3 * (run initial stage).nextContact.time.1) ^ 2 =
        3 * (run initial stage).nextContact.time.1 := fun stage =>
    Real.sq_sqrt (mul_nonneg (by norm_num)
      (run initial stage).nextContact.time_pos.le)
  have tangentSq : ∀ stage : Nat,
      Real.sqrt (wholeRestartPrefixTangentSquare initial stage) ^ 2 =
        wholeRestartPrefixTangentSquare initial stage := fun stage =>
    Real.sq_sqrt (wholeRestartPrefixTangentSquare_nonneg initial stage)
  simp_rw [timeSq, tangentSq] at cauchy
  unfold wholeRestartSelectedPrefixTimeSum
  rw [← Finset.mul_sum] at cauchy
  simpa only [mul_assoc] using cauchy

/-- Cauchy--Schwarz is applied only after the exact restart block has been
assembled.  No sum of independent per-edge `sqrt time` bounds remains. -/
theorem wholeRestartVelocityAt_sub_norm_sq_le_time_mul_tangentBlock
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    ‖wholeRestartVelocityAt initial length -
        wholeRestartVelocityAt initial 0‖ ^ 2 ≤
      3 * wholeRestartSelectedPrefixTimeSum initial length *
        (∑ stage ∈ Finset.range length,
          wholeRestartPrefixTangentSquare initial stage) := by
  have blockLe :=
    wholeRestartVelocityAt_sub_norm_le_sum_prefixBudget initial length
  have factorized :
      (∑ stage ∈ Finset.range length,
          Real.sqrt
            (3 * (run initial stage).nextContact.time.1 *
              wholeRestartPrefixTangentSquare initial stage)) =
        ∑ stage ∈ Finset.range length,
          Real.sqrt (3 * (run initial stage).nextContact.time.1) *
            Real.sqrt (wholeRestartPrefixTangentSquare initial stage) := by
    apply Finset.sum_congr rfl
    intro stage _stageMem
    exact Real.sqrt_mul
      (mul_nonneg (by norm_num)
        (run initial stage).nextContact.time_pos.le)
      (wholeRestartPrefixTangentSquare initial stage)
  rw [factorized] at blockLe
  have sumNonneg :
      0 ≤ ∑ stage ∈ Finset.range length,
        Real.sqrt (3 * (run initial stage).nextContact.time.1) *
          Real.sqrt (wholeRestartPrefixTangentSquare initial stage) := by
    exact Finset.sum_nonneg fun stage _stageMem =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have squared :=
    (sq_le_sq₀ (norm_nonneg _) sumNonneg).2 blockLe
  exact squared.trans
    (sum_sqrt_prefixTime_mul_sqrt_tangentSquare_sq_le initial length)

/-- Final block modulus after the signed mass boundary has telescoped.  The
initial physical mass is paid once, while all interior tangent action is
charged to the actual cubic ledger. -/
theorem wholeRestartVelocityAt_sub_norm_sq_le_blockCubicLedger
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    ‖wholeRestartVelocityAt initial length -
        wholeRestartVelocityAt initial 0‖ ^ 2 ≤
      3 * wholeRestartSelectedPrefixTimeSum initial length *
        ((∑ stage ∈ Finset.range length,
            wholeRestartPrefixCubicAction initial stage) +
          nu.coeff * wholeVorticityEuclideanMass
            (run initial 0).contact.physicalState) := by
  exact (wholeRestartVelocityAt_sub_norm_sq_le_time_mul_tangentBlock
      initial length).trans
    (mul_le_mul_of_nonneg_left
      (sum_wholeRestartPrefixTangentSquare_le_sum_cubicAction_add_initialMass
        initial length)
      (mul_nonneg (by norm_num)
        (wholeRestartSelectedPrefixTimeSum_nonneg initial length)))

theorem wholeRestartVelocityAt_sub_norm_sq_le_blockFourthPowerLedger
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) :
    ‖wholeRestartVelocityAt initial length -
        wholeRestartVelocityAt initial 0‖ ^ 2 ≤
      3 * wholeRestartSelectedPrefixTimeSum initial length *
        (wholeRestartCubicFourthCoefficient nu *
            (∑ stage ∈ Finset.range length,
              1 / wholeRestartCoefficientCeiling
                (run initial stage).contact ^ 4) +
          nu.coeff * wholeVorticityEuclideanMass
            (run initial 0).contact.physicalState) := by
  exact (wholeRestartVelocityAt_sub_norm_sq_le_blockCubicLedger
      initial length).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (sum_wholeRestartPrefixCubicAction_le_fourthPower initial length)
        le_rfl)
      (mul_nonneg (by norm_num)
        (wholeRestartSelectedPrefixTimeSum_nonneg initial length)))

end
end ThreeDimensionalVorticityCoefficientWholeRestartBlockKineticLedger
end NavierStokes
end SaturationMonoid
