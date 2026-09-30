import H0mework.NavierStokes.Restart.VelocityWeakEndpoint

/-!
# Zero kinetic-defect completion on the physical velocity carrier

The actual contact sequence is observed simultaneously in the weighted
vorticity kinetic carrier and in the physical Biot--Savart velocity carrier.
On differences of two actual transverse contacts these two observations have
exactly the same Hilbert distance.  Consequently the already generated
zero-defect strong kinetic branch forces strong convergence to the physical
velocity endpoint on the same refined source subsequence.

No endpoint, subsequence, limit, faithfulness law, continuation witness, or
target trajectory is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-! ## Exact same-event carrier isometry -/

/-- Inverse-Laplacian kinetic Euclideanization preserves subtraction before
the whole-carrier norm is read. -/
theorem puncturedWholeVorticityKineticEuclideanState_sub
    (left right : ComplexVorticityHilbertState) :
    puncturedWholeVorticityKineticEuclideanState (left - right) =
      puncturedWholeVorticityKineticEuclideanState left -
        puncturedWholeVorticityKineticEuclideanState right := by
  apply lp.ext
  rw [lp.coeFn_sub]
  change
    puncturedWholeVorticityKineticEuclideanCoefficient (left - right) =
      puncturedWholeVorticityKineticEuclideanCoefficient left -
        puncturedWholeVorticityKineticEuclideanCoefficient right
  funext wave
  change
    puncturedWholeVorticityKineticEuclideanCoefficient
        (left - right) wave =
      puncturedWholeVorticityKineticEuclideanCoefficient left wave -
        puncturedWholeVorticityKineticEuclideanCoefficient right wave
  ext coordinate
  simp [puncturedWholeVorticityKineticEuclideanCoefficient,
    euclideanCoordinateRow, smul_sub]

/-- Biot--Savart velocity formation preserves subtraction before the
physical whole-carrier norm is read. -/
theorem puncturedWholeVelocityEuclideanState_sub
    (left right : ComplexVorticityHilbertState) :
    puncturedWholeVelocityEuclideanState (left - right) =
      puncturedWholeVelocityEuclideanState left -
        puncturedWholeVelocityEuclideanState right := by
  apply lp.ext
  rw [lp.coeFn_sub]
  change
    puncturedWholeVelocityEuclideanCoefficient (left - right) =
      puncturedWholeVelocityEuclideanCoefficient left -
        puncturedWholeVelocityEuclideanCoefficient right
  funext wave
  change
    puncturedWholeVelocityEuclideanCoefficient (left - right) wave =
      puncturedWholeVelocityEuclideanCoefficient left wave -
        puncturedWholeVelocityEuclideanCoefficient right wave
  ext coordinate
  simp [puncturedWholeVelocityEuclideanCoefficient,
    euclideanCoordinateRow, biotSavartVelocityCoefficient_sub]

/-- On two actual source contacts, the physical velocity difference and the
weighted-vorticity kinetic difference have identical norm square. -/
theorem wholeRestartContactVelocityState_sub_norm_sq_eq_kinetic
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (left right : ℕ) :
    ‖wholeRestartContactVelocityState initial left -
        wholeRestartContactVelocityState initial right‖ ^ 2 =
      ‖wholeRestartContactKineticState initial left -
        wholeRestartContactKineticState initial right‖ ^ 2 := by
  let leftState := (run initial left).contact.physicalState
  let rightState := (run initial right).contact.physicalState
  have differenceTransverse :
      WholeStateTransverse (leftState - rightState) :=
    wholeStateTransverse_sub leftState rightState
      (run initial left).contact.transverse
      (run initial right).contact.transverse
  calc
    ‖wholeRestartContactVelocityState initial left -
        wholeRestartContactVelocityState initial right‖ ^ 2 =
        ‖puncturedWholeVelocityEuclideanState
          (leftState - rightState)‖ ^ 2 := by
      rw [puncturedWholeVelocityEuclideanState_sub]
      rfl
    _ = puncturedWholeVorticityKineticMass (leftState - rightState) :=
      puncturedWholeVelocityEuclideanState_norm_sq
        (leftState - rightState) differenceTransverse
    _ = ‖puncturedWholeVorticityKineticEuclideanState
          (leftState - rightState)‖ ^ 2 :=
      (puncturedWholeVorticityKineticEuclideanState_norm_sq
        (leftState - rightState)).symm
    _ = ‖wholeRestartContactKineticState initial left -
        wholeRestartContactKineticState initial right‖ ^ 2 := by
      rw [puncturedWholeVorticityKineticEuclideanState_sub]
      rfl

/-- The preceding square identity is an exact distance isometry on the
actual source contact lineage. -/
theorem wholeRestartContactVelocityState_dist_eq_kinetic
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (left right : ℕ) :
    dist (wholeRestartContactVelocityState initial left)
        (wholeRestartContactVelocityState initial right) =
      dist (wholeRestartContactKineticState initial left)
        (wholeRestartContactKineticState initial right) := by
  rw [dist_eq_norm, dist_eq_norm]
  have squareEq :=
    wholeRestartContactVelocityState_sub_norm_sq_eq_kinetic
      initial left right
  nlinarith [norm_nonneg
      (wholeRestartContactVelocityState initial left -
        wholeRestartContactVelocityState initial right),
    norm_nonneg
      (wholeRestartContactKineticState initial left -
        wholeRestartContactKineticState initial right)]

/-! ## Zero-defect physical completion -/

/-- Strong kinetic convergence on the generated upstream subsequence forces
strong physical-velocity convergence on the exact refined subsequence already
stored by the velocity endpoint receipt. -/
theorem
    GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.velocity_strong_tendsto_of_kineticStrong
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (kineticStrong :
      Tendsto
        (fun index =>
          wholeRestartContactKineticState
            initial (receipt.kineticReceipt.subsequence index))
        atTop
        (nhds receipt.kineticReceipt.endpoint)) :
    Tendsto
      (fun index =>
        wholeRestartContactVelocityState initial (receipt.subsequence index))
      atTop
      (nhds receipt.velocityEndpoint) := by
  let kineticSequence : ℕ → WholeRestartKineticEndpointState :=
    fun index =>
      wholeRestartContactKineticState initial (receipt.subsequence index)
  let velocitySequence : ℕ → WholeRestartVelocityEndpointState :=
    fun index =>
      wholeRestartContactVelocityState initial (receipt.subsequence index)
  have kineticStrongShared :
      Tendsto kineticSequence atTop
        (nhds receipt.kineticReceipt.endpoint) := by
    simpa only [kineticSequence,
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
      Function.comp_def] using
      kineticStrong.comp
        receipt.velocitySubsubsequence_strictMono.tendsto_atTop
  have kineticCauchy : CauchySeq kineticSequence :=
    kineticStrongShared.cauchySeq
  have velocityCauchy : CauchySeq velocitySequence := by
    rw [Metric.cauchySeq_iff] at kineticCauchy ⊢
    intro epsilon epsilonPos
    obtain ⟨cutoff, close⟩ := kineticCauchy epsilon epsilonPos
    refine ⟨cutoff, ?_⟩
    intro left leftGe right rightGe
    rw [show
      dist (velocitySequence left) (velocitySequence right) =
        dist (kineticSequence left) (kineticSequence right) by
          exact wholeRestartContactVelocityState_dist_eq_kinetic
            initial (receipt.subsequence left) (receipt.subsequence right)]
    exact close left leftGe right rightGe
  obtain ⟨velocityLimit, velocityStrong⟩ :=
    cauchySeq_tendsto_of_complete velocityCauchy
  have strongInnerTendsto
      (test : WholeRestartVelocityEndpointState) :
      Tendsto
        (fun index => inner ℂ (velocitySequence index) test)
        atTop
        (nhds (inner ℂ velocityLimit test)) :=
    velocityStrong.inner tendsto_const_nhds
  have weakInnerTendsto
      (test : WholeRestartVelocityEndpointState) :
      Tendsto
        (fun index => inner ℂ (velocitySequence index) test)
        atTop
        (nhds (inner ℂ receipt.velocityEndpoint test)) := by
    simpa only [velocitySequence] using
      receipt.velocity_weak_tendsto_shared test
  have innerEq (test : WholeRestartVelocityEndpointState) :
      inner ℂ velocityLimit test = inner ℂ receipt.velocityEndpoint test :=
    tendsto_nhds_unique
      (strongInnerTendsto test) (weakInnerTendsto test)
  have limitEq : velocityLimit = receipt.velocityEndpoint := by
    let difference := velocityLimit - receipt.velocityEndpoint
    have selfZero : inner ℂ difference difference = 0 := by
      dsimp only [difference]
      rw [inner_sub_left, innerEq]
      rw [inner_sub_right]
      ring
    have normSqZero : ‖difference‖ ^ 2 = 0 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact congrArg Complex.re selfZero
    have differenceZero : difference = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg difference]
    exact sub_eq_zero.mp differenceZero
  simpa only [velocitySequence, limitEq] using velocityStrong

/-- Vanishing of the source-generated kinetic endpoint defect forces strong
completion in the physical velocity carrier.  Strong kinetic convergence is
derived from the receipt's own exhaustive defect disposition, not supplied as
a faithfulness premise. -/
theorem
    GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.velocity_strong_tendsto_of_kineticDefect_eq_zero
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (defectZero :
      wholeRestartKineticWeakEndpointDefect
        initial receipt.kineticReceipt.endpoint = 0) :
    Tendsto
      (fun index =>
        wholeRestartContactVelocityState initial (receipt.subsequence index))
      atTop
      (nhds receipt.velocityEndpoint) := by
  rcases receipt.kineticReceipt.defect_disposition with
    defectPositive | zeroBranch
  · exact False.elim (by linarith)
  · exact velocity_strong_tendsto_of_kineticStrong receipt zeroBranch.2

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
end NavierStokes
end SaturationMonoid
