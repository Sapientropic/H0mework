import H0mework.Versions.X.NavierStokes.ClockAccount.History

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

def physicalPrefixMass (stage : Nat) : Real :=
  wholePrefixVorticityMass
    (run stackedShortCurrent stage).nextContact.time
    (run stackedShortCurrent stage).nextReceipt.stateLimit

def physicalKineticAccount (stage : Nat) : Real :=
  puncturedWholeVorticityKineticMass
    (run stackedShortCurrent stage).contact.physicalState /
      (2 * butterflyGainViscosity.coeff)

def physicalDensityReserve (stage : Nat) : Real :=
  2 + ∑ prior ∈ Finset.range stage,
    (physicalPrefixMass prior - source.clockAt (source.stateAfter prior))

theorem physicalCurrent_eq_run (stage : Nat) :
    (source.stateAfter stage).1.physical = run stackedShortCurrent stage :=
  congrArg (fun current => current.physical)
    (standingActionWholeRestartMediumSource_stateAfter_current
      stackedInitialActionMaterialInstruction stage)

theorem physicalKineticAccount_eq_source (stage : Nat) :
    physicalKineticAccount stage =
      puncturedWholeVorticityKineticMass
        (source.stateAfter stage).1.physical.contact.physicalState /
          (2 * butterflyGainViscosity.coeff) := by
  rw [physicalCurrent_eq_run]
  rfl

theorem physicalKineticAccount_step (stage : Nat) :
    physicalKineticAccount stage =
      physicalKineticAccount (stage + 1) + physicalPrefixMass stage := by
  have ledger := (run stackedShortCurrent stage).nextContact_kineticDissipation_eq
  have denominatorPos : 0 < 2 * butterflyGainViscosity.coeff :=
    mul_pos (by norm_num) butterflyGainViscosity.coeff_pos
  unfold physicalKineticAccount physicalPrefixMass
  rw [run_succ, next_contact]
  apply mul_right_cancel₀ denominatorPos.ne'
  rw [add_mul, div_mul_cancel₀ _ denominatorPos.ne',
    div_mul_cancel₀ _ denominatorPos.ne']
  rw [mul_comm _ (2 * butterflyGainViscosity.coeff)]
  exact ledger.symm

theorem physicalKineticAccount_add_prefix_eq_initial (stage : Nat) :
    physicalKineticAccount stage +
      (∑ prior ∈ Finset.range stage, physicalPrefixMass prior) =
        physicalKineticAccount 0 := by
  induction stage with
  | zero => simp
  | succ stage previous =>
      rw [Finset.sum_range_succ]
      linarith [physicalKineticAccount_step stage]

theorem physicalDensityReserve_step (stage : Nat) :
    physicalDensityReserve (stage + 1) =
      physicalDensityReserve stage + physicalPrefixMass stage -
        source.clockAt (source.stateAfter stage) := by
  unfold physicalDensityReserve
  rw [Finset.sum_range_succ]
  ring

theorem reachable_potential_eq_kinetic_add_densityReserve
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    face.clockState.potential =
      physicalKineticAccount stage + physicalDensityReserve stage := by
  have folded := reachable.prefix_add_potential_eq_initial
  have kinetic := physicalKineticAccount_add_prefix_eq_initial stage
  have initialPotential :
      (butterflyCappedCreditClockState
        butterflyZeroBankInitialInstruction).potential =
      physicalKineticAccount 0 + 2 := by
    change min (wholeVorticityEuclideanMass
      stackedShortCurrent.contact.physicalState) 2 +
        physicalKineticAccount 0 + 0 = physicalKineticAccount 0 + 2
    rw [min_eq_right stackedShortCurrent_contact_wholeMass_gt_two.le]
    ring
  rw [initialPotential] at folded
  unfold physicalDensityReserve
  rw [Finset.sum_sub_distrib]
  linarith

theorem residual_densityReserve_shortfall
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (shortfall : ButterflyCreditClockFaceResidualAt stage face
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction stage)) :
    physicalDensityReserve (stage + 1) <
      min
        (min (wholeVorticityEuclideanMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState) 2)
        (standingActionBarrierTail butterflyGainViscosity
          (source.stateAfter (stage + 1)).1.standing.anchorLevel) := by
  have currentEq := reachable_potential_eq_kinetic_add_densityReserve reachable
  have kinetic := physicalKineticAccount_step stage
  have density := physicalDensityReserve_step stage
  have cappedShortfall : face.clockState.potential <
      source.clockAt (source.stateAfter stage) +
        cappedMassKineticClockPotential (source.stateAfter (stage + 1)) := by
    cases face <;> exact shortfall.cappedCreditShortfall
  have completeShortfall : face.clockState.potential <
      source.clockAt (source.stateAfter stage) +
        kineticBarrierPotential (source.stateAfter (stage + 1)) := by
    cases face <;> exact shortfall.completeCreditShortfall
  rw [currentEq] at cappedShortfall completeShortfall
  unfold cappedMassKineticClockPotential at cappedShortfall
  unfold kineticBarrierPotential at completeShortfall
  rw [← physicalKineticAccount_eq_source] at cappedShortfall completeShortfall
  apply lt_min
  · linarith
  · linarith

/-- The source density reserve directly selects the compiler's actual paid
successor.  Every existing material alternative is consumed by that compiler;
the negative output is rejected on the same reachable occurrence. -/
noncomputable def reachable_transition_of_densityReserve
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (covered :
      min
        (min (wholeVorticityEuclideanMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState) 2)
        (standingActionBarrierTail butterflyGainViscosity
          (source.stateAfter (stage + 1)).1.standing.anchorLevel) ≤
        physicalDensityReserve (stage + 1)) :
    Σ nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        face.clockState nextFace.clockState
        (nativeFluidMediumRootOperationalOutcomeAt source
          (source.stateAfter stage)) := by
  rcases butterflyCreditClockFaceTotalTransition stage face
      (sourceGeneratedStandingActionRunClockDisposition
        stackedInitialActionMaterialInstruction stage) with paid | shortfall
  · exact paid
  · exact False.elim
      (not_lt_of_ge covered (residual_densityReserve_shortfall reachable shortfall))

theorem densityReserve_covers_of_transition
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)))
    (settlement : SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
      face.clockState nextFace.clockState
      (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage))) :
    min
      (min (wholeVorticityEuclideanMass
        (source.stateAfter (stage + 1)).1.physical.contact.physicalState) 2)
      (standingActionBarrierTail butterflyGainViscosity
        (source.stateAfter (stage + 1)).1.standing.anchorLevel) ≤
      physicalDensityReserve (stage + 1) := by
  have paid := settlement.resolved.settlement
  have wasteNonneg := settlement.resolved.waste_nonneg
  have currentEq := reachable_potential_eq_kinetic_add_densityReserve reachable
  have kinetic := physicalKineticAccount_step stage
  have density := physicalDensityReserve_step stage
  cases nextFace with
  | capped instruction =>
      change face.clockState.potential = source.clockAt (source.stateAfter stage) +
        (cappedMassKineticClockPotential (source.stateAfter (stage + 1)) +
          instruction.bank) + _ at paid
      rw [currentEq] at paid
      unfold cappedMassKineticClockPotential at paid
      rw [← physicalKineticAccount_eq_source] at paid
      apply (min_le_left _ _).trans
      linarith [instruction.bank_nonneg]
  | complete instruction =>
      change face.clockState.potential = source.clockAt (source.stateAfter stage) +
        (kineticBarrierPotential (source.stateAfter (stage + 1)) +
          instruction.bank) + _ at paid
      rw [currentEq] at paid
      unfold kineticBarrierPotential at paid
      rw [← physicalKineticAccount_eq_source] at paid
      apply (min_le_right _ _).trans
      linarith [instruction.bank_nonneg]
  | rich instruction =>
      change face.clockState.potential = source.clockAt (source.stateAfter stage) +
        (butterflyCreditBearingClockState instruction).potential + _ at paid
      rw [currentEq, butterflyCreditBearingClockState_eq_complete_add_prepaid] at paid
      change physicalKineticAccount stage + physicalDensityReserve stage =
        source.clockAt (source.stateAfter stage) +
          (kineticBarrierPotential (source.stateAfter (stage + 1)) +
            (instruction.bank + butterflyRichCurrentPrepaidCredit (stage + 1))) + _ at paid
      unfold kineticBarrierPotential at paid
      rw [← physicalKineticAccount_eq_source] at paid
      apply (min_le_right _ _).trans
      linarith [instruction.bank_nonneg, butterflyRichCurrentPrepaidCredit_nonneg (stage + 1)]


/-- The density condition is exactly the payment fibre of the existing
three-face compiler, so passing to the source account adds no obligation. -/
theorem transition_nonempty_iff_densityReserve
    {stage : Nat}
    {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    Nonempty (Σ nextFace : ButterflyCreditClockFaceAt (source.stateAfter (stage + 1)),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        face.clockState nextFace.clockState
        (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage))) ↔
      min
        (min (wholeVorticityEuclideanMass
          (source.stateAfter (stage + 1)).1.physical.contact.physicalState) 2)
        (standingActionBarrierTail butterflyGainViscosity
          (source.stateAfter (stage + 1)).1.standing.anchorLevel) ≤
        physicalDensityReserve (stage + 1) := by
  constructor
  · rintro ⟨nextFace, settlement⟩
    exact densityReserve_covers_of_transition reachable nextFace settlement
  · intro covered
    exact ⟨reachable_transition_of_densityReserve reachable covered⟩

end

end SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
