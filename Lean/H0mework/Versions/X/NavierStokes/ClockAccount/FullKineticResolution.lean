import H0mework.Versions.X.NavierStokes.ClockAccount.FullSelectionHorizon
import H0mework.Versions.X.NavierStokes.ClockAccount.FullSource

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.KineticClockResolution

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

abbrev source := FullBoundary.source

/-- Physical kinetic mass expressed in the source's fixed clock payment units. -/
def clockState (state : source.State) : SourceGeneratedRootClockStateAt source state where
  potential := puncturedWholeVorticityKineticMass state.1.physical.contact.physicalState /
    SelectionHorizon.paymentRate
  potential_nonneg := div_nonneg (puncturedWholeVorticityKineticMass_nonneg _)
    SelectionHorizon.paymentRate_pos.le

private theorem physicalAt (stage : Nat) :
    (source.stateAfter stage).1.physical = run concreteCounterexampleInitial stage := by
  have current := standingActionWholeRestartMediumSource_stateAfter_current
    stackedInitialActionMaterialInstruction stage
  exact congrArg (fun runtime => runtime.physical) current

private theorem clockAt (stage : Nat) :
    source.clockAt (source.stateAfter stage) =
      (run concreteCounterexampleInitial stage).nextContact.time.1 := by
  change (source.stateAfter stage).1.physical.nextContact.time.1 = _
  rw [physicalAt]
  rfl

private theorem potentialAt (stage : Nat) :
    (clockState (source.stateAfter stage)).potential =
      puncturedWholeVorticityKineticMass
        (run concreteCounterexampleInitial stage).contact.physicalState /
          SelectionHorizon.paymentRate := by
  change puncturedWholeVorticityKineticMass
    (source.stateAfter stage).1.physical.contact.physicalState / _ = _
  rw [physicalAt]
  rfl

private theorem nextPotentialAt (stage : Nat) :
    (clockState (source.successor (source.stateAfter stage))).potential =
      puncturedWholeVorticityKineticMass
        (run concreteCounterexampleInitial (stage + 1)).contact.physicalState /
          SelectionHorizon.paymentRate := by
  rw [← NativeFluidMediumSource.stateAfter_succ]
  exact potentialAt (stage + 1)

/-- The same actual window pays its clock even when its net enstrophy debit
is nonpositive. Only the actual next mass enters the source estimate. -/
theorem dominationOfHigh (stage : Nat)
    (high : WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    source.clockAt (source.stateAfter stage) +
      (clockState (source.successor (source.stateAfter stage))).potential ≤
        (clockState (source.stateAfter stage)).potential := by
  rw [clockAt, potentialAt, nextPotentialAt]
  have payment := SelectionHorizon.contact_time_le_payment_of_high stage high
  have ledger := run_contact_kineticDissipation_succ_le concreteCounterexampleInitial stage
  have paid := add_le_add_right payment
    (puncturedWholeVorticityKineticMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState)
  have total : (run concreteCounterexampleInitial stage).nextContact.time.1 *
      SelectionHorizon.paymentRate +
        puncturedWholeVorticityKineticMass
          (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤
        puncturedWholeVorticityKineticMass
          (run concreteCounterexampleInitial stage).contact.physicalState := by
    linarith
  apply (le_div_iff₀ SelectionHorizon.paymentRate_pos).mpr
  rw [add_mul, div_mul_cancel₀ _ SelectionHorizon.paymentRate_pos.ne']
  exact total

/-- The original material and retained clock also cover the physical reserve. -/
structure InstructionAt (stage : Nat) where
  base : FullSource.InstructionAt (source.stateAfter stage)
  coversKinetic : (clockState (source.stateAfter stage)).potential ≤ base.clock.potential

def initialInstruction : InstructionAt 0 where
  base :=
    { material := FullSource.initialInstruction.material
      clock := clockState (source.stateAfter 0) }
  coversKinetic := le_rfl

/-- Reuse the already completed zero-waste advance, retaining every surplus
and the original material predecessor. The new obligation is paid by kinetics. -/
def advanceOfHigh (stage : Nat) (instruction : InstructionAt stage)
    (high : WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    Σ next : InstructionAt (stage + 1),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        instruction.base.clock next.base.clock
        (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage)) := by
  have kinetic := dominationOfHigh stage high
  have covered := instruction.coversKinetic
  have nextNonneg := (clockState (source.successor (source.stateAfter stage))).potential_nonneg
  have solvent : source.clockAt (source.stateAfter stage) ≤ instruction.base.clock.potential := by
    linarith
  let advanced := FullSource.advance stage instruction.base solvent
  refine ⟨⟨advanced.1, ?_⟩, advanced.2⟩
  change (clockState (source.stateAfter (stage + 1))).potential ≤
    instruction.base.clock.potential - source.clockAt (source.stateAfter stage)
  rw [NativeFluidMediumSource.stateAfter_succ]
  linarith

theorem advanceOfHigh_retains_surplus (stage : Nat) (instruction : InstructionAt stage)
    (high : WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    (advanceOfHigh stage instruction high).1.base.clock.potential =
      instruction.base.clock.potential - source.clockAt (source.stateAfter stage) := by
  rfl

/-- One actual next contact selects a clock settlement or the original global
physical continuation. No future branch or enstrophy-growth table is input. -/
def resolve (stage : Nat) (instruction : InstructionAt stage) :
    (Σ next : InstructionAt (stage + 1),
      SourceGeneratedRootClockSettlementAt source (source.stateAfter stage)
        instruction.base.clock next.base.clock
        (nativeFluidMediumRootOperationalOutcomeAt source (source.stateAfter stage))) ⊕
      GeneratedWholeGlobalPhysicalTrajectory concreteCounterexampleInitial := by
  by_cases low : wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState ≤
        WindowMassCoefficient.halfCriticalMass
  · exact .inr (SmallBranch.lowContact_globalTrajectory (stage + 1) low)
  · exact .inl (advanceOfHigh stage instruction (lt_of_not_ge low))

private theorem initialHigh :
    WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial 1).contact.physicalState := by
  have kernelOne : (1 : Real) ≤
      ∑' wave : IntegerWavevector, integerWaveCriticalKernel wave := by
    let axis : IntegerWavevector := fun coordinate => if coordinate = 0 then 1 else 0
    have lower := summable_integerWaveCriticalKernel.le_tsum axis
      (fun wave _ => integerWaveCriticalKernel_nonneg wave)
    simpa [integerWaveCriticalKernel, integerWaveNormSq, axis] using lower
  have halfLe : WindowMassCoefficient.halfCriticalMass / 2 ≤ (1 : Real) / 40000 := by
    rw [WindowMassCoefficient.halfCriticalMass_half_eq]
    apply one_div_le_one_div_of_le (by norm_num : (0 : Real) < 40000)
    nlinarith
  have thresholdLt : WindowMassCoefficient.halfCriticalMass < 2 := by linarith
  change WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
    stackedShortCurrent.nextContact.physicalState
  exact thresholdLt.trans stackedShortCurrent_nextContact_wholeMass_gt_two

/-- The concrete source's first step takes the paid branch of this same rule. -/
def initialTransition := advanceOfHigh 0 initialInstruction initialHigh

theorem initialTransition_exact_remaining :
    initialInstruction.base.clock.potential = source.clockAt (source.stateAfter 0) +
      initialTransition.1.base.clock.potential := by
  rw [initialTransition, advanceOfHigh_retains_surplus]
  ring

end
end SaturationMonoid.NavierStokes.KineticClockResolution
