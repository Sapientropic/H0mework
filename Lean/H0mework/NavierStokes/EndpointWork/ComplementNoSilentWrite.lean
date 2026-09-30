import H0mework.Realization.Faces.ComplementInitiality
import H0mework.NavierStokes.EndpointWork.NativeCausalRedirect
import H0mework.NavierStokes.EndpointTransport.PairDuhamelMacroWrite
import H0mework.NavierStokes.Restart.HeatCommutatorNativeVelocityPairRedirect

/-!
# Complement no-silence on an endpoint atom's actual native edge

A positive endpoint kinetic atom already generates an arbitrarily late
changed edge of the actual unforced restart path.  This module registers the
two coefficient endpoints of that same edge as the image of the canonical
two-point complement carrier.

If both the causal tangent and every pre-quotient pair innovation were silent,
the exact same-edge Duhamel compiler would identify the two registered
endpoints.  Their source-generated nonzero increment also makes the
registration injective, so joint silence would make the canonical complement
pair subsingleton, contradicting its initial nondegeneracy.

The final theorem consumes this exclusion immediately.  One actual endpoint
macro step writes its generated unforced physical successor and internally
chooses either the zero atom branch or, cofinally, a non-silent tangent/pair
responsibility.  A selected pair innovation also exhausts its own heat
commutator: zero commutator retains the pair's native next/trace settlement,
while a nonzero commutator generates an ordered velocity-pair next/whole-trace
redirect on the same receipt.

The complement carrier is a consumer of the already-generated edge.  It does
not choose the edge, output, pair, time, branch, nonzero witness, target, or
continuation.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open ComplementObservation
open AffineRelaxation

noncomputable section

/-! ## The actual edge as a canonical two-point observation -/

/-- Register the old and new coefficient of one actual native edge as the two
points of the canonical complement carrier.  The source has already generated
the edge, index, and output before this readout is formed. -/
def wholeRestartActualOutputEdgeRegistration
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    (canonicalComplementPair.{0} :
        ComplementObservationCarrier.{0}).Carrier →
      ComplexCoordinateVector :=
  fun point =>
    if point.down then
      (run initial index).nextContact.physicalState output
    else
      (run initial index).contact.physicalState output

@[simp] theorem wholeRestartActualOutputEdgeRegistration_null
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    wholeRestartActualOutputEdgeRegistration
        initial index output (ULift.up false) =
      (run initial index).contact.physicalState output := by
  rfl

@[simp] theorem wholeRestartActualOutputEdgeRegistration_complementNull
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    wholeRestartActualOutputEdgeRegistration
        initial index output (ULift.up true) =
      (run initial index).nextContact.physicalState output := by
  rfl

/-- A nonzero coefficient increment makes the canonical-pair registration
injective.  No complement action is imposed on the physical target. -/
theorem
    wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0) :
    Function.Injective
      (wholeRestartActualOutputEdgeRegistration initial index output) := by
  intro left right equality
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  cases left <;> cases right
  · rfl
  · exfalso
    exact incrementNonzero (sub_eq_zero.mpr equality.symm)
  · exfalso
    exact incrementNonzero (sub_eq_zero.mpr equality)
  · rfl

/-! ## Joint silence collapses the complement pair -/

/-- Componentwise silence of the exact same-edge causal decomposition.
Requiring every pair occurrence to vanish prevents aggregate cancellation
from hiding an unpaid component. -/
def wholeRestartActualOutputCausalJointSilent
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) : Prop :=
  wholeRestartCrossingUnforcedTangentRow initial index output = 0 ∧
    ∀ first : IntegerWavevector,
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first = 0

/-- On a changed nonzero output, joint silence identifies the two actual edge
endpoints.  Injectivity then transfers that identification back to every pair
of points in the canonical complement carrier. -/
theorem
    wholeRestartActualOutputCausalJointSilent_generates_canonicalPair_subsingleton
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0)
    (silent :
      wholeRestartActualOutputCausalJointSilent initial index output) :
    Subsingleton
      (canonicalComplementPair.{0} :
        ComplementObservationCarrier.{0}).Carrier := by
  have aggregateZero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) = 0 := by
    rw [show
      (fun first : IntegerWavevector =>
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) = 0 by
      funext first
      exact silent.2 first]
    exact tsum_zero
  have incrementZero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output = 0 := by
    rw [nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      initial index output outputNonzero, silent.1, smul_zero,
      aggregateZero, add_zero]
  have endpointEq :
      (run initial index).nextContact.physicalState output =
        (run initial index).contact.physicalState output :=
    sub_eq_zero.mp incrementZero
  have registrationConstant :
      ∀ left right,
        wholeRestartActualOutputEdgeRegistration
            initial index output left =
          wholeRestartActualOutputEdgeRegistration
            initial index output right := by
    intro left right
    rcases left with ⟨left⟩
    rcases right with ⟨right⟩
    cases left <;> cases right <;>
      simp [wholeRestartActualOutputEdgeRegistration, endpointEq]
  let injective :=
    wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
      initial index output incrementNonzero
  exact
    ⟨fun left right =>
      injective (registrationConstant left right)⟩

/-- The canonical complement pair's generated nondegeneracy excludes
componentwise silence on the changed actual output. -/
theorem
    wholeRestartActualOutputIncrement_ne_zero_excludes_causalJointSilent
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (incrementNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0) :
    ¬ wholeRestartActualOutputCausalJointSilent initial index output := by
  intro silent
  exact
    no_subsingleton_complement_observation_carrier
      (canonicalComplementPair.{0} : ComplementObservationCarrier.{0})
      (wholeRestartActualOutputCausalJointSilent_generates_canonicalPair_subsingleton
        initial index output outputNonzero incrementNonzero silent)

/-! The complement contradiction is consumed before quotient: it selects an
actual nonzero component rather than stopping at a Boolean no-silence
readout. -/

/-- Failure of componentwise joint silence generates either the tangent
component or one concrete pre-quotient pair innovation. -/
theorem
    wholeRestartActualOutput_not_causalJointSilent_generates_tangent_or_pairInnovation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (notSilent :
      ¬ wholeRestartActualOutputCausalJointSilent initial index output) :
    wholeRestartCrossingUnforcedTangentRow initial index output ≠ 0 ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first ≠ 0 := by
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index output ≠ 0
  · exact Or.inl tangentNonzero
  · right
    have tangentZero :
        wholeRestartCrossingUnforcedTangentRow initial index output = 0 :=
      not_ne_iff.mp tangentNonzero
    have notEveryPairSilent :
        ¬ ∀ first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial index output first = 0 := by
      intro everyPairSilent
      exact notSilent ⟨tangentZero, everyPairSilent⟩
    push Not at notEveryPairSilent
    exact notEveryPairSilent

/-! ## Pair innovation and heat-commutator native exhaustion -/

/-- One nonzero pair innovation keeps its original next/pointwise-trace
responsibility and, on the same index and ordered pair, internally exhausts
the heat commutator.  A nonzero commutator generates an actual-time ordered
velocity-pair responsibility; a zero commutator is recorded as the closed
relation branch. -/
theorem
    wholeRestartPairDuhamelInnovationOccurrence_ne_zero_generates_heatCommutator_nativeExhaustion
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (innovationNonzero :
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first ≠ 0) :
    (wholeRestartNextPairOccurrence initial index output first ≠ 0 ∨
      ∃ time :
          Icc (0 : ℝ) (run initial index).nextContact.time.1,
        wholeRestartPairOccurrenceTrace
          initial index output first time ≠ 0) ∧
      (wholeRestartVelocityTriadHeatCommutatorTrace initial index
            first (output - first) = 0 ∨
        ∃ time :
            Icc (0 : ℝ) (run initial index).nextContact.time.1,
          actualWholeVelocityBilinearEnergyOccurrence
              (run initial index).nextContact.prefixReceipt
              first (output - first) time ≠ 0 ∧
            actualWholeContinuousVelocityPairVector
              (run initial index).nextContact.prefixReceipt
              first (output - first) time ≠ 0 ∧
            (wholeRestartNextVelocityPairOccurrence initial index
                  first (output - first) ≠ 0 ∨
              (linearResidualTrace
                  wholeRestartSplicedVelocityPairOccurrenceTailKeep
                  (wholeRestartSplicedVelocityPairOccurrenceTail
                    initial index time 0) 0)
                    first (output - first) ≠ 0) ∧
            run initial (index + 1) =
              (run initial index).next) := by
  refine
    ⟨wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
      initial index output first innovationNonzero, ?_⟩
  by_cases commutatorNonzero :
      wholeRestartVelocityTriadHeatCommutatorTrace initial index
        first (output - first) ≠ 0
  · exact Or.inr
      (wholeRestartVelocityTriadHeatCommutatorTrace_ne_zero_generates_nativeVelocityPairResponsibility
        initial index first (output - first) commutatorNonzero)
  · exact Or.inl (not_ne_iff.mp commutatorNonzero)

/-! ## Source-facing whole write -/

/-- One actual endpoint macro step writes its generated unforced physical
successor and exhausts its kinetic atom without a caller-selected branch.

In the active branch, every requested old-run index has a later actual edge
whose positive physical time and nonzero output are selected by the source.
That edge embeds the canonical complement pair, rejects componentwise joint
silence, and enters the tangent or pair/heat-commutator native disposition.
The endpoint edge, output, pair, time, and branch are all generated inside the
conclusion. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_complementNoSilent_nativeWholeWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        ∀ requestedStart : ℕ,
          ∃ index : ℕ,
            requestedStart ≤ index ∧
              run current (index + 1) =
                (run current index).next ∧
              0 < (run current index).nextContact.time.1 ∧
              ∃ output : IntegerWavevector,
                output ≠ 0 ∧
                  (run current index).nextContact.physicalState output -
                      (run current index).contact.physicalState output ≠ 0 ∧
                  (run current index).nextContact.physicalState output -
                        (run current index).contact.physicalState output =
                      wholeRestartCausalTangentGain current index output •
                          wholeRestartCrossingUnforcedTangentRow
                            current index output +
                        (∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current index output first) ∧
                  Function.Injective
                    (wholeRestartActualOutputEdgeRegistration
                      current index output) ∧
                  ¬ wholeRestartActualOutputCausalJointSilent
                    current index output ∧
                  ((∃ tangentNonzero :
                          wholeRestartCrossingUnforcedTangentRow
                            current index ≠ 0,
                      ∃ localTime : ℝ,
                        0 < localTime ∧
                          localTime <
                            (run current index).nextContact.time.1 ∧
                          localTime *
                                (wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current index tangentNonzero 0 / 2) ≤
                              ∫ time in (0 : ℝ)..localTime,
                                wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current index tangentNonzero time ∧
                            0 <
                              ∫ time in (0 : ℝ)..localTime,
                                wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current index tangentNonzero time ∧
                            (∫ time in (0 : ℝ)..localTime,
                                wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current index tangentNonzero time) ≤
                              ‖(run current index).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
                    ∃ first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                            current index output first ≠ 0 ∧
                        (wholeRestartNextPairOccurrence
                              current index output first ≠ 0 ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current index).nextContact.time.1,
                            wholeRestartPairOccurrenceTrace
                              current index output first time ≠ 0) ∧
                        (wholeRestartVelocityTriadHeatCommutatorTrace
                              current index first (output - first) = 0 ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current index).nextContact.time.1,
                            actualWholeVelocityBilinearEnergyOccurrence
                                (run current index).nextContact.prefixReceipt
                                first (output - first) time ≠ 0 ∧
                              actualWholeContinuousVelocityPairVector
                                (run current index).nextContact.prefixReceipt
                                first (output - first) time ≠ 0 ∧
                              (wholeRestartNextVelocityPairOccurrence
                                    current index first (output - first) ≠ 0 ∨
                                (linearResidualTrace
                                    wholeRestartSplicedVelocityPairOccurrenceTailKeep
                                    (wholeRestartSplicedVelocityPairOccurrenceTail
                                      current index time 0) 0)
                                      first (output - first) ≠ 0) ∧
                              run current (index + 1) =
                                (run current index).next))) := by
  constructor
  · cases step with
    | advance elapsedBounded =>
        exact
          (wholeRestartEndpointCausalMacroFrame_physical_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
  · let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    rcases endpointReceipt.kineticReceipt.defect_disposition with
      defectPositive | defectZero
    · right
      have atomPositive :
          0 < step.physicalStageKineticEnergyAtom := by
        rw [step.physicalStageKineticEnergyAtom_eq_defect]
        exact defectPositive
      intro requestedStart
      obtain
          ⟨index, requestedLe, output, outputNonzero,
            incrementNonzero, causalSplit⟩ :=
        physicalStageKineticEnergyAtom_pos_generates_late_nativeCausalSplit
          step atomPositive requestedStart
      have registrationInjective :=
        wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
          current index output incrementNonzero
      have noJointSilence :=
        wholeRestartActualOutputIncrement_ne_zero_excludes_causalJointSilent
          current index output outputNonzero incrementNonzero
      refine
        ⟨index, requestedLe, rfl,
          (run current index).nextContact.time_pos,
          output, outputNonzero, incrementNonzero, causalSplit,
          registrationInjective, noJointSilence, ?_⟩
      rcases
          wholeRestartActualOutput_not_causalJointSilent_generates_tangent_or_pairInnovation
            current index output noJointSilence with
        tangentOutputNonzero | pair
      · have tangentNonzero :
            wholeRestartCrossingUnforcedTangentRow current index ≠ 0 := by
          intro tangentZero
          exact tangentOutputNonzero (congrFun tangentZero output)
        exact Or.inl
          ⟨tangentNonzero,
            wholeRestartCrossingUnforcedTangent_positiveTimePayment
              current index tangentNonzero⟩
      · rcases pair with ⟨first, innovationNonzero⟩
        obtain ⟨pairResponsibility, heatExhaustion⟩ :=
          wholeRestartPairDuhamelInnovationOccurrence_ne_zero_generates_heatCommutator_nativeExhaustion
            current index output first innovationNonzero
        exact Or.inr
          ⟨first, innovationNonzero, pairResponsibility, heatExhaustion⟩
    · left
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectZero.1

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
end NavierStokes
end SaturationMonoid
