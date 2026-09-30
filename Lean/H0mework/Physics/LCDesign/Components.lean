import H0mework.Physics.PortCoupling.OperatorTolerance

/-!
# Finite LC/transducer design kernel

This file compiles an explicit finite component specification into the
Hilbert-space quarter-period operator.  The specification has one normalized
lossless LC resonator and one passive reciprocal transducer stage at every
embodiment channel.  Component parameters enter the compiler; no coupling,
consciousness or body verdict is a design field.

The distinguished design uses unit inductance/capacitance and a non-ideal
`99/100` transfer gain.  Its compiled operator is provably different from the
ideal Hamiltonian centre, yet leaves enough norm margin for a second open
implementation ball around the design itself.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open _root_.SaturationMonoid.AffineRelaxation
open Physical.Interface

noncomputable section

/-- Parameters of one normalized LC resonator followed by a reciprocal
transducer stage. -/
structure LCTransducerBranchDesign where
  inductance : ℝ
  capacitance : ℝ
  transferGain : ℝ

/-- The same certified branch is replicated at every one of the ten typed
channels.  The channel type fixes the wiring addresses before compilation. -/
structure UniformFiniteLCTransducerNetworkDesign where
  branch : LCTransducerBranchDesign

inductive LCTransducerComponentKind where
  | inductor
  | capacitor
  | reciprocalTransducer
  deriving DecidableEq, Repr, FintypeViaProxy

/-- Each typed channel carries an inductor, capacitor and reciprocal
transducer slot. -/
abbrev FiniteLCTransducerComponentSlot :=
  FiniteEmbodimentChannel × LCTransducerComponentKind

theorem finiteLCTransducerComponentSlot_cardinality :
    Fintype.card FiniteLCTransducerComponentSlot = 30 := by
  decide

/-- Source-side component admissibility only.  No compiled dynamics or target
classification is stored in this certificate. -/
structure LCTransducerComponentAdmissibleAt
    (design : UniformFiniteLCTransducerNetworkDesign) : Prop where
  inductancePositive : 0 < design.branch.inductance
  capacitancePositive : 0 < design.branch.capacitance
  transferGainPositive : 0 < design.branch.transferGain
  transferGainPassive : design.branch.transferGain ≤ 1

def normalizedLCAngularFrequency
    (design : UniformFiniteLCTransducerNetworkDesign) : ℝ :=
  (Real.sqrt
    (design.branch.inductance * design.branch.capacitance))⁻¹

/-- The ideal lossless resonator dynamics compiled from `L` and `C`. -/
def compiledLCResonatorOperator
    (design : UniformFiniteLCTransducerNetworkDesign) (time : ℝ) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (schrodingerScalarPhaseFlowHom
    (E := HilbertEmbodimentState)
    (normalizedLCAngularFrequency design)
    (Multiplicative.ofAdd time)).toLinearIsometry.toContinuousLinearMap

/-- The reciprocal transducer gain is applied after the resonator stage. -/
def compiledLCTransducerOperator
    (design : UniformFiniteLCTransducerNetworkDesign) (time : ℝ) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (design.branch.transferGain : ℂ) •
    compiledLCResonatorOperator design time

def compiledLCTransducerQuarterOperator
    (design : UniformFiniteLCTransducerNetworkDesign) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  compiledLCTransducerOperator design (Real.pi / 2)

/-- An explicit non-ideal component design. -/
def ninetyNinePercentUnitLCTransducerDesign :
    UniformFiniteLCTransducerNetworkDesign where
  branch := {
    inductance := 1
    capacitance := 1
    transferGain := (99 : ℝ) / 100
  }

theorem ninetyNinePercentUnitLCTransducerDesign_admissible :
    LCTransducerComponentAdmissibleAt
      ninetyNinePercentUnitLCTransducerDesign where
  inductancePositive := by norm_num [ninetyNinePercentUnitLCTransducerDesign]
  capacitancePositive := by norm_num [ninetyNinePercentUnitLCTransducerDesign]
  transferGainPositive := by norm_num [ninetyNinePercentUnitLCTransducerDesign]
  transferGainPassive := by norm_num [ninetyNinePercentUnitLCTransducerDesign]

theorem ninetyNinePercentUnitLC_frequency_eq_one :
    normalizedLCAngularFrequency
      ninetyNinePercentUnitLCTransducerDesign = 1 := by
  norm_num [normalizedLCAngularFrequency,
    ninetyNinePercentUnitLCTransducerDesign]

def scaledQuarterOperator (gain : ℝ) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  (gain : ℂ) • idealQuarterOperator

theorem compiledNinetyNinePercentQuarterOperator_eq_scaled :
    compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign =
      scaledQuarterOperator ((99 : ℝ) / 100) := by
  unfold compiledLCTransducerQuarterOperator compiledLCTransducerOperator
    compiledLCResonatorOperator scaledQuarterOperator idealQuarterOperator
  rw [ninetyNinePercentUnitLC_frequency_eq_one]
  norm_num [ninetyNinePercentUnitLCTransducerDesign]

theorem scaledQuarterOperator_sub (gain : ℝ) :
    scaledQuarterOperator gain - idealQuarterOperator =
      (((gain : ℂ) - 1) • idealQuarterOperator) := by
  ext state
  simp [scaledQuarterOperator, sub_smul]

theorem scaledQuarterOperator_sub_scaled (left right : ℝ) :
    scaledQuarterOperator left - scaledQuarterOperator right =
      ((((left - right : ℝ) : ℂ)) • idealQuarterOperator) := by
  ext state
  simp [scaledQuarterOperator, sub_smul]

theorem scaledQuarterOperator_injective :
    Function.Injective scaledQuarterOperator := by
  intro left right same
  have sameAt := congrArg
    (fun operator : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState =>
      operator (encodeHilbert (intervention .sourceBound 1))) same
  simp only [scaledQuarterOperator, smul_apply,
    idealQuarterOperator_apply,
    harmonicFlow_pi_div_two_eq_evolve_on_intervention] at sameAt
  have coordinateSame := congrArg
    (fun state : HilbertEmbodimentState => (state .sourceBound).re) sameAt
  simpa [encodeHilbert, encodeComplex, encodePort, evolve, intervention] using
    coordinateSame

theorem norm_idealQuarterOperator_le : ‖idealQuarterOperator‖ ≤ 1 := by
  exact LinearIsometry.norm_toContinuousLinearMap_le _

theorem ninetyNinePercentCenter_error_le_oneHundredth :
    ‖compiledLCTransducerQuarterOperator
          ninetyNinePercentUnitLCTransducerDesign - idealQuarterOperator‖ ≤
      (1 : ℝ) / 100 := by
  rw [compiledNinetyNinePercentQuarterOperator_eq_scaled,
    scaledQuarterOperator_sub, norm_smul]
  have bound := norm_idealQuarterOperator_le
  norm_num at bound ⊢
  linarith

theorem ninetyNinePercentCenter_hasOperatorTolerance :
    OperatorToleranceAt
      (compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign) := by
  unfold OperatorToleranceAt
  exact lt_of_le_of_lt ninetyNinePercentCenter_error_le_oneHundredth
    (by norm_num)

/-- The component-generated centre is genuinely non-ideal. -/
theorem ninetyNinePercentCenter_ne_ideal :
    compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign ≠ idealQuarterOperator := by
  rw [compiledNinetyNinePercentQuarterOperator_eq_scaled]
  rw [← show scaledQuarterOperator 1 = idealQuarterOperator by
    simp [scaledQuarterOperator]]
  intro same
  have gainSame := scaledQuarterOperator_injective same
  norm_num at gainSame

/-- A fabrication/implementation margin around the already non-ideal
component-generated centre. -/
def WithinNinetyNinePercentDesignToleranceAt
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState) :
    Prop :=
  ‖implementation - compiledLCTransducerQuarterOperator
      ninetyNinePercentUnitLCTransducerDesign‖ < (1 : ℝ) / 200

theorem withinNinetyNinePercentDesignTolerance_operatorTolerance
    (implementation : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (withinDesign : WithinNinetyNinePercentDesignToleranceAt implementation) :
    OperatorToleranceAt implementation := by
  unfold WithinNinetyNinePercentDesignToleranceAt at withinDesign
  unfold OperatorToleranceAt
  calc
    ‖implementation - idealQuarterOperator‖ =
        ‖(implementation - compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign) +
          (compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign -
              idealQuarterOperator)‖ := by congr 1; abel
    _ ≤ ‖implementation - compiledLCTransducerQuarterOperator
          ninetyNinePercentUnitLCTransducerDesign‖ +
        ‖compiledLCTransducerQuarterOperator
          ninetyNinePercentUnitLCTransducerDesign - idealQuarterOperator‖ :=
      norm_add_le _ _
    _ < (1 : ℝ) / 200 + (1 : ℝ) / 100 :=
      add_lt_add_of_lt_of_le withinDesign
        ninetyNinePercentCenter_error_le_oneHundredth
    _ < (1 : ℝ) / 40 := by norm_num

theorem ninetyNinePercentDesignTolerance_inhabited :
    WithinNinetyNinePercentDesignToleranceAt
      (compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign) := by
  norm_num [WithinNinetyNinePercentDesignToleranceAt]

def nearbyNinetyNinePointThreePercentOperator :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  scaledQuarterOperator ((993 : ℝ) / 1000)

/-- A second, explicit operator lies strictly inside the design-centred ball. -/
theorem nearbyNinetyNinePointThreePercentOperator_withinDesignTolerance :
    WithinNinetyNinePercentDesignToleranceAt
      nearbyNinetyNinePointThreePercentOperator := by
  unfold WithinNinetyNinePercentDesignToleranceAt
    nearbyNinetyNinePointThreePercentOperator
  rw [compiledNinetyNinePercentQuarterOperator_eq_scaled,
    scaledQuarterOperator_sub_scaled, norm_smul]
  have bound := norm_idealQuarterOperator_le
  norm_num at bound ⊢
  linarith

theorem nearbyNinetyNinePointThreePercentOperator_ne_designCenter :
    nearbyNinetyNinePointThreePercentOperator ≠
      compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign := by
  rw [nearbyNinetyNinePointThreePercentOperator,
    compiledNinetyNinePercentQuarterOperator_eq_scaled]
  intro same
  have gainSame := scaledQuarterOperator_injective same
  norm_num at gainSame

end

end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.ninetyNinePercentCenter_hasOperatorTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.ninetyNinePercentCenter_ne_ideal
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.withinNinetyNinePercentDesignTolerance_operatorTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.nearbyNinetyNinePointThreePercentOperator_withinDesignTolerance
