import H0mework.Physics.GaugeFlow.P843

/-!
# Proposition 844: concrete action zero is active trace-zero sector

P843 proved that every trace-zero sector produces the concrete color-loop
action zero fiber of P842.  This file proves the reverse readout and packages
the exact equivalence:

`SU7GaugeFlowConcreteActionZeroFiberLaw`

is the same data as an active scalar together with a global trace-zero
prime-edge sector.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open GrandUnification
open AffineRelaxation

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Active trace-zero sector -/

/-- A trace-zero prime-edge sector equipped with an active scalar keep. -/
structure ActiveTraceZeroPrimeEdgeSector where
  sigma : ℝ
  sigma_active : sigma ≠ 0
  sector : TraceZeroPrimeEdgeSector

/-- THEOREM 1: a concrete action-zero law forgets to an active trace-zero
sector. -/
def activeTraceZeroSector_of_concreteActionZeroFiber
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw) :
    ActiveTraceZeroPrimeEdgeSector where
  sigma := C.sigma
  sigma_active := C.sigma_active
  sector := {
    loop := fun n hn => {
      leftPrime := (C.pick n hn).1
      rightPrime := (C.pick n hn).2
      trace_zero := by
        exact
          (su7GaugeFlowColorLoopAction_zero_iff_traceExact n
            (C.pick n hn).1 (C.pick n hn).2).mp
            (C.action_zero n hn)
    }
  }

/-- THEOREM 2: an active trace-zero sector produces the concrete action-zero
law. -/
def concreteActionZeroFiber_of_activeTraceZeroSector
    (A : ActiveTraceZeroPrimeEdgeSector) :
    SU7GaugeFlowConcreteActionZeroFiberLaw :=
  concreteActionZeroFiber_of_traceZeroPrimeEdgeSector
    A.sigma A.sigma_active A.sector

/-- THEOREM 3: the active-sector readout preserves the concrete action law's
prime-edge picks. -/
theorem activeTraceZeroSector_of_concreteActionZeroFiber_pick_eq
    (C : SU7GaugeFlowConcreteActionZeroFiberLaw)
    (n : ℕ) (hn : 2 ≤ n) :
    ((activeTraceZeroSector_of_concreteActionZeroFiber C).sector.loop
      n hn).leftPrime = (C.pick n hn).1 ∧
      ((activeTraceZeroSector_of_concreteActionZeroFiber C).sector.loop
        n hn).rightPrime = (C.pick n hn).2 :=
  ⟨rfl, rfl⟩

/-- THEOREM 4: the concrete action-zero law and the active trace-zero sector
are equivalent data. -/
def concreteActionZeroFiber_activeTraceZeroSectorEquiv :
    SU7GaugeFlowConcreteActionZeroFiberLaw ≃
      ActiveTraceZeroPrimeEdgeSector where
  toFun := activeTraceZeroSector_of_concreteActionZeroFiber
  invFun := concreteActionZeroFiber_of_activeTraceZeroSector
  left_inv := by
    intro C
    cases C with
    | mk sigma sigma_active pick action_zero =>
      simp [activeTraceZeroSector_of_concreteActionZeroFiber,
        concreteActionZeroFiber_of_activeTraceZeroSector,
        concreteActionZeroFiber_of_traceZeroPrimeEdgeSector]
  right_inv := by
    intro A
    cases A with
    | mk sigma sigma_active sector =>
      cases sector with
      | mk loop =>
        simp [activeTraceZeroSector_of_concreteActionZeroFiber,
          concreteActionZeroFiber_of_activeTraceZeroSector,
          concreteActionZeroFiber_of_traceZeroPrimeEdgeSector]

/-- THEOREM 5: concrete action-zero producer existence is equivalent to
active trace-zero sector existence. -/
theorem concreteActionZeroProducer_iff_activeTraceZeroSector :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      Nonempty ActiveTraceZeroPrimeEdgeSector := by
  constructor
  · intro H
    exact ⟨activeTraceZeroSector_of_concreteActionZeroFiber
      (Classical.choice H)⟩
  · intro H
    exact ⟨concreteActionZeroFiber_of_activeTraceZeroSector
      (Classical.choice H)⟩

/-- THEOREM 6: a gauge-flow trace-zero normalizer is exactly an active
trace-zero sector after choosing an active scalar. -/
def activeTraceZeroSector_of_gaugeFlowNormalizer
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (N : SU7GaugeFlowTraceZeroNormalizer) :
    ActiveTraceZeroPrimeEdgeSector where
  sigma := sigma
  sigma_active := hsigma
  sector := traceZeroPrimeEdgeSector_of_gaugeFlowNormalizer N

/-- THEOREM 7: primitive gauge dynamics produces an active trace-zero sector,
through the concrete action equivalence. -/
def activeTraceZeroSector_of_primitiveGaugeDynamics
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (G : SU7PrimitiveGaugeDynamicsNormalFormLaw) :
    ActiveTraceZeroPrimeEdgeSector :=
  activeTraceZeroSector_of_concreteActionZeroFiber
    (concreteActionZeroFiber_of_primitiveGaugeDynamics sigma hsigma G)

/-- THEOREM 8: spectrum-resolved alpha convergence produces an active
trace-zero sector, through the concrete action equivalence. -/
def activeTraceZeroSector_of_spectrumResolvedAlphaConvergentCarrier
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (C : SpectrumResolvedAlphaConvergentCarrier) :
    ActiveTraceZeroPrimeEdgeSector :=
  activeTraceZeroSector_of_concreteActionZeroFiber
    (concreteActionZeroFiber_of_spectrumResolvedAlphaConvergentCarrier
      sigma hsigma C)

/-! ## Certificate -/

/-- P844 certificate: concrete action-zero and active trace-zero sector are
equivalent producer objects. -/
structure ConcreteActionZeroActiveTraceZeroEquivalenceCertificate where
  concrete_to_active :
    SU7GaugeFlowConcreteActionZeroFiberLaw ->
      ActiveTraceZeroPrimeEdgeSector
  active_to_concrete :
    ActiveTraceZeroPrimeEdgeSector ->
      SU7GaugeFlowConcreteActionZeroFiberLaw
  concrete_active_equiv :
    SU7GaugeFlowConcreteActionZeroFiberLaw ≃
      ActiveTraceZeroPrimeEdgeSector
  producer_iff_active :
    SU7GaugeFlowConcreteActionZeroFiberProducer ↔
      Nonempty ActiveTraceZeroPrimeEdgeSector
  primitive_to_active :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SU7PrimitiveGaugeDynamicsNormalFormLaw ->
        ActiveTraceZeroPrimeEdgeSector
  spectrum_alpha_to_active :
    ∀ (sigma : ℝ), sigma ≠ 0 ->
      SpectrumResolvedAlphaConvergentCarrier ->
        ActiveTraceZeroPrimeEdgeSector

/-- THEOREM 9: canonical P844 equivalence certificate. -/
def concreteActionZeroActiveTraceZeroEquivalenceCertificate :
    ConcreteActionZeroActiveTraceZeroEquivalenceCertificate where
  concrete_to_active :=
    activeTraceZeroSector_of_concreteActionZeroFiber
  active_to_concrete :=
    concreteActionZeroFiber_of_activeTraceZeroSector
  concrete_active_equiv :=
    concreteActionZeroFiber_activeTraceZeroSectorEquiv
  producer_iff_active :=
    concreteActionZeroProducer_iff_activeTraceZeroSector
  primitive_to_active :=
    activeTraceZeroSector_of_primitiveGaugeDynamics
  spectrum_alpha_to_active :=
    activeTraceZeroSector_of_spectrumResolvedAlphaConvergentCarrier


end StandardModelConstraint
end SaturationMonoid
