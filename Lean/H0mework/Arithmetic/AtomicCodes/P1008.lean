import H0mework.Physics.RepresentationSources.P1007

/-!
# Proposition 1008: any bounded endpoint spectrum cannot be the producer

P1007 refuted the concrete block-code endpoint attempt.  This file proves the
general reason: any same-carrier endpoint generator whose left/right endpoint
codes are uniformly bounded fails on sufficiently large even fibers.

Thus the inhabitant producer demanded by P1004/P1005 must contain an unbounded
representation/tensor endpoint spectrum.  A finite relabeling of the existing
SU(7) block-incidence carrier cannot be enough.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Bounded endpoint-code spectra fail -/

/-- A same-carrier cell whose endpoint codes are bounded by `bound`. -/
def SameCarrierEndpointCodesBounded
    (bound : ℕ) {n : ℕ}
    (cell : SU7SameCarrierAtomicCell n) : Prop :=
  sameCarrierAtomCode cell.leftAtom ≤ bound ∧
    sameCarrierAtomCode cell.rightAtom ≤ bound

/-- If both endpoint codes are bounded by `bound`, the endpoint-balance
residual cannot vanish on any fiber `n > bound`. -/
theorem endpointBalanceResidual_ne_zero_of_endpointCodesBounded
    {bound n : ℕ} {cell : SU7SameCarrierAtomicCell n}
    (hbounded : SameCarrierEndpointCodesBounded bound cell)
    (hgt : bound < n) :
    endpointBalanceResidual cell ≠ 0 := by
  intro hzero
  have hsum :
      sameCarrierAtomCode cell.leftAtom +
          sameCarrierAtomCode cell.rightAtom =
        2 * n :=
    endpoint_zero_to_sameCarrier_balance cell hzero
  rcases hbounded with ⟨hleft, hright⟩
  omega

/-- Consequently, no bounded endpoint-code cell can hit the concrete atomic
zero target above its bound. -/
theorem not_concreteAtomicZero_of_endpointCodesBounded
    {bound n : ℕ} {cell : SU7SameCarrierAtomicCell n}
    (hbounded : SameCarrierEndpointCodesBounded bound cell)
    (hgt : bound < n) :
    ¬ SameCarrierConcreteAtomicZero cell := by
  intro hzero
  exact
    endpointBalanceResidual_ne_zero_of_endpointCodesBounded hbounded hgt
      hzero.2.1

/-- The same bounded-spectrum obstruction holds for the tensor target. -/
theorem not_tensorAtomicZero_of_endpointCodesBounded
    (C : SameCarrierWeightTensorCoding)
    {bound n : ℕ} {cell : SU7SameCarrierAtomicCell n}
    (hbounded : SameCarrierEndpointCodesBounded bound cell)
    (hgt : bound < n) :
    ¬ SameCarrierTensorAtomicZero C cell := by
  intro hzero
  exact
    endpointBalanceResidual_ne_zero_of_endpointCodesBounded hbounded hgt
      hzero.2.1

/-! ## No uniformly bounded producer -/

/-- A concrete endpoint producer whose generated cells all use endpoint codes
bounded by one global `bound`. -/
def BoundedConcreteAtomicEndpointProducer (bound : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ cell : SU7SameCarrierAtomicCell n,
      SameCarrierEndpointCodesBounded bound cell ∧
        SameCarrierConcreteAtomicZero cell

/-- No uniformly bounded concrete endpoint-code producer can cover all active
fibers. -/
theorem no_boundedConcreteAtomicEndpointProducer
    (bound : ℕ) :
    ¬ BoundedConcreteAtomicEndpointProducer bound := by
  intro hproducer
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases hproducer n hn with ⟨cell, hbounded, hzero⟩
  exact not_concreteAtomicZero_of_endpointCodesBounded
    hbounded hgt hzero

/-! ## Any successful producer is necessarily unbounded -/

/-- Any concrete full producer must generate endpoint codes above every fixed
bound.  This is the exact shape constraint left by P1008: the real inhabitant
producer cannot be a finite relabeling or bounded lookup table. -/
theorem concreteAtomicProducer_forces_unboundedEndpointCodes
    (H :
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7SameCarrierAtomicCell n,
          SameCarrierConcreteAtomicZero cell) :
    ∀ bound : ℕ,
      ∃ n : ℕ,
        ∃ cell : SU7SameCarrierAtomicCell n,
          2 ≤ n ∧
            bound < n ∧
              SameCarrierConcreteAtomicZero cell ∧
                ¬ SameCarrierEndpointCodesBounded bound cell := by
  intro bound
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases H n hn with ⟨cell, hzero⟩
  refine ⟨n, cell, hn, hgt, hzero, ?_⟩
  intro hbounded
  exact not_concreteAtomicZero_of_endpointCodesBounded
    hbounded hgt hzero

/-- A tensor endpoint producer whose generated cells all use endpoint codes
bounded by one global `bound`. -/
def BoundedTensorAtomicEndpointProducer
    (C : SameCarrierWeightTensorCoding) (bound : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ cell : SU7SameCarrierAtomicCell n,
      SameCarrierEndpointCodesBounded bound cell ∧
        SameCarrierTensorAtomicZero C cell

/-- No uniformly bounded tensor endpoint-code producer can cover all active
fibers. -/
theorem no_boundedTensorAtomicEndpointProducer
    (C : SameCarrierWeightTensorCoding)
    (bound : ℕ) :
    ¬ BoundedTensorAtomicEndpointProducer C bound := by
  intro hproducer
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases hproducer n hn with ⟨cell, hbounded, hzero⟩
  exact not_tensorAtomicZero_of_endpointCodesBounded C
    hbounded hgt hzero

/-- Any tensor-atomic full producer must generate endpoint codes above every
fixed bound. -/
theorem tensorAtomicProducer_forces_unboundedEndpointCodes
    (C : SameCarrierWeightTensorCoding)
    (H :
      ∀ n : ℕ, 2 ≤ n ->
        ∃ cell : SU7SameCarrierAtomicCell n,
          SameCarrierTensorAtomicZero C cell) :
    ∀ bound : ℕ,
      ∃ n : ℕ,
        ∃ cell : SU7SameCarrierAtomicCell n,
          2 ≤ n ∧
            bound < n ∧
              SameCarrierTensorAtomicZero C cell ∧
                ¬ SameCarrierEndpointCodesBounded bound cell := by
  intro bound
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases H n hn with ⟨cell, hzero⟩
  refine ⟨n, cell, hn, hgt, hzero, ?_⟩
  intro hbounded
  exact not_tensorAtomicZero_of_endpointCodesBounded C
    hbounded hgt hzero


end StandardModelConstraint
end SaturationMonoid
