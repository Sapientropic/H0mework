import H0mework.Arithmetic.AtomicCodes.P1015

/-!
# Proposition 1016: a successful SU(7) tensor-atom lift producer is unbounded

P1015 ruled out fixed finite SU(7) tensor-atom tables.  This file records the
positive shape forced by the same obstruction: any successful P1014-style
producer must generate SU(7) tensor atoms with unbounded endpoint codes.

This is still not the inhabitant producer.  It is the exact spectrum condition
the inhabitant producer must satisfy, stated without importing any downstream
arithmetic throat and without using primality as a cell input.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## P1014-style producer shape -/

/-- A P1014-style SU(7) tensor-atom lift producer.

For each active fiber it supplies a generated terminal color cell, two SU(7)
tensor-irreducible atoms, and a P1011 zero cell obtained by the P1014 lift.
-/
def SU7TensorAtomLiftProducer
    (C : SU7WeightTensorCoding) : Prop :=
  ∀ n : ℕ, 2 ≤ n ->
    ∃ generated : SU7GeneratedTerminalColorCell n,
      ∃ left right : SU7TensorIrreducibleAtom C,
        ∃ allowed : SameCarrierGaugeAllowed generated,
          SameCarrierTensorAtomicCellZero
            (sameCarrierTensorAtomicCellOfSU7TensorAtoms
              generated left right allowed)

/-- A successful P1014-style producer has unbounded SU(7) tensor-atom endpoint
codes. -/
theorem su7TensorAtomLiftProducer_forces_unboundedAtomCodes
    (C : SU7WeightTensorCoding)
    (H : SU7TensorAtomLiftProducer C) :
    ∀ bound : ℕ,
      ∃ n : ℕ,
        ∃ generated : SU7GeneratedTerminalColorCell n,
          ∃ left right : SU7TensorIrreducibleAtom C,
            ∃ allowed : SameCarrierGaugeAllowed generated,
              2 ≤ n ∧
                bound < n ∧
                  SameCarrierTensorAtomicCellZero
                    (sameCarrierTensorAtomicCellOfSU7TensorAtoms
                      generated left right allowed) ∧
                    (bound < left.weight.code ∨
                      bound < right.weight.code) := by
  intro bound
  let n := bound + 2
  have hn : 2 ≤ n := by omega
  have hgt : bound < n := by omega
  rcases H n hn with ⟨generated, left, right, allowed, hzero⟩
  let tcell :=
    sameCarrierTensorAtomicCellOfSU7TensorAtoms
      generated left right allowed
  have hendpoint :
      endpointBalanceResidual (sameCarrierCellOfTensorAtomicCell tcell) =
        0 := by
    unfold SameCarrierTensorAtomicCellZero fullCarrierResidualOfTensorAtomicCell
      fullCarrierResidual at hzero
    exact congrArg Prod.snd hzero
  have hsum :
      left.weight.code + right.weight.code = 2 * n := by
    have hbalance :=
      endpoint_zero_to_sameCarrier_balance
        (sameCarrierCellOfTensorAtomicCell tcell) hendpoint
    exact hbalance
  have hunbounded :
      bound < left.weight.code ∨ bound < right.weight.code := by
    omega
  exact
    ⟨n, generated, left, right, allowed, hn, hgt, hzero, hunbounded⟩

/-- A successful P1014-style producer cannot have all generated tensor-atom
codes bounded by one global bound. -/
theorem no_globalBound_for_SU7TensorAtomLiftProducer
    (C : SU7WeightTensorCoding)
    (H : SU7TensorAtomLiftProducer C)
    (bound : ℕ) :
    ¬
      (∀ n : ℕ, 2 ≤ n ->
        ∀ generated : SU7GeneratedTerminalColorCell n,
          ∀ left right : SU7TensorIrreducibleAtom C,
            ∀ allowed : SameCarrierGaugeAllowed generated,
              SameCarrierTensorAtomicCellZero
                (sameCarrierTensorAtomicCellOfSU7TensorAtoms
                  generated left right allowed) ->
                left.weight.code ≤ bound ∧ right.weight.code ≤ bound) := by
  intro hbounded
  rcases su7TensorAtomLiftProducer_forces_unboundedAtomCodes C H bound with
    ⟨n, generated, left, right, allowed, hn, _hgt, hzero, hlarge⟩
  have hb := hbounded n hn generated left right allowed hzero
  omega

/-! ## Certificate -/

/-- P1016 certificate: the remaining inhabitant producer must be an unbounded
SU(7) tensor-atom spectrum. -/
structure SU7TensorAtomLiftUnboundedSpectrumCertificate where
  forces_unbounded_codes :
    ∀ (C : SU7WeightTensorCoding),
      SU7TensorAtomLiftProducer C ->
        ∀ bound : ℕ,
          ∃ n : ℕ,
            ∃ generated : SU7GeneratedTerminalColorCell n,
              ∃ left right : SU7TensorIrreducibleAtom C,
                ∃ allowed : SameCarrierGaugeAllowed generated,
                  2 ≤ n ∧
                    bound < n ∧
                      SameCarrierTensorAtomicCellZero
                        (sameCarrierTensorAtomicCellOfSU7TensorAtoms
                          generated left right allowed) ∧
                        (bound < left.weight.code ∨
                          bound < right.weight.code)
  no_global_bound :
    ∀ (C : SU7WeightTensorCoding)
      (_ : SU7TensorAtomLiftProducer C)
      (bound : ℕ),
      ¬
        (∀ n : ℕ, 2 ≤ n ->
          ∀ generated : SU7GeneratedTerminalColorCell n,
            ∀ left right : SU7TensorIrreducibleAtom C,
              ∀ allowed : SameCarrierGaugeAllowed generated,
                SameCarrierTensorAtomicCellZero
                  (sameCarrierTensorAtomicCellOfSU7TensorAtoms
                    generated left right allowed) ->
                  left.weight.code ≤ bound ∧ right.weight.code ≤ bound)

/-- THEOREM 1: canonical unbounded-spectrum certificate. -/
def su7TensorAtomLiftUnboundedSpectrumCertificate :
    SU7TensorAtomLiftUnboundedSpectrumCertificate where
  forces_unbounded_codes :=
    su7TensorAtomLiftProducer_forces_unboundedAtomCodes
  no_global_bound :=
    no_globalBound_for_SU7TensorAtomLiftProducer


end StandardModelConstraint
end SaturationMonoid
