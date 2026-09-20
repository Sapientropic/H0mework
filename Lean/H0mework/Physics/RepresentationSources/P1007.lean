import H0mework.Arithmetic.AtomicCodes.P1005

/-!
# Proposition 1007: block-incidence endpoint coding is not the producer

The first possible inhabitant producer would be to reuse the existing SU(7)
block/incidence generator and read endpoint codes directly from the four
carrier blocks.  This file proves that route is impossible: the block-code
endpoint generator cannot even hit endpoint balance at the concrete fiber
`n = 4`.

So the real producer cannot be the P993/P984 incidence orbit alone.  It has to
come from a deeper representation/tensor spectrum whose endpoint codes are not
just the finite block labels `0,1,2,3`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

set_option linter.defProp false

/-! ## The finite block-code endpoint attempt -/

/-- Same-carrier atom obtained by reading the endpoint code directly from a
SU(7) carrier block label. -/
def sameCarrierAtomOfCarrierBlock
    (block : SU7CarrierBlock) : SameCarrierSU7Atom :=
  sameCarrierAtomOfWeightAndCode
    (terminalWeightOfCarrierBlock block)
    (SU7CarrierBlock.code block)

/-- Same-carrier endpoint cell obtained directly from one SU(7) block
incidence. -/
def sameCarrierBlockCodeCell
    (n : ℕ) (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    SU7SameCarrierAtomicCell n where
  generated :=
    generatedTerminalColorCellOfRepresentationSlot n branch incidence
  leftAtom :=
    sameCarrierAtomOfCarrierBlock (SU7BlockIncidence.endpoints incidence).1
  rightAtom :=
    sameCarrierAtomOfCarrierBlock (SU7BlockIncidence.endpoints incidence).2
  atom_left_matches_weight := by
    simp [SameCarrierAtomMatchesWeight, sameCarrierAtomOfCarrierBlock,
      sameCarrierAtomOfWeightAndCode,
      generatedTerminalColorCellOfRepresentationSlot]
  atom_right_matches_weight := by
    simp [SameCarrierAtomMatchesWeight, sameCarrierAtomOfCarrierBlock,
      sameCarrierAtomOfWeightAndCode,
      generatedTerminalColorCellOfRepresentationSlot]
  allowed := by
    simp [SameCarrierGaugeAllowed,
      generatedTerminalColorCellOfRepresentationSlot]

/-- In the block-code endpoint attempt, endpoint codes are just the endpoint
block labels. -/
theorem sameCarrierBlockCodeCell_endpointResidual_eq
    (n : ℕ) (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    endpointBalanceResidual
        (sameCarrierBlockCodeCell n branch incidence) =
      ((SU7CarrierBlock.code (SU7BlockIncidence.endpoints incidence).1 : ℤ) +
          (SU7CarrierBlock.code
            (SU7BlockIncidence.endpoints incidence).2 : ℤ)) -
        ((2 * n : ℕ) : ℤ) := by
  rfl

/-! ## The concrete failure at fiber four -/

/-- The block-code endpoint attempt cannot balance the fiber `n = 4`. -/
theorem endpointBalanceResidual_blockCodeCell_four_ne_zero
    (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    endpointBalanceResidual
        (sameCarrierBlockCodeCell 4 branch incidence) ≠ 0 := by
  cases incidence <;>
    simp [endpointBalanceResidual, sameCarrierBlockCodeCell,
      sameCarrierAtomOfCarrierBlock, sameCarrierAtomOfWeightAndCode,
      sameCarrierAtomCode, SU7BlockIncidence.endpoints,
      SU7CarrierBlock.code]

/-- Therefore no block-code endpoint cell at `n = 4` can hit the concrete
atomic zero target. -/
theorem not_concreteAtomicZero_blockCodeCell_four
    (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    ¬ SameCarrierConcreteAtomicZero
        (sameCarrierBlockCodeCell 4 branch incidence) := by
  intro hzero
  exact
    endpointBalanceResidual_blockCodeCell_four_ne_zero branch incidence
      hzero.2.1

/-- Nor can it hit the tensor-atomic zero target for any faithful tensor
coding. -/
theorem not_tensorAtomicZero_blockCodeCell_four
    (C : SameCarrierWeightTensorCoding)
    (branch : SU3FlagSchubertCell)
    (incidence : SU7BlockIncidence) :
    ¬ SameCarrierTensorAtomicZero C
        (sameCarrierBlockCodeCell 4 branch incidence) := by
  intro hzero
  exact
    endpointBalanceResidual_blockCodeCell_four_ne_zero branch incidence
      hzero.2.1

/-- The block-code endpoint generator fails at fiber `4` as an entire
generated family, independently of the Schubert branch and incidence slot. -/
theorem blockCodeEndpointGenerator_fails_fiber_four :
    ∀ branch : SU3FlagSchubertCell,
      ∀ incidence : SU7BlockIncidence,
        ¬ SameCarrierConcreteAtomicZero
          (sameCarrierBlockCodeCell 4 branch incidence) := by
  intro branch incidence
  exact not_concreteAtomicZero_blockCodeCell_four branch incidence


end StandardModelConstraint
end SaturationMonoid
