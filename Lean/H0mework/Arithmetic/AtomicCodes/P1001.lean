import H0mework.Physics.ColorLoops.P997

/-!
# Proposition 1001: same-carrier endpoint-balance producer

P997 stops at the physical zero-trace projection.  This file adds the requested
same-carrier endpoint layer without importing the downstream arithmetic throat
and without using any number-theoretic endpoint predicate.  The atom has two
coordinates:

* the SU(7) terminal block-weight readout that must match the generated cell;
* an endpoint code used only by the endpoint-balance residual.

The main theorem produces a generated SU(7) terminal cell plus two matching
same-carrier atoms whose two residual components vanish.  The separate
faithfulness theorem that makes endpoint codes representation-theoretically
atomic is intentionally not asserted here.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Same-carrier atoms below endpoint faithfulness -/

/-- Same-carrier atomic weight: one coordinate matches the SU(7) generated
terminal block surface; the other is the endpoint-balance code. -/
structure SameCarrierSU7AtomicWeight where
  blockWeight : Fin 7 -> ℤ
  endpointCode : ℕ

/-- Same-carrier atom.  This layer carries no endpoint faithfulness predicate. -/
structure SameCarrierSU7Atom where
  weight : SameCarrierSU7AtomicWeight

/-- Endpoint code read from a same-carrier atom. -/
def sameCarrierAtomCode (a : SameCarrierSU7Atom) : ℕ :=
  a.weight.endpointCode

/-- Weight matching between a same-carrier atom and a generated terminal
SU(7) block-weight readout. -/
def SameCarrierAtomMatchesWeight
    (a : SameCarrierSU7Atom) (w : Fin 7 -> ℤ) : Prop :=
  a.weight.blockWeight = w

/-- Gauge allowance read at the generated SU(7) cell layer. -/
def SameCarrierGaugeAllowed
    {n : ℕ} (cell : SU7GeneratedTerminalColorCell n) : Prop :=
  cell.gaugeAllowed

/-- The same-carrier atomic cell requested by the producer spine. -/
structure SU7SameCarrierAtomicCell (n : ℕ) where
  generated : SU7GeneratedTerminalColorCell n
  leftAtom : SameCarrierSU7Atom
  rightAtom : SameCarrierSU7Atom
  atom_left_matches_weight :
    SameCarrierAtomMatchesWeight leftAtom generated.leftWeight
  atom_right_matches_weight :
    SameCarrierAtomMatchesWeight rightAtom generated.rightWeight
  allowed : SameCarrierGaugeAllowed generated

/-! ## Two-component residual -/

/-- Physical cell obtained by projecting the generated terminal cell. -/
def sameCarrierPhysicalCell
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SU7TerminalPhysicalBranchCell n :=
  terminalPhysicalCellOfGeneratedColorCell cell.generated

/-- Color trace residual of the generated SU(7) carrier component. -/
def colorTraceResidual
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) : ℤ :=
  physicalColorLoopTrace (sameCarrierPhysicalCell cell)

/-- Endpoint-balance residual of the same-carrier atom-code component. -/
def endpointBalanceResidual
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) : ℤ :=
  ((sameCarrierAtomCode cell.leftAtom : ℤ) +
      (sameCarrierAtomCode cell.rightAtom : ℤ)) -
    ((2 * n : ℕ) : ℤ)

/-- Full same-carrier residual: color trace plus endpoint balance. -/
def fullCarrierResidual
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) : ℤ × ℤ :=
  (colorTraceResidual cell, endpointBalanceResidual cell)

/-! ## Canonical producer cell -/

/-- Same-carrier atom with a chosen block-weight readout and endpoint code. -/
def sameCarrierAtomOfWeightAndCode
    (w : Fin 7 -> ℤ) (code : ℕ) : SameCarrierSU7Atom where
  weight := { blockWeight := w, endpointCode := code }

@[simp] theorem sameCarrierAtomOfWeightAndCode_matches
    (w : Fin 7 -> ℤ) (code : ℕ) :
    SameCarrierAtomMatchesWeight
      (sameCarrierAtomOfWeightAndCode w code) w := rfl

@[simp] theorem sameCarrierAtomOfWeightAndCode_code
    (w : Fin 7 -> ℤ) (code : ℕ) :
    sameCarrierAtomCode (sameCarrierAtomOfWeightAndCode w code) = code := rfl

/-- Canonical generated zero cell used by the same-carrier producer. -/
def sameCarrierGeneratedZeroCell (n : ℕ) :
    SU7GeneratedTerminalColorCell n :=
  generatedTerminalColorCellOfRepresentationSlot n
    SU3FlagSchubertCell.e
    SU7BlockIncidence.positiveNegativeSinglet

/-- Canonical same-carrier atomic zero candidate. -/
def sameCarrierAtomicZeroCandidate (n : ℕ) :
    SU7SameCarrierAtomicCell n where
  generated := sameCarrierGeneratedZeroCell n
  leftAtom :=
    sameCarrierAtomOfWeightAndCode
      (sameCarrierGeneratedZeroCell n).leftWeight n
  rightAtom :=
    sameCarrierAtomOfWeightAndCode
      (sameCarrierGeneratedZeroCell n).rightWeight n
  atom_left_matches_weight := by
    simp [sameCarrierGeneratedZeroCell]
  atom_right_matches_weight := by
    simp [sameCarrierGeneratedZeroCell]
  allowed := by
    simp [SameCarrierGaugeAllowed, sameCarrierGeneratedZeroCell,
      generatedTerminalColorCellOfRepresentationSlot]

/-- The canonical same-carrier candidate has zero color trace. -/
theorem sameCarrierAtomicZeroCandidate_colorTrace_zero
    (n : ℕ) :
    colorTraceResidual (sameCarrierAtomicZeroCandidate n) = 0 := by
  unfold colorTraceResidual sameCarrierPhysicalCell
    sameCarrierAtomicZeroCandidate sameCarrierGeneratedZeroCell
  exact physicalColorLoopTrace_eq_zero_of_exact
    (physicalColorLoopExact_of_generated_exact
      (generatedRepresentationSingletTerminalCell_exact n
        SU3FlagSchubertCell.e))

/-- The canonical same-carrier candidate has zero endpoint balance. -/
theorem sameCarrierAtomicZeroCandidate_endpointBalance_zero
    (n : ℕ) :
    endpointBalanceResidual (sameCarrierAtomicZeroCandidate n) = 0 := by
  simp [endpointBalanceResidual, sameCarrierAtomicZeroCandidate,
    sameCarrierGeneratedZeroCell, sameCarrierAtomCode,
    sameCarrierAtomOfWeightAndCode]
  omega

/-- Pre-atomic same-carrier endpoint-balance producer: every active fiber has
a generated SU(7) terminal cell plus two matching same-carrier atoms whose
color and endpoint-balance residuals vanish.

This theorem intentionally does not assert endpoint/tensor atomicity.  P1003
blocks the naive `(n,n)` candidate once atomicity is made real; P1004/P1005
identify the remaining producer as the tensor-atomic full-zero target. -/
theorem su7AtomicZeroEndpointProducer :
    ∀ n : ℕ, 2 ≤ n ->
      ∃ cell : SU7SameCarrierAtomicCell n,
        fullCarrierResidual cell = (0, 0) := by
  intro n _hn
  refine ⟨sameCarrierAtomicZeroCandidate n, ?_⟩
  ext <;> simp [fullCarrierResidual,
    sameCarrierAtomicZeroCandidate_colorTrace_zero,
    sameCarrierAtomicZeroCandidate_endpointBalance_zero]

/-- Endpoint zero is exactly the integer balance readout for same-carrier
atoms.  This is only the endpoint-balance projection; it does not assert any
separate endpoint faithfulness predicate. -/
theorem endpoint_zero_to_sameCarrier_balance
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n)
    (hzero : endpointBalanceResidual cell = 0) :
    sameCarrierAtomCode cell.leftAtom + sameCarrierAtomCode cell.rightAtom =
      2 * n := by
  unfold endpointBalanceResidual at hzero
  omega


end StandardModelConstraint
end SaturationMonoid
