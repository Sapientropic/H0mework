import H0mework.Arithmetic.AtomicCodes.P1003

/-!
# Proposition 1004: the full-zero gate is exactly endpoint-atomic balance

P1003 showed that the P1001 `(n,n)` endpoint candidate is blocked by a real
endpoint-atomicity readout.  This file turns that obstruction into the hard
same-carrier gate: once the concrete endpoint-atomic readout is installed,
full zero is equivalent to a cell whose color trace, endpoint balance, and
both endpoint atomicity predicates all vanish/hold.

The file does not create a new endpoint producer.  It proves the exact shape
that such a producer must hit.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Concrete endpoint-atomic full-zero object -/

/-- Same-carrier object built from an arbitrary endpoint cell with the concrete
endpoint-atomicity readout and the already-produced alpha source readout. -/
def sameCarrierObjectOfCellWithEndpointAtomicReadout
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SameCarrierObject n where
  endpointCell := cell
  alphaSource := alphaStrongFourSourceIndependentContribution
  atomIrreducibilityReadout := sameCarrierEndpointAtomicReadout

/-! ## Readout exactness -/

/-- The concrete endpoint-atomic readout is zero exactly on endpoint-atomic
same-carrier atoms. -/
theorem sameCarrierEndpointAtomicReadout_zero_iff_atomAtomic
    (a : SameCarrierSU7Atom) :
    sameCarrierEndpointAtomicReadout a = 0 ↔ SameCarrierAtomAtomic a := by
  classical
  by_cases h : SameCarrierAtomAtomic a
  · simp [sameCarrierEndpointAtomicReadout, h]
  · simp [sameCarrierEndpointAtomicReadout, h]

/-- The atom residual of the concrete readout is zero exactly when both
same-carrier endpoints are atomic. -/
theorem sameCarrierAtomIrreducibilityResidual_zero_iff_endpointAtomicPair
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    sameCarrierAtomIrreducibilityResidual
        (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) = 0 ↔
      SameCarrierAtomAtomic cell.leftAtom ∧
        SameCarrierAtomAtomic cell.rightAtom := by
  classical
  by_cases hleft : SameCarrierAtomAtomic cell.leftAtom <;>
    by_cases hright : SameCarrierAtomAtomic cell.rightAtom <;>
      simp [sameCarrierAtomIrreducibilityResidual,
        sameCarrierObjectOfCellWithEndpointAtomicReadout,
        sameCarrierEndpointAtomicReadout, hleft, hright]

/-- The alpha residual remains zero for every endpoint cell because the alpha
source readout is the independent four-source producer. -/
theorem sameCarrierObjectOfCell_endpointAtomic_alpha_zero
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    sameCarrierAlphaConvergenceResidual
        (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) = 0 := by
  unfold sameCarrierAlphaConvergenceResidual
    sameCarrierObjectOfCellWithEndpointAtomicReadout
  rw [alphaStrongIndependentFourSource_inverseResidual]
  norm_num

/-! ## The hard gate -/

/-- Concrete full-zero target for the same-carrier endpoint layer. -/
def SameCarrierConcreteAtomicZero
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) : Prop :=
  colorTraceResidual cell = 0 ∧
    endpointBalanceResidual cell = 0 ∧
      SameCarrierAtomAtomic cell.leftAtom ∧
        SameCarrierAtomAtomic cell.rightAtom

/-- Under the concrete endpoint-atomic readout, same-carrier full zero is
exactly concrete endpoint-atomic balance. -/
theorem sameCarrierFullZero_iff_concreteAtomicZero
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SameCarrierFullZero
        (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) ↔
      SameCarrierConcreteAtomicZero cell := by
  constructor
  · intro hzero
    unfold SameCarrierFullZero sameCarrierResidualVector at hzero
    have hpair :
        (sameCarrierPhysicalTraceResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell),
          sameCarrierEndpointResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell)) =
          (0, 0) :=
      congrArg Prod.fst hzero
    have hatomPair :
        (sameCarrierAtomIrreducibilityResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell),
          sameCarrierAlphaConvergenceResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell)) =
          (0, 0) :=
      congrArg Prod.snd hzero
    have htrace :
        colorTraceResidual cell = 0 := by
      unfold sameCarrierPhysicalTraceResidual
        sameCarrierObjectOfCellWithEndpointAtomicReadout at hpair
      exact congrArg Prod.fst hpair
    have hendpoint :
        endpointBalanceResidual cell = 0 := by
      unfold sameCarrierEndpointResidual
        sameCarrierObjectOfCellWithEndpointAtomicReadout at hpair
      exact congrArg Prod.snd hpair
    have hatoms :
        SameCarrierAtomAtomic cell.leftAtom ∧
          SameCarrierAtomAtomic cell.rightAtom := by
      have hsum :
          sameCarrierAtomIrreducibilityResidual
              (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) =
            0 :=
        congrArg Prod.fst hatomPair
      exact
        (sameCarrierAtomIrreducibilityResidual_zero_iff_endpointAtomicPair
          cell).mp hsum
    exact ⟨htrace, hendpoint, hatoms.1, hatoms.2⟩
  · intro hconcrete
    rcases hconcrete with ⟨htrace, hendpoint, hleft, hright⟩
    unfold SameCarrierFullZero sameCarrierResidualVector
      sameCarrierPhysicalTraceResidual sameCarrierEndpointResidual
    have hatom :
        sameCarrierAtomIrreducibilityResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) = 0 := by
      exact
        (sameCarrierAtomIrreducibilityResidual_zero_iff_endpointAtomicPair
          cell).mpr ⟨hleft, hright⟩
    have halpha :
        sameCarrierAlphaConvergenceResidual
            (sameCarrierObjectOfCellWithEndpointAtomicReadout cell) = 0 :=
      sameCarrierObjectOfCell_endpointAtomic_alpha_zero cell
    simpa [sameCarrierObjectOfCellWithEndpointAtomicReadout, htrace,
      hendpoint] using And.intro hatom halpha

/-- The existential full-zero fiber for the concrete endpoint-atomic readout is
exactly the existential concrete endpoint-atomic zero fiber. -/
theorem sameCarrierEndpointAtomicFullZero_iff_existsConcreteAtomicZero
    {n : ℕ} :
    (∃ cell : SU7SameCarrierAtomicCell n,
        SameCarrierFullZero
          (sameCarrierObjectOfCellWithEndpointAtomicReadout cell)) ↔
      ∃ cell : SU7SameCarrierAtomicCell n,
        SameCarrierConcreteAtomicZero cell := by
  constructor
  · rintro ⟨cell, hzero⟩
    exact ⟨cell,
      (sameCarrierFullZero_iff_concreteAtomicZero cell).mp hzero⟩
  · rintro ⟨cell, hzero⟩
    exact ⟨cell,
      (sameCarrierFullZero_iff_concreteAtomicZero cell).mpr hzero⟩

/-- A concrete endpoint-atomic zero cell immediately gives the endpoint-balance
equation on the same carrier. -/
theorem concreteAtomicZero_to_sameCarrier_balance
    {n : ℕ} {cell : SU7SameCarrierAtomicCell n}
    (hzero : SameCarrierConcreteAtomicZero cell) :
    sameCarrierAtomCode cell.leftAtom +
        sameCarrierAtomCode cell.rightAtom =
      2 * n :=
  endpoint_zero_to_sameCarrier_balance cell hzero.2.1


end StandardModelConstraint
end SaturationMonoid
