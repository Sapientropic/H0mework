import H0mework.Arithmetic.AtomicCodes.P1004

/-!
# Proposition 1005: same-carrier tensor atomicity replaces the placeholder

The historical `IsIrreducibleRepresentation` predicate is still a compatibility
placeholder in older receipts.  This file installs the replacement predicate
on the new same-carrier track: irreducibility is stated as indecomposability
with respect to a tensor coding of same-carrier weights.

The theorem is not a new endpoint producer.  It proves that the tensor
predicate is exactly the P1004 endpoint-atomic gate when the tensor coding is
faithful to endpoint multiplication and can lift endpoint factorizations back
to tensor factorizations.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

set_option linter.defProp false

/-! ## Same-carrier tensor coding -/

/-- Tensor coding for same-carrier weights.  It keeps the representation-side
operation separate from endpoint arithmetic while requiring two faithfulness
laws:

* tensoring multiplies endpoint codes;
* every endpoint factorization lifts to an actual tensor factorization of the
  same weight.
-/
structure SameCarrierWeightTensorCoding where
  tensor :
    SameCarrierSU7AtomicWeight ->
      SameCarrierSU7AtomicWeight ->
        SameCarrierSU7AtomicWeight
  tensor_endpointCode :
    ∀ u v,
      (tensor u v).endpointCode = u.endpointCode * v.endpointCode
  lift_endpoint_factorization :
    ∀ (w : SameCarrierSU7AtomicWeight) (a b : ℕ),
      w.endpointCode = a * b ->
        ∃ u v,
          tensor u v = w ∧
            u.endpointCode = a ∧
              v.endpointCode = b

/-- Tensor indecomposability of a same-carrier weight. -/
def SameCarrierTensorIrreducible
    (C : SameCarrierWeightTensorCoding)
    (w : SameCarrierSU7AtomicWeight) : Prop :=
  2 ≤ w.endpointCode ∧
    ∀ u v : SameCarrierSU7AtomicWeight,
      C.tensor u v = w ->
        u.endpointCode = 1 ∨ v.endpointCode = 1

/-- Tensor atomicity of a same-carrier atom. -/
def SameCarrierTensorAtomAtomic
    (C : SameCarrierWeightTensorCoding)
    (a : SameCarrierSU7Atom) : Prop :=
  SameCarrierTensorIrreducible C a.weight

/-! ## Tensor atomicity is the same hard gate as endpoint atomicity -/

/-- Faithful tensor indecomposability is exactly endpoint atomicity. -/
theorem sameCarrierTensorIrreducible_iff_endpointAtomic
    (C : SameCarrierWeightTensorCoding)
    (w : SameCarrierSU7AtomicWeight) :
    SameCarrierTensorIrreducible C w ↔
      SameCarrierEndpointAtomic w.endpointCode := by
  constructor
  · intro h
    rcases h with ⟨h2, hfactor⟩
    refine ⟨h2, ?_⟩
    intro a b hmul
    rcases C.lift_endpoint_factorization w a b hmul with
      ⟨u, v, htensor, hu, hv⟩
    rcases hfactor u v htensor with hunit | hunit
    · left
      rw [← hu]
      exact hunit
    · right
      rw [← hv]
      exact hunit
  · intro h
    rcases h with ⟨h2, hfactor⟩
    refine ⟨h2, ?_⟩
    intro u v htensor
    have hcodeFromEq :
        (C.tensor u v).endpointCode = w.endpointCode := by
      simpa using
        congrArg SameCarrierSU7AtomicWeight.endpointCode htensor
    have hcode :
        w.endpointCode = u.endpointCode * v.endpointCode := by
      rw [← hcodeFromEq]
      exact C.tensor_endpointCode u v
    exact hfactor u.endpointCode v.endpointCode hcode

/-- Atom-level tensor atomicity is exactly the concrete atom-atomic gate. -/
theorem sameCarrierTensorAtomAtomic_iff_atomAtomic
    (C : SameCarrierWeightTensorCoding)
    (a : SameCarrierSU7Atom) :
    SameCarrierTensorAtomAtomic C a ↔
      SameCarrierAtomAtomic a := by
  change
    SameCarrierTensorIrreducible C a.weight ↔
      SameCarrierEndpointAtomic a.weight.endpointCode
  exact sameCarrierTensorIrreducible_iff_endpointAtomic C a.weight

/-! ## Tensor readout and full-zero gate -/

/-- Concrete atom residual readout using tensor atomicity. -/
noncomputable def sameCarrierTensorAtomicReadout
    (C : SameCarrierWeightTensorCoding)
    (a : SameCarrierSU7Atom) : ℤ :=
  by
    classical
    exact if SameCarrierTensorAtomAtomic C a then 0 else 1

/-- The tensor readout is zero exactly on tensor-atomic atoms. -/
theorem sameCarrierTensorAtomicReadout_zero_iff_tensorAtomic
    (C : SameCarrierWeightTensorCoding)
    (a : SameCarrierSU7Atom) :
    sameCarrierTensorAtomicReadout C a = 0 ↔
      SameCarrierTensorAtomAtomic C a := by
  classical
  by_cases h : SameCarrierTensorAtomAtomic C a
  · simp [sameCarrierTensorAtomicReadout, h]
  · simp [sameCarrierTensorAtomicReadout, h]

/-- Tensor and endpoint readouts agree under faithful tensor coding. -/
theorem sameCarrierTensorAtomicReadout_eq_endpointAtomicReadout
    (C : SameCarrierWeightTensorCoding)
    (a : SameCarrierSU7Atom) :
    sameCarrierTensorAtomicReadout C a =
      sameCarrierEndpointAtomicReadout a := by
  classical
  by_cases h : SameCarrierTensorAtomAtomic C a
  · have hendpoint : SameCarrierAtomAtomic a :=
      (sameCarrierTensorAtomAtomic_iff_atomAtomic C a).mp h
    simp [sameCarrierTensorAtomicReadout, sameCarrierEndpointAtomicReadout,
      h, hendpoint]
  · have hendpoint : ¬ SameCarrierAtomAtomic a := by
      intro ha
      exact h ((sameCarrierTensorAtomAtomic_iff_atomAtomic C a).mpr ha)
    simp [sameCarrierTensorAtomicReadout, sameCarrierEndpointAtomicReadout,
      h, hendpoint]

/-- Same-carrier object using the tensor-atomic residual readout. -/
def sameCarrierObjectOfCellWithTensorAtomicReadout
    (C : SameCarrierWeightTensorCoding)
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SameCarrierObject n where
  endpointCell := cell
  alphaSource := alphaStrongFourSourceIndependentContribution
  atomIrreducibilityReadout := sameCarrierTensorAtomicReadout C

/-- Tensor full-zero target for the same-carrier endpoint layer. -/
def SameCarrierTensorAtomicZero
    (C : SameCarrierWeightTensorCoding)
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) : Prop :=
  colorTraceResidual cell = 0 ∧
    endpointBalanceResidual cell = 0 ∧
      SameCarrierTensorAtomAtomic C cell.leftAtom ∧
        SameCarrierTensorAtomAtomic C cell.rightAtom

/-- The tensor full-zero gate is equivalent to the concrete endpoint gate. -/
theorem sameCarrierTensorAtomicZero_iff_concreteAtomicZero
    (C : SameCarrierWeightTensorCoding)
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SameCarrierTensorAtomicZero C cell ↔
      SameCarrierConcreteAtomicZero cell := by
  constructor
  · intro h
    rcases h with ⟨htrace, hendpoint, hleft, hright⟩
    exact
      ⟨htrace, hendpoint,
        (sameCarrierTensorAtomAtomic_iff_atomAtomic C cell.leftAtom).mp hleft,
        (sameCarrierTensorAtomAtomic_iff_atomAtomic C cell.rightAtom).mp hright⟩
  · intro h
    rcases h with ⟨htrace, hendpoint, hleft, hright⟩
    exact
      ⟨htrace, hendpoint,
        (sameCarrierTensorAtomAtomic_iff_atomAtomic C cell.leftAtom).mpr hleft,
        (sameCarrierTensorAtomAtomic_iff_atomAtomic C cell.rightAtom).mpr hright⟩

/-- Under faithful tensor coding, tensor-readout full zero is exactly tensor
atomic balance on the same carrier. -/
theorem sameCarrierFullZero_iff_tensorAtomicZero
    (C : SameCarrierWeightTensorCoding)
    {n : ℕ} (cell : SU7SameCarrierAtomicCell n) :
    SameCarrierFullZero
        (sameCarrierObjectOfCellWithTensorAtomicReadout C cell) ↔
      SameCarrierTensorAtomicZero C cell := by
  have hobject :
      sameCarrierObjectOfCellWithTensorAtomicReadout C cell =
        sameCarrierObjectOfCellWithEndpointAtomicReadout cell := by
    unfold sameCarrierObjectOfCellWithTensorAtomicReadout
      sameCarrierObjectOfCellWithEndpointAtomicReadout
    congr
    funext a
    exact sameCarrierTensorAtomicReadout_eq_endpointAtomicReadout C a
  rw [hobject]
  exact
    (sameCarrierFullZero_iff_concreteAtomicZero cell).trans
      (sameCarrierTensorAtomicZero_iff_concreteAtomicZero C cell).symm

/-- The tensor-readout full-zero fiber is exactly the tensor-atomic zero fiber. -/
theorem sameCarrierTensorAtomicFullZero_iff_existsTensorAtomicZero
    (C : SameCarrierWeightTensorCoding)
    {n : ℕ} :
    (∃ cell : SU7SameCarrierAtomicCell n,
        SameCarrierFullZero
          (sameCarrierObjectOfCellWithTensorAtomicReadout C cell)) ↔
      ∃ cell : SU7SameCarrierAtomicCell n,
        SameCarrierTensorAtomicZero C cell := by
  constructor
  · rintro ⟨cell, hzero⟩
    exact ⟨cell,
      (sameCarrierFullZero_iff_tensorAtomicZero C cell).mp hzero⟩
  · rintro ⟨cell, hzero⟩
    exact ⟨cell,
      (sameCarrierFullZero_iff_tensorAtomicZero C cell).mpr hzero⟩


end StandardModelConstraint
end SaturationMonoid
