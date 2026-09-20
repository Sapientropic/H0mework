import H0mework.Physics.CouplingSources.P399

/-!
# Proposition 400: physical weak endpoint implies selected perturbativity

P399 proves that the physical gauge corridor pins the weak endpoint to

`g(weak)^2 = (4*pi) * (81/500)`.

Since `81/500 < 1` and `4*pi > 0`, every selected Yukawa squared coupling
bounded by that endpoint is strictly below `4*pi`.  This closes the loop back
to P380's perturbative producer surface `g(yukawa)^2 < fourPi`, but now as a
consequence of the physical-four-pi weak corridor rather than as an independent
assumption.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace PhysicalFourPiGaugeWeakCorridorWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-! ## Physical corridor gives perturbative selected Yukawas -/

/-- THEOREM 1: a physical-four-pi gauge weak corridor implies P380's selected
Yukawa perturbativity condition `g(yukawa)^2 < fourPi`. -/
theorem toSelectedYukawaGaugeCouplingsSubunit
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    SelectedYukawaGaugeCouplingsSubunit Z := by
  refine ⟨?_, ?_⟩
  · rw [W.fourPi_eq_realFourPi]
    exact realFourPi_pos
  · intro y
    have hendpoint :
        realFourPi * sigmaWeakNominal ℝ < realFourPi := by
      calc
        realFourPi * sigmaWeakNominal ℝ < realFourPi * (1 : ℝ) :=
          mul_lt_mul_of_pos_left sigmaWeakNominal_lt_one_real realFourPi_pos
        _ = realFourPi := by ring
    calc
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat)
          ≤ realFourPi * sigmaWeakNominal ℝ :=
            W.selected_yukawa_gaugeCouplingSq_le_realFourPi_mul_sigmaWeakNominal y
      _ < realFourPi := hendpoint
      _ = Z.running.fourPi := W.fourPi_eq_realFourPi.symm

end PhysicalFourPiGaugeWeakCorridorWitness

/-! ## Existential producer consequences -/

/-- THEOREM 2: the physical gauge corridor supplies P380's perturbative
selected-Yukawa gauge producer. -/
theorem existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, W.toSelectedYukawaGaugeCouplingsSubunit⟩

/-- THEOREM 3: the physical gauge corridor therefore supplies the P379
zero-free/nonabsorbing selected-Yukawa sigma producer. -/
theorem existsZeroFreeNonabsorbing_of_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  exact
    existsZeroFreeNonabsorbing_of_perturbativeSelectedYukawaGauge ∘
      existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor

/-- THEOREM 4: physical gauge-corridor data are sufficient for the current
unified-formula spine by the perturbativity route. -/
theorem unifiedFormulaSpine_nonempty_of_physicalGaugeCorridor_via_perturbativity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  exact
    unifiedFormulaSpine_nonempty_of_perturbativeSelectedYukawaGauge ∘
      existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor

/-- THEOREM 5: physical gauge-corridor data are sufficient for the primitive
producer atoms by the perturbativity route. -/
theorem primitiveProducerAtoms_nonempty_of_physicalGaugeCorridor_via_perturbativity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  exact
    primitiveProducerAtoms_nonempty_of_perturbativeSelectedYukawaGauge ∘
      existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor

/-- THEOREM 6: the physical path-table normal form also supplies perturbative
selected-Yukawa gauge data. -/
theorem existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier := by
  exact
    existsZeroFreePerturbativeSelectedYukawaGauge_of_physicalGaugeCorridor ∘
      existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalGaugeCorridor.mp

end StandardModelConstraint
end SaturationMonoid
