import H0mework.Physics.SourceForms.P398

/-!
# Proposition 399: physical weak gauge-coupling numerical endpoint

P398 moves the remaining physical corridor from the running-sigma coordinate
back to the squared gauge-coupling coordinate.  This file extracts the numeric
weak endpoint forced by the already pinned data:

* P274 defines `sigma(scale) = g(scale)^2 / fourPi`;
* P276 pins `sigma(weak)=81/500`;
* P396/P398's physical corridor pins `fourPi = 4*pi`.

Together these prove

`g(weak)^2 = (4*pi) * (81/500)`.

Thus the selected-Yukawa corridor may be cited as a concrete upper bound
against the physical weak endpoint, not merely as an abstract comparison with
`g(weak)^2`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

namespace PhysicalFourPiGaugeWeakCorridorWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-! ## Weak endpoint as a physical number -/

/-- THEOREM 1: in a physical-four-pi gauge corridor, the weak-scale squared
gauge coupling is exactly `(4*pi) * (81/500)`. -/
theorem weak_gaugeCouplingSq_eq_realFourPi_mul_sigmaWeakNominal
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) =
      realFourPi * sigmaWeakNominal ℝ := by
  let x :=
    (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat)
  have hdiv :
      sigmaWeakNominal ℝ = x / realFourPi := by
    calc
      sigmaWeakNominal ℝ =
          Z.running.sigma StandardModelScaleCode.weak := by
            rw [ZeroContinuousFreeStandardModelCertificate.sigma_weak_code_eq_nominal Z]
      _ = x / Z.running.fourPi := by
            simp [x, alphaFromGaugeCoupling,
              Z.running.sigma_eq_alpha StandardModelScaleCode.weak]
      _ = x / realFourPi := by
            rw [W.fourPi_eq_realFourPi]
  have hmul :
      sigmaWeakNominal ℝ * realFourPi = x := by
    calc
      sigmaWeakNominal ℝ * realFourPi =
          (x / realFourPi) * realFourPi := by rw [hdiv]
      _ = x := div_mul_cancel₀ x (ne_of_gt realFourPi_pos)
  simpa [x, mul_comm] using hmul.symm

/-- THEOREM 2: every selected Yukawa squared gauge coupling is bounded by the
physical weak endpoint `(4*pi) * (81/500)`. -/
theorem selected_yukawa_gaugeCouplingSq_le_realFourPi_mul_sigmaWeakNominal
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) (y : YukawaParameter) :
    (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
      realFourPi * sigmaWeakNominal ℝ := by
  simpa [W.weak_gaugeCouplingSq_eq_realFourPi_mul_sigmaWeakNominal] using
    W.selected_yukawa_gauge_le_weak y

/-- THEOREM 3: the same upper bound, stated in alpha/sigma coordinates, is the
pinned weak sigma endpoint.  This is mostly a citation convenience for notes
that want the gauge-side and sigma-side readings next to each other. -/
theorem selected_yukawa_alpha_le_sigmaWeakNominal
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) (y : YukawaParameter) :
    alphaFromGaugeCoupling realFourPi
        (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
      sigmaWeakNominal ℝ := by
  have hle := W.selected_yukawa_gaugeCouplingSq_le_realFourPi_mul_sigmaWeakNominal y
  have hpos : 0 < realFourPi := realFourPi_pos
  have hdiv :
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
          realFourPi ≤
        (realFourPi * sigmaWeakNominal ℝ) / realFourPi :=
    (div_le_div_iff_of_pos_right hpos).mpr hle
  have hcancel :
      (realFourPi * sigmaWeakNominal ℝ) / realFourPi =
        sigmaWeakNominal ℝ := by
    exact mul_div_cancel_left₀ (sigmaWeakNominal ℝ) (ne_of_gt realFourPi_pos)
  simpa [alphaFromGaugeCoupling, hcancel] using hdiv

end PhysicalFourPiGaugeWeakCorridorWitness

/-! ## Existential producer consequences -/

/-- A named receipt for the numerical weak-endpoint consequence of the physical
gauge corridor. -/
structure PhysicalGaugeWeakNumericalEndpointReceipt
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  weak_gauge_sq_eq :
    (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) =
      realFourPi * sigmaWeakNominal ℝ
  selected_yukawa_gauge_sq_le :
    ∀ y : YukawaParameter,
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
        realFourPi * sigmaWeakNominal ℝ
  selected_yukawa_alpha_le :
    ∀ y : YukawaParameter,
      alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
        sigmaWeakNominal ℝ

namespace PhysicalFourPiGaugeWeakCorridorWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 4: a physical gauge corridor canonically carries the numerical weak
endpoint receipt. -/
theorem toPhysicalGaugeWeakNumericalEndpointReceipt
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    PhysicalGaugeWeakNumericalEndpointReceipt Z :=
  { weak_gauge_sq_eq :=
      W.weak_gaugeCouplingSq_eq_realFourPi_mul_sigmaWeakNominal
    selected_yukawa_gauge_sq_le :=
      W.selected_yukawa_gaugeCouplingSq_le_realFourPi_mul_sigmaWeakNominal
    selected_yukawa_alpha_le :=
      W.selected_yukawa_alpha_le_sigmaWeakNominal }

end PhysicalFourPiGaugeWeakCorridorWitness

/-- THEOREM 5: existence of the physical gauge-side corridor produces a
zero-free certificate equipped with the concrete weak-endpoint receipt. -/
theorem exists_physicalGaugeWeakNumericalEndpointReceipt_of_physicalGaugeCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ->
      ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
        Nonempty (PhysicalGaugeWeakNumericalEndpointReceipt Z) := by
  rintro ⟨Z, ⟨W⟩⟩
  exact ⟨Z, ⟨W.toPhysicalGaugeWeakNumericalEndpointReceipt⟩⟩

/-- THEOREM 6: P397/P398's physical path-table normal form also yields the
concrete weak-endpoint numerical receipt. -/
theorem exists_physicalGaugeWeakNumericalEndpointReceipt_of_physicalPathTable
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ->
      ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
        Nonempty (PhysicalGaugeWeakNumericalEndpointReceipt Z) := by
  exact
    exists_physicalGaugeWeakNumericalEndpointReceipt_of_physicalGaugeCorridor ∘
      existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalGaugeCorridor.mp

end StandardModelConstraint
end SaturationMonoid
