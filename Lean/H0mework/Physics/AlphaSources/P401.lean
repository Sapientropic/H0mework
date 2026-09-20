import H0mework.Physics.CouplingSources.P400

/-!
# Proposition 401: physical alpha weak-bound normal form

P398/P399/P400 leave the live physical producer as a gauge-side weak corridor:

* `fourPi = 4*pi`;
* every selected Yukawa squared gauge coupling is bounded by the weak squared
  gauge coupling.

P399 already proves that this corridor implies the more physical alpha bound

`alpha_yukawa = g(yukawa)^2 / (4*pi) <= 81/500`.

This file proves the converse, so the remaining producer obligation can be
stated directly in the physical alpha coordinate without loss.  The weak
endpoint is reconstructed from the pinned running-sigma law and
`fourPi = 4*pi`, not assumed as a fresh field.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Physical alpha-coordinate weak bound -/

/-- Physical alpha-coordinate normal form for the selected Yukawa corridor. -/
def PhysicalSelectedYukawaAlphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    Prop :=
  Z.running.fourPi = realFourPi ∧
    ∀ y : YukawaParameter,
      alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
        sigmaWeakNominal ℝ

namespace PhysicalSelectedYukawaAlphaWeakBound

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: once `fourPi = 4*pi`, the pinned weak running-sigma endpoint
forces the weak squared gauge coupling to be `(4*pi) * (81/500)`.

This is the P399 weak-endpoint calculation with only the physical four-pi
normalization as input, so the reverse direction below does not depend on an
already-built gauge corridor witness. -/
theorem weak_gaugeCouplingSq_eq_realFourPi_mul_sigmaWeakNominal_of_fourPi_eq
    (hfour : Z.running.fourPi = realFourPi) :
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
            rw [hfour]
  have hmul :
      sigmaWeakNominal ℝ * realFourPi = x := by
    calc
      sigmaWeakNominal ℝ * realFourPi =
          (x / realFourPi) * realFourPi := by rw [hdiv]
      _ = x := div_mul_cancel₀ x (ne_of_gt realFourPi_pos)
  simpa [x, mul_comm] using hmul.symm

/-- THEOREM 2: a physical alpha weak-bound gives the selected squared-gauge
weak corridor. -/
theorem selected_yukawa_gauge_le_weak
    (H : PhysicalSelectedYukawaAlphaWeakBound Z) :
    ∀ y : YukawaParameter,
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) := by
  intro y
  rcases H with ⟨hfour, halpha⟩
  have hdiv :
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
          realFourPi ≤
        sigmaWeakNominal ℝ := by
    simpa [alphaFromGaugeCoupling] using halpha y
  have hcancel :
      (realFourPi * sigmaWeakNominal ℝ) / realFourPi =
        sigmaWeakNominal ℝ := by
    exact mul_div_cancel_left₀ (sigmaWeakNominal ℝ) (ne_of_gt realFourPi_pos)
  have hdiv' :
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
          realFourPi ≤
        (realFourPi * sigmaWeakNominal ℝ) / realFourPi := by
    simpa [hcancel] using hdiv
  have hsq_le_endpoint :
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
        realFourPi * sigmaWeakNominal ℝ :=
    (div_le_div_iff_of_pos_right realFourPi_pos).mp hdiv'
  have hweak :
      (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat) =
        realFourPi * sigmaWeakNominal ℝ :=
    weak_gaugeCouplingSq_eq_realFourPi_mul_sigmaWeakNominal_of_fourPi_eq
      (Z := Z) hfour
  simpa [hweak] using hsq_le_endpoint

/-- THEOREM 3: the physical alpha-coordinate weak bound constructs the
P398 physical gauge-side weak corridor. -/
theorem toPhysicalFourPiGaugeWeakCorridorWitness
    (H : PhysicalSelectedYukawaAlphaWeakBound Z) :
    PhysicalFourPiGaugeWeakCorridorWitness Z :=
  { fourPi_eq_realFourPi := H.1
    selected_yukawa_gauge_le_weak := H.selected_yukawa_gauge_le_weak }

end PhysicalSelectedYukawaAlphaWeakBound

namespace PhysicalFourPiGaugeWeakCorridorWitness

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 4: the P398 physical gauge-side weak corridor gives exactly the
physical alpha-coordinate weak bound. -/
theorem toPhysicalSelectedYukawaAlphaWeakBound
    (W : PhysicalFourPiGaugeWeakCorridorWitness Z) :
    PhysicalSelectedYukawaAlphaWeakBound Z :=
  ⟨W.fourPi_eq_realFourPi,
    fun y => W.selected_yukawa_alpha_le_sigmaWeakNominal y⟩

end PhysicalFourPiGaugeWeakCorridorWitness

/-! ## Exact normal-form equivalence -/

/-- THEOREM 5: the physical gauge weak corridor is equivalent to the physical
alpha weak-bound normal form. -/
theorem physicalGaugeCorridor_iff_selectedYukawaAlphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier} :
    PhysicalFourPiGaugeWeakCorridorWitness Z ↔
      PhysicalSelectedYukawaAlphaWeakBound Z := by
  constructor
  · exact PhysicalFourPiGaugeWeakCorridorWitness.toPhysicalSelectedYukawaAlphaWeakBound
  · exact PhysicalSelectedYukawaAlphaWeakBound.toPhysicalFourPiGaugeWeakCorridorWitness

/-- Existence of the physical alpha-coordinate weak-bound producer. -/
def ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    PhysicalSelectedYukawaAlphaWeakBound Z

/-- THEOREM 6: at the producer-existence level, the physical gauge weak
corridor and physical alpha weak-bound are the same remaining obligation. -/
theorem existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiGaugeWeakCorridorWitness Index A CKMCarrier ↔
      ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier := by
  constructor
  · rintro ⟨Z, ⟨W⟩⟩
    exact ⟨Z, W.toPhysicalSelectedYukawaAlphaWeakBound⟩
  · rintro ⟨Z, H⟩
    exact ⟨Z, ⟨H.toPhysicalFourPiGaugeWeakCorridorWitness⟩⟩

/-- THEOREM 7: the physical path-table producer can now be read directly as
the physical alpha-coordinate weak-bound producer. -/
theorem existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ↔
      ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier :=
  existsZeroFreePhysicalFourPiRunningSigmaYukawaRGPathTableProducer_iff_physicalGaugeCorridor.trans
    existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound

end StandardModelConstraint
end SaturationMonoid
