/-
  Proposition 380: perturbative selected Yukawa gauge couplings imply the
  nonabsorbing sigma condition.

  P379 removed the sampled Yukawa clock fields: sampled-rate existence is
  equivalent to the selected Yukawa rates satisfying `sigma < 1`.

  This file pushes that remaining condition one layer closer to the physical
  Standard-Model producer.  P274 already says `sigma(scale)` is the gauge alpha
  `g(scale)^2 / fourPi`.  Therefore a perturbative bound

      g(scale)^2 < fourPi

  on the selected Yukawa scales is sufficient to put those sigmas in the
  nonabsorbing region.  The point is not to solve the RG equations here.  The
  point is to make the next producer obligation exact: construct the zero-free
  certificate plus this selected-scale perturbative gauge bound, and P379/P380
  canonically supply the unified-formula spine.
-/

import H0mework.Physics.YukawaSources.P379

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Selected Yukawa perturbative gauge bound -/

/-- The selected Yukawa scale gauge couplings are perturbative enough to keep
the associated running sigma rates nonabsorbing.

Because P274 defines `sigma(scale) = gaugeCoupling(scale)^2 / fourPi`, the
numerical bound needed here is exactly `g^2 < fourPi` with positive `fourPi`. -/
def SelectedYukawaGaugeCouplingsSubunit
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    Prop :=
  0 < Z.running.fourPi ∧
    ∀ y : YukawaParameter,
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) <
        Z.running.fourPi

/-- A zero-free certificate equipped with selected-scale perturbative gauge
couplings.  This is the producer-side form of the remaining P379 obligation. -/
def ExistsZeroFreePerturbativeSelectedYukawaGauge
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    SelectedYukawaGaugeCouplingsSubunit Z

/-- THEOREM 1: the selected-scale perturbative gauge bound implies the P379
nonabsorbing selected Yukawa sigma condition. -/
theorem yukawaSigmaNonabsorbing_of_selectedYukawaGaugeCouplingsSubunit
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (hZ : SelectedYukawaGaugeCouplingsSubunit Z) :
    YukawaSigmaNonabsorbing Z := by
  intro y
  rcases hZ with ⟨hfour, hsub⟩
  calc
    Z.running.sigma (StandardModelScaleCode.yukawa y)
        = alphaFromGaugeCoupling Z.running.fourPi
            (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) := by
          exact Z.running.sigma_eq_alpha (StandardModelScaleCode.yukawa y)
    _ =
        (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
          Z.running.fourPi := by
          rfl
    _ < 1 := by
      have hdiv :
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) /
              Z.running.fourPi <
            Z.running.fourPi / Z.running.fourPi :=
        div_lt_div_of_pos_right (hsub y) hfour
      have hself : Z.running.fourPi / Z.running.fourPi = (1 : ℝ) :=
        div_self (ne_of_gt hfour)
      simpa [hself] using hdiv

/-- THEOREM 2: a perturbative selected-Yukawa gauge producer supplies the
P379 zero-free/nonabsorbing producer. -/
theorem existsZeroFreeNonabsorbing_of_perturbativeSelectedYukawaGauge
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier ->
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  rintro ⟨Z, hZ⟩
  exact ⟨Z, yukawaSigmaNonabsorbing_of_selectedYukawaGaugeCouplingsSubunit Z hZ⟩

/-- THEOREM 3: perturbative selected Yukawa gauge data are sufficient for the
current Standard-Model unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_perturbativeSelectedYukawaGauge
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma.mpr
      (existsZeroFreeNonabsorbing_of_perturbativeSelectedYukawaGauge h)

/-- THEOREM 4: equivalently, the P378 primitive producer atoms are available
from the zero-free certificate plus selected-scale perturbative gauge bound. -/
theorem primitiveProducerAtoms_nonempty_of_perturbativeSelectedYukawaGauge
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma.mpr
      (existsZeroFreeNonabsorbing_of_perturbativeSelectedYukawaGauge h)

end StandardModelConstraint
end SaturationMonoid
