import H0mework.Physics.YukawaSources.P381

/-!
# Proposition 382: gauge-coupling corridor induces the running-sigma corridor

P381 reduced the remaining selected Yukawa nonabsorbing obligation to one
running-sigma corridor:

`sigma(yukawa y) <= sigma(weak)`.

This file moves that corridor one layer closer to the Standard-Model-facing
gauge data.  P274 reads every running sigma as the same gauge-alpha expression

`sigma(scale) = gaugeCoupling(scale)^2 / fourPi`.

Therefore, when `fourPi > 0`, a single gauge-coupling corridor

`g(yukawa y)^2 <= g(weak)^2`

implies P381's sigma corridor, and hence the current unified-formula spine.

Boundary: this still does not prove the RG monotonicity/corridor itself.  It
states the exact certificate a physical beta-function / threshold producer
must supply: selected Yukawa gauge couplings are bounded by the weak endpoint.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Gauge-coupling weak corridor -/

/-- The selected Yukawa gauge couplings sit below the weak-endpoint gauge
coupling, measured after squaring, with the same positive `fourPi` denominator.

This is the gauge-data version of P381's running-sigma corridor. -/
def SelectedYukawaGaugeCouplingsBoundedByWeak
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    Prop :=
  0 < Z.running.fourPi ∧
    ∀ y : YukawaParameter,
      (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^ (2 : Nat)

/-- A zero-free certificate equipped with a weak-endpoint gauge-coupling
corridor.  This is the current closest Lean-side normal form to a future
RG/threshold producer. -/
def ExistsZeroFreeGaugeWeakCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    SelectedYukawaGaugeCouplingsBoundedByWeak Z

/-- THEOREM 1: the gauge-coupling weak corridor implies P381's running-sigma
weak corridor. -/
theorem selectedYukawaSigmaBoundedByWeak_of_selectedYukawaGaugeCouplingsBoundedByWeak
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (hZ : SelectedYukawaGaugeCouplingsBoundedByWeak Z) :
    SelectedYukawaSigmaBoundedByWeak Z := by
  intro y
  rcases hZ with ⟨hfour, hbound⟩
  calc
    Z.running.sigma (StandardModelScaleCode.yukawa y)
        =
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ^
            (2 : Nat) / Z.running.fourPi := by
          rw [Z.running.sigma_eq_alpha (StandardModelScaleCode.yukawa y)]
          rfl
    _ ≤
          (Z.running.gaugeCoupling StandardModelScaleCode.weak) ^
            (2 : Nat) / Z.running.fourPi := by
          exact div_le_div_of_nonneg_right (hbound y) (le_of_lt hfour)
    _ =
        Z.running.sigma StandardModelScaleCode.weak := by
          rw [Z.running.sigma_eq_alpha StandardModelScaleCode.weak]
          rfl

/-- THEOREM 2: a zero-free gauge-coupling weak corridor supplies P381's
zero-free running-sigma corridor. -/
theorem existsZeroFreeRunningSigmaWeakCorridor_of_gaugeWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeGaugeWeakCorridor Index A CKMCarrier ->
      ExistsZeroFreeRunningSigmaWeakCorridor Index A CKMCarrier := by
  rintro ⟨Z, hZ⟩
  exact
    ⟨Z,
      selectedYukawaSigmaBoundedByWeak_of_selectedYukawaGaugeCouplingsBoundedByWeak
        Z hZ⟩

/-- THEOREM 3: a zero-free gauge-coupling weak corridor is sufficient for the
current Standard-Model unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_gaugeWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeGaugeWeakCorridor Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_of_runningSigmaWeakCorridor
      (existsZeroFreeRunningSigmaWeakCorridor_of_gaugeWeakCorridor h)

/-- THEOREM 4: equivalently, the primitive producer atoms are available from
the zero-free certificate plus a weak-endpoint gauge-coupling corridor. -/
theorem primitiveProducerAtoms_nonempty_of_gaugeWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeGaugeWeakCorridor Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_of_runningSigmaWeakCorridor
      (existsZeroFreeRunningSigmaWeakCorridor_of_gaugeWeakCorridor h)

end StandardModelConstraint
end SaturationMonoid
