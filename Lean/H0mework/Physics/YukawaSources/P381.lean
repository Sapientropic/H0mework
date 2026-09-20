import H0mework.Physics.YukawaSources.P380

/-!
# Proposition 381: running-sigma corridor closes the nonabsorbing Yukawa bound

P379 erased the sampled Yukawa clocks down to one condition:
selected Yukawa sigmas must be nonabsorbing (`sigma < 1`).

P380 showed one local way to get that condition: a perturbative gauge bound
`g(scale)^2 < fourPi` at each selected Yukawa scale.

This file records the next more unified producer shape.  P274/P276 already pin
the weak endpoint to `sigma(M_Z)=81/500`, which is strictly below `1`.  Hence a
single running-sigma corridor condition

`sigma(yukawa y) <= sigma(weak)`

for every selected Yukawa scale is enough to supply all nonabsorbing Yukawa
rates, and therefore enough for the current unified-formula spine.

Boundary: this does not solve the RG equations or prove the physical corridor.
It turns the remaining obligation into an explicit RG/corridor producer:
construct the zero-free certificate and show selected Yukawa scales lie no
higher than the weak endpoint.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Weak-endpoint running-sigma corridor -/

/-- THEOREM 1: the pinned weak endpoint `81/500` is nonabsorbing. -/
theorem sigmaWeakNominal_lt_one_real :
    sigmaWeakNominal ℝ < 1 := by
  norm_num [sigmaWeakNominal]

/-- A zero-free certificate whose selected Yukawa sigmas lie inside the
GUT-to-weak running corridor, bounded above by the weak endpoint.

This is deliberately stated on `sigma`, not on clock fields.  After P379, the
sampled clocks are already known to be canonical consequences of `sigma < 1`. -/
def SelectedYukawaSigmaBoundedByWeak
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) :
    Prop :=
  ∀ y : YukawaParameter,
    Z.running.sigma (StandardModelScaleCode.yukawa y) ≤
      Z.running.sigma StandardModelScaleCode.weak

/-- A zero-free certificate equipped with one running-sigma corridor bound.
This is a producer-side normal form between P380's local perturbative bounds
and a future full RG/threshold calculation. -/
def ExistsZeroFreeRunningSigmaWeakCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    SelectedYukawaSigmaBoundedByWeak Z

/-- THEOREM 2: the weak-endpoint corridor implies the P379 nonabsorbing
selected Yukawa sigma condition. -/
theorem yukawaSigmaNonabsorbing_of_selectedYukawaSigmaBoundedByWeak
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (hZ : SelectedYukawaSigmaBoundedByWeak Z) :
    YukawaSigmaNonabsorbing Z := by
  intro y
  exact lt_of_le_of_lt (hZ y) <| by
    rw [ZeroContinuousFreeStandardModelCertificate.sigma_weak_code_eq_nominal Z]
    exact sigmaWeakNominal_lt_one_real

/-- THEOREM 3: a zero-free running corridor supplies the P379
zero-free/nonabsorbing producer. -/
theorem existsZeroFreeNonabsorbing_of_runningSigmaWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaWeakCorridor Index A CKMCarrier ->
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  rintro ⟨Z, hZ⟩
  exact ⟨Z, yukawaSigmaNonabsorbing_of_selectedYukawaSigmaBoundedByWeak Z hZ⟩

/-- THEOREM 4: a zero-free certificate plus the weak-endpoint running corridor
is sufficient for the current Standard-Model unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_runningSigmaWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaWeakCorridor Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma.mpr
      (existsZeroFreeNonabsorbing_of_runningSigmaWeakCorridor h)

/-- THEOREM 5: equivalently, the primitive producer atoms are available from
the zero-free certificate plus one running-sigma corridor bound. -/
theorem primitiveProducerAtoms_nonempty_of_runningSigmaWeakCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRunningSigmaWeakCorridor Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_iff_existsZeroFreeNonabsorbingYukawaSigma.mpr
      (existsZeroFreeNonabsorbing_of_runningSigmaWeakCorridor h)

end StandardModelConstraint
end SaturationMonoid
