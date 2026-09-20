import H0mework.Physics.CouplingSources.P382

/-!
# Proposition 383: RG monotonicity produces the gauge weak corridor

P382 reduced the selected Yukawa nonabsorbing obligation to a gauge-coupling
weak corridor:

`g(yukawa)^2 <= g(weak)^2`.

This file states the next producer in the form a real RG/threshold proof should
eventually discharge.  If there is an RG scale relation whose selected Yukawa
points lie below the weak endpoint, and the squared gauge coupling is monotone
along that relation, then P382's corridor follows, hence the unified-formula
spine follows.

Boundary: the RG scale relation and monotonicity theorem are still supplied by
the certificate.  The contribution here is the exact Lean bridge from such an
RG monotonicity producer to the existing grand-unification spine.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## RG monotonicity producer shape -/

/-- A physical RG/threshold producer should provide this shape: a scale
relation, selected Yukawa scales below the weak endpoint in that relation, and
monotonicity of squared gauge coupling along it.

No total order is assumed.  The relation can be the exact partial order or
preorder that a future threshold analysis justifies. -/
structure SelectedYukawaRGMonotonicityCertificate
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  scaleLe : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  fourPi_pos : 0 < Z.running.fourPi
  selected_yukawa_le_weak :
    ∀ y : YukawaParameter, scaleLe (StandardModelScaleCode.yukawa y)
      StandardModelScaleCode.weak
  gaugeCouplingSq_monotone :
    ∀ {a b : StandardModelScaleCode}, scaleLe a b ->
      (Z.running.gaugeCoupling a) ^ (2 : Nat) ≤
        (Z.running.gaugeCoupling b) ^ (2 : Nat)

/-- A zero-free certificate equipped with the RG monotonicity producer shape. -/
def ExistsZeroFreeRGMonotonicityCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (SelectedYukawaRGMonotonicityCertificate Z)

/-- THEOREM 1: an RG monotonicity certificate implies P382's gauge weak
corridor. -/
theorem selectedYukawaGaugeCouplingsBoundedByWeak_of_rgMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier)
    (C : SelectedYukawaRGMonotonicityCertificate Z) :
    SelectedYukawaGaugeCouplingsBoundedByWeak Z := by
  refine ⟨C.fourPi_pos, ?_⟩
  intro y
  exact C.gaugeCouplingSq_monotone (C.selected_yukawa_le_weak y)

/-- THEOREM 2: an RG monotonicity producer supplies P382's zero-free
gauge-coupling weak corridor. -/
theorem existsZeroFreeGaugeWeakCorridor_of_rgMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      ExistsZeroFreeGaugeWeakCorridor Index A CKMCarrier := by
  rintro ⟨Z, ⟨C⟩⟩
  exact ⟨Z, selectedYukawaGaugeCouplingsBoundedByWeak_of_rgMonotonicity Z C⟩

/-- THEOREM 3: a zero-free RG monotonicity producer is sufficient for the
current Standard-Model unified-formula spine. -/
theorem unifiedFormulaSpine_nonempty_of_rgMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) := by
  intro h
  exact
    unifiedFormulaSpine_nonempty_of_gaugeWeakCorridor
      (existsZeroFreeGaugeWeakCorridor_of_rgMonotonicity h)

/-- THEOREM 4: equivalently, primitive producer atoms are available from a
zero-free certificate plus an RG monotonicity producer. -/
theorem primitiveProducerAtoms_nonempty_of_rgMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier ->
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  intro h
  exact
    primitiveProducerAtoms_nonempty_of_gaugeWeakCorridor
      (existsZeroFreeGaugeWeakCorridor_of_rgMonotonicity h)

end StandardModelConstraint
end SaturationMonoid
