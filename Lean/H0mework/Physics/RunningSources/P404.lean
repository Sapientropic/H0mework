import H0mework.Physics.SourceContracts.P403

/-!
# Proposition 404: physical alpha-RG monotonicity produces the weak bound

P401/P402 identify the current Standard-Model grand-unification entrypoint as
the physical alpha weak-bound:

`fourPi = 4*pi` and `alpha_yukawa <= 81/500`.

This file lowers that obligation to the next producer surface a real
RG/threshold calculation should supply: selected Yukawa scales lie below the
weak endpoint in a physical scale relation, and the physical gauge alpha
`g^2/(4*pi)` is monotone along that relation.

Boundary: this still does not derive the beta functions, threshold matching, or
representation content.  It proves the exact Lean bridge from such a physical
alpha-monotonicity producer into the current grand-unification receipt chain.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Physical alpha-RG monotonicity producer -/

/-- A physical RG/threshold producer in alpha coordinates.

The relation `physicalScaleLe` is deliberately not required to be total.  A
future beta-function/threshold proof may justify a partial order or preorder.
The important point is that the monotone quantity is the physical alpha
`g^2/(4*pi)`, not an arbitrary coordinate wrapper; the relation itself is also
forbidden from being definitionally the target alpha order. -/
structure PhysicalAlphaRGMonotonicityProducer
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier) where
  physicalScaleLe : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  scale_relation_not_alpha_order :
    physicalScaleLe ≠
      fun a b : StandardModelScaleCode =>
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
          alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b)
  fourPi_eq_realFourPi : Z.running.fourPi = realFourPi
  selected_yukawa_le_weak :
    ∀ y : YukawaParameter, physicalScaleLe (StandardModelScaleCode.yukawa y)
      StandardModelScaleCode.weak
  alpha_monotone :
    ∀ {a b : StandardModelScaleCode}, physicalScaleLe a b ->
      alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b)

namespace PhysicalAlphaRGMonotonicityProducer

variable {Index A CKMCarrier : Type*} [AddCommGroup A]
variable {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}

/-- THEOREM 1: the physical scale relation is not just the alpha-order target
itself.  This keeps the P404 producer from collapsing back to the P391-style
identity-coordinate trick. -/
theorem scale_relation_not_alpha_order_theorem
    (P : PhysicalAlphaRGMonotonicityProducer Z) :
    P.physicalScaleLe ≠
      fun a b : StandardModelScaleCode =>
        alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling a) ≤
          alphaFromGaugeCoupling realFourPi (Z.running.gaugeCoupling b) :=
  P.scale_relation_not_alpha_order

/-- THEOREM 2: under physical four-pi normalization, the weak endpoint alpha is
exactly the pinned weak sigma value `81/500`. -/
theorem weak_alpha_eq_sigmaWeakNominal_of_fourPi_eq
    (hfour : Z.running.fourPi = realFourPi) :
    alphaFromGaugeCoupling realFourPi
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) =
      sigmaWeakNominal ℝ := by
  calc
    alphaFromGaugeCoupling realFourPi
        (Z.running.gaugeCoupling StandardModelScaleCode.weak) =
        alphaFromGaugeCoupling Z.running.fourPi
          (Z.running.gaugeCoupling StandardModelScaleCode.weak) := by
          rw [hfour]
    _ = Z.running.sigma StandardModelScaleCode.weak := by
          exact (Z.running.sigma_eq_alpha StandardModelScaleCode.weak).symm
    _ = sigmaWeakNominal ℝ :=
          ZeroContinuousFreeStandardModelCertificate.sigma_weak_code_eq_nominal Z

/-- THEOREM 3: a physical alpha-RG monotonicity producer supplies the direct
P401 alpha weak-bound. -/
theorem toPhysicalSelectedYukawaAlphaWeakBound
    (P : PhysicalAlphaRGMonotonicityProducer Z) :
    PhysicalSelectedYukawaAlphaWeakBound Z := by
  refine ⟨P.fourPi_eq_realFourPi, ?_⟩
  intro y
  have hα :
      alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
        alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling StandardModelScaleCode.weak) :=
    P.alpha_monotone (P.selected_yukawa_le_weak y)
  simpa [weak_alpha_eq_sigmaWeakNominal_of_fourPi_eq
      (Z := Z) P.fourPi_eq_realFourPi] using hα

/-- Conversion: the same physical alpha producer also forgets to P383's squared
gauge-coupling monotonicity producer. -/
def toSelectedYukawaRGMonotonicityCertificate
    (P : PhysicalAlphaRGMonotonicityProducer Z) :
    SelectedYukawaRGMonotonicityCertificate Z := by
  refine
    { scaleLe := P.physicalScaleLe
      fourPi_pos := ?_
      selected_yukawa_le_weak := P.selected_yukawa_le_weak
      gaugeCouplingSq_monotone := ?_ }
  · rw [P.fourPi_eq_realFourPi]
    exact realFourPi_pos
  · intro a b hab
    have hα := P.alpha_monotone hab
    simpa [alphaFromGaugeCoupling] using
      (div_le_div_iff_of_pos_right realFourPi_pos).mp hα

end PhysicalAlphaRGMonotonicityProducer

/-! ## Existence-level bridges -/

/-- A zero-free certificate equipped with the physical alpha-RG monotonicity
producer. -/
def ExistsZeroFreePhysicalAlphaRGMonotonicityProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    Nonempty (PhysicalAlphaRGMonotonicityProducer Z)

/-- THEOREM 4: physical alpha-RG monotonicity constructs the P401/P402
alpha weak-bound producer. -/
theorem existsZeroFreePhysicalSelectedYukawaAlphaWeakBound_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound Index A CKMCarrier := by
  rintro ⟨Z, ⟨P⟩⟩
  exact ⟨Z, P.toPhysicalSelectedYukawaAlphaWeakBound⟩

/-- THEOREM 5: physical alpha-RG monotonicity also constructs the older P383
RG-monotonicity corridor. -/
theorem existsZeroFreeRGMonotonicityCorridor_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier := by
  rintro ⟨Z, ⟨P⟩⟩
  exact ⟨Z, ⟨P.toSelectedYukawaRGMonotonicityCertificate⟩⟩

/-- THEOREM 6: physical alpha-RG monotonicity is sufficient for the current
grand-unification receipt. -/
theorem rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) := by
  intro h
  exact
    rgMonotonicityGrandUnificationReceipt_nonempty_of_alphaWeakBound
      (existsZeroFreePhysicalSelectedYukawaAlphaWeakBound_of_physicalAlphaRGMonotonicity h)

/-- THEOREM 7: compact grand-unification receipt from the physical
alpha-monotonicity producer surface. -/
theorem physicalAlphaRGMonotonicity_grandUnification_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      Nonempty (RGMonotonicityGrandUnificationReceipt Index A CKMCarrier) ∧
      Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ∧
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) ∧
      ExistsZeroFreePerturbativeSelectedYukawaGauge Index A CKMCarrier ∧
      ExistsZeroFreeNonabsorbingYukawaSigma Index A CKMCarrier := by
  intro h
  exact
    alphaWeakBound_grandUnification_receipt
      (existsZeroFreePhysicalSelectedYukawaAlphaWeakBound_of_physicalAlphaRGMonotonicity h)

end StandardModelConstraint
end SaturationMonoid
