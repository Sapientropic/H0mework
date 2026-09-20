import H0mework.Physics.JointSources.P407

/-!
# Proposition 408: P404 already supplies the single-source holy-grail producer

P407 introduced the strongest current bookkeeping normal form: one primitive
atom object supplies the opened zero-free certificate, the unified formula
spine, and the atom payload, while the physical alpha-RG producer is indexed by
that same zero-free object.

This file proves that P407 does not add a stronger physical hypothesis over
P404.  A P404 physical alpha-RG monotonicity producer already implies the
selected Yukawa sigmas are nonabsorbing (`sigma < 1`), so P379's canonical
sampled-clock construction opens the same zero-free certificate into primitive
atoms.  Those atoms then supply the P407 single-source producer.

Boundary: the beta functions / thresholds / representation content are still
the remaining physical producer.  The contribution here is that the current
front door is the single-source normal form, not an extra assumption layered on
top of P404.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## P404 gives canonical nonabsorbing Yukawa sigmas -/

/-- THEOREM 1: physical alpha-RG monotonicity forces every selected Yukawa
running sigma below one. -/
theorem yukawaSigmaNonabsorbing_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    {Z : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier}
    (P : PhysicalAlphaRGMonotonicityProducer Z) :
    YukawaSigmaNonabsorbing Z := by
  intro y
  have hbound :
      alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
        sigmaWeakNominal ℝ :=
    P.toPhysicalSelectedYukawaAlphaWeakBound.2 y
  have hsigma :
      Z.running.sigma (StandardModelScaleCode.yukawa y) =
        alphaFromGaugeCoupling realFourPi
          (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) := by
    calc
      Z.running.sigma (StandardModelScaleCode.yukawa y) =
          alphaFromGaugeCoupling Z.running.fourPi
            (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) := by
            exact Z.running.sigma_eq_alpha (StandardModelScaleCode.yukawa y)
      _ = alphaFromGaugeCoupling realFourPi
            (Z.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) := by
            rw [P.fourPi_eq_realFourPi]
  exact lt_of_le_of_lt (by simpa [hsigma] using hbound)
    sigmaWeakNominal_lt_one_real

/-! ## Primitive atoms opened from the same zero-free object -/

/-- THEOREM 2: opening a minimal producer kernel into primitive atoms and then
forgetting back to the zero-free certificate is definitionally the original
zero-free object. -/
theorem primitiveAtoms_ofMinimalProducerKernel_toZeroFree
    {Index A CKMCarrier : Type*} [AddCommGroup A]
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    (GrandUnificationPrimitiveProducerAtoms.ofMinimalProducerKernel M).toZeroFree =
      M.zeroFree := by
  rfl

/-- THEOREM 3: physical alpha-RG monotonicity constructs P407's single-source
producer.  Thus P407 is a stronger normal form for the P404 front door, not a
new physical assumption. -/
theorem singleSourcePhysicalProducer_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      ExistsSingleSourcePhysicalGrandUnificationProducer
        Index A CKMCarrier := by
  rintro ⟨Z, ⟨P⟩⟩
  have hnon : YukawaSigmaNonabsorbing Z :=
    yukawaSigmaNonabsorbing_of_physicalAlphaRGMonotonicity P
  rcases existsSampledYukawaClocks_of_nonabsorbing Z hnon with
    ⟨yukawaLambda, yukawaStep, hsampled⟩
  let M : MinimalGrandUnificationProducerKernel Index A CKMCarrier :=
    { zeroFree := Z
      yukawaLambda := yukawaLambda
      yukawaStep := yukawaStep
      selected_yukawa_sigma_sampled := hsampled }
  let atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier :=
    GrandUnificationPrimitiveProducerAtoms.ofMinimalProducerKernel M
  have hzero : atoms.toZeroFree = Z := by
    dsimp [atoms, M]
    exact primitiveAtoms_ofMinimalProducerKernel_toZeroFree M
  refine ⟨atoms, ?_⟩
  rw [hzero]
  exact ⟨P⟩

/-- THEOREM 4: exact front-door normal form.  The physical alpha-RG producer
surface from P404 is equivalent to the P407 single-source producer surface. -/
theorem singleSourcePhysicalProducer_iff_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsSingleSourcePhysicalGrandUnificationProducer Index A CKMCarrier ↔
      ExistsZeroFreePhysicalAlphaRGMonotonicityProducer
        Index A CKMCarrier := by
  constructor
  · exact existsPhysicalAlphaRGMonotonicity_of_singleSource
  · exact singleSourcePhysicalProducer_of_physicalAlphaRGMonotonicity

/-- THEOREM 5: exact receipt-level normal form.  The fully canonical
single-source holy-grail receipt exists iff the P404 physical alpha-RG producer
surface exists. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      ExistsZeroFreePhysicalAlphaRGMonotonicityProducer
        Index A CKMCarrier :=
  singleSourcePhysicalHolyGrailReceipt_nonempty_iff_producer.trans
    singleSourcePhysicalProducer_iff_physicalAlphaRGMonotonicity

/-- THEOREM 6: the P404 front door now yields the P407 single-source holy-grail
receipt directly. -/
theorem physicalAlphaRGMonotonicity_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      ∃ C : SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier,
        C.receipt.zeroFree = C.atoms.toZeroFree ∧
        HEq C.receipt.rg
          C.physicalRG.toSelectedYukawaRGMonotonicityCertificate ∧
        C.receipt.spine = C.atoms.toUnifiedFormulaSpine ∧
        C.receipt.primitiveAtoms = C.atoms ∧
        C.receipt.spine.target.sampled.zeroFree = C.atoms.toZeroFree ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        C.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) * C.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ := by
  intro h
  exact
    singleSourcePhysicalGrandUnification_holy_grail_receipt
      (singleSourcePhysicalProducer_of_physicalAlphaRGMonotonicity h)

end StandardModelConstraint
end SaturationMonoid
