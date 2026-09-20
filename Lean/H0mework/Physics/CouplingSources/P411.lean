import H0mework.Physics.AlphaSources.P410

/-!
# Proposition 411: the single-source receipt in running-sigma coordinates

P410 proves that the current single-source holy-grail receipt exists iff the
direct P401 physical alpha weak-bound exists.  P398/P401 already prove that,
under physical `fourPi = 4*pi`, the same obligation is exactly the compact
running-sigma corridor:

`sigma(yukawa y) <= sigma(weak)`.

This file composes those bridges.  The current front door can now be cited in
the native coordinate of the unified relaxation spine: a zero-free certificate,
physical four-pi normalization, and the selected-Yukawa running-sigma weak
corridor.

Boundary: this is still a normal-form theorem.  It does not derive the
zero-free seed, the RG/threshold inequalities, or the representation-breaking
physics that would produce the corridor.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Running-sigma front-door normal form -/

/-- THEOREM 1: the compact physical four-pi running-sigma corridor is exactly
the direct P401 alpha weak-bound surface. -/
theorem physicalFourPiSigmaCorridor_iff_alphaWeakBound
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier ↔
      ExistsZeroFreePhysicalSelectedYukawaAlphaWeakBound
        Index A CKMCarrier :=
  existsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness_iff_physicalGaugeCorridor.trans
    existsZeroFreePhysicalFourPiGaugeWeakCorridorWitness_iff_alphaWeakBound

/-- THEOREM 2: exact receipt-level normal form in the native running-sigma
coordinate.  The P407 single-source holy-grail receipt exists iff the compact
physical four-pi selected-sigma weak corridor exists. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalFourPiSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier := by
  exact
    singleSourcePhysicalHolyGrailReceipt_nonempty_iff_alphaWeakBound.trans
      (Iff.symm physicalFourPiSigmaCorridor_iff_alphaWeakBound)

/-- THEOREM 3: compact single-source holy-grail receipt directly from the
physical four-pi running-sigma corridor. -/
theorem physicalFourPiSigmaCorridor_singleSource_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalFourPiRunningSigmaIndependentCoordinateWitness
        Index A CKMCarrier ->
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
    alphaWeakBound_singleSource_holy_grail_receipt
      ((physicalFourPiSigmaCorridor_iff_alphaWeakBound).mp h)

end StandardModelConstraint
end SaturationMonoid
