import H0mework.Physics.RunningSources.P404

/-!
# Proposition 405: physical grand-unification holy-grail normal form

P373/P384/P403/P404 leave the Standard-Model projection in a producer-relative
but now very narrow shape.  The remaining physical front door is:

* a zero-free Standard-Model certificate;
* a physical alpha-RG monotonicity producer for the selected Yukawa scales.

This file packages that front door as the current "holy-grail" normal form.
It proves that the physical producer surface is exactly sufficient to carry, in
one receipt:

* zero continuous free parameters on the accepted 19-slot surface;
* `theta_QCD = 0`;
* `alpha_em = 1/137`;
* `sin^2(theta_W)(GUT) = 3/8`;
* `alpha_GUT^{-1} = 133/3`;
* the direct strong-coupling closure `alpha_s(M_Z)=1179/10000`;
* exact running-sigma CKM phase closure;
* sampled continuous Yukawa residuals.

Boundary: this is not a beta-function, threshold, Higgs-representation, or CKM
depth derivation.  It is the strongest current Lean-normal form for the
grand-unification target: all remaining physics is localized in the explicit
physical alpha-RG producer plus the zero-free certificate.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Physical holy-grail receipt -/

/-- The current physical grand-unification receipt.

It keeps the remaining physical producer visible while carrying the already
proved P384 grand-unification receipt.  This prevents the central result from
being read as an unconditional Standard-Model derivation. -/
structure PhysicalGrandUnificationHolyGrailReceipt
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  zeroFree : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier
  physicalRG : PhysicalAlphaRGMonotonicityProducer zeroFree
  receipt : RGMonotonicityGrandUnificationReceipt Index A CKMCarrier

namespace PhysicalGrandUnificationHolyGrailReceipt

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the receipt exposes exactly the physical alpha-RG producer
surface from P404. -/
theorem toPhysicalAlphaRGMonotonicityProducer
    (H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier :=
  ⟨H.zeroFree, ⟨H.physicalRG⟩⟩

/-- THEOREM 2: the embedded P384 receipt still forgets to the older RG
monotonicity corridor. -/
theorem toExistsZeroFreeRGMonotonicityCorridor
    (H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) :
    ExistsZeroFreeRGMonotonicityCorridor Index A CKMCarrier :=
  H.receipt.toExistsZeroFreeRGMonotonicityCorridor

/-- THEOREM 3: the physical scale relation is not definitionally just the
target alpha order. -/
theorem scale_relation_not_alpha_order
    (H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) :
    H.physicalRG.physicalScaleLe ≠
      fun a b : StandardModelScaleCode =>
        alphaFromGaugeCoupling realFourPi
            (H.zeroFree.running.gaugeCoupling a) ≤
          alphaFromGaugeCoupling realFourPi
            (H.zeroFree.running.gaugeCoupling b) :=
  H.physicalRG.scale_relation_not_alpha_order_theorem

/-- THEOREM 4: the physical producer gives the selected-Yukawa alpha weak
bound, in direct physical alpha coordinates. -/
theorem selected_yukawa_alpha_le_weak
    (H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier)
    (y : YukawaParameter) :
    alphaFromGaugeCoupling realFourPi
        (H.zeroFree.running.gaugeCoupling (StandardModelScaleCode.yukawa y)) ≤
      sigmaWeakNominal ℝ :=
  H.physicalRG.toPhysicalSelectedYukawaAlphaWeakBound.2 y

/-- THEOREM 5: the central receipt in one statement.

The conjunction is intentionally explicit: it is the machine-checkable surface
of the current Standard-Model grand-unification target. -/
theorem holy_grail_receipt
    (H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) :
    NoContinuousFreeParameters
        H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
      (∀ p : ParameterVector ℝ,
        H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
          p StandardModelParameter.qcd_theta = 0) ∧
      alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      H.receipt.spine.target.strongResidualProducer.correctedOutput =
        alphaStrongDisplayed ℝ ∧
      (ckmCPDepthSum : ℝ) * H.receipt.spine.target.cpRunningSigma =
        cpRawPhaseClaim ℝ ∧
      cpDeltaCPClaim ℝ =
        cpTauProxy ℝ -
          (ckmCPDepthSum : ℝ) * H.receipt.spine.target.cpRunningSigma ∧
      (∀ p : ParameterVector ℝ,
        H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
          ∀ y : YukawaParameter,
            p (yukawaSlot y) =
              (H.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y) *
                AffineRelaxation.realDecayResidual
                  (H.receipt.spine.target.sampled.yukawaLambda y)
                  ((H.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                        H.receipt.spine.target.sampled.zeroFree.selectedSeed y :
                        ℝ) *
                    H.receipt.spine.target.sampled.yukawaStep y)) := by
  rcases H.receipt.spine.target.direct_strong_closure_receipt with
    ⟨hem, hweak, hgut, hstrong, hraw⟩
  exact
    ⟨H.receipt.noContinuousFreeParameters,
      (fun p hp => H.receipt.spine.target.accepted_thetaQCD_zero p hp),
      hem, hweak, hgut, hstrong, hraw,
      H.receipt.spine.target.deltaCP_eq_tauProxy_minus_running_depth,
      (fun p hp y =>
        H.receipt.accepted_yukawa_eq_sampled_continuous_residual p hp y)⟩

end PhysicalGrandUnificationHolyGrailReceipt

/-! ## Normal form -/

/-- THEOREM 6: a physical alpha-RG monotonicity producer constructs the current
holy-grail receipt. -/
theorem physicalHolyGrailReceipt_nonempty_of_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      Nonempty (PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) := by
  intro h
  rcases h with ⟨Z, ⟨P⟩⟩
  rcases
    rgMonotonicityGrandUnificationReceipt_nonempty_of_physicalAlphaRGMonotonicity
      (show ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier
        from ⟨Z, ⟨P⟩⟩) with
    ⟨R⟩
  exact ⟨{ zeroFree := Z, physicalRG := P, receipt := R }⟩

/-- THEOREM 7: exact normal form.  The current holy-grail receipt exists iff
the explicit physical alpha-RG producer surface exists. -/
theorem physicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier) ↔
      ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier := by
  constructor
  · rintro ⟨H⟩
    exact H.toPhysicalAlphaRGMonotonicityProducer
  · exact physicalHolyGrailReceipt_nonempty_of_physicalAlphaRGMonotonicity

/-- THEOREM 8: compact citation form for the current grand-unification target.

This is the theorem downstream documents should cite when they need the central
Standard-Model projection receipt without replaying P373-P404. -/
theorem physicalAlphaRGMonotonicity_holy_grail_receipt
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsZeroFreePhysicalAlphaRGMonotonicityProducer Index A CKMCarrier ->
      ∃ H : PhysicalGrandUnificationHolyGrailReceipt Index A CKMCarrier,
        NoContinuousFreeParameters
            H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
          (∀ p : ParameterVector ℝ,
            H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
              p StandardModelParameter.qcd_theta = 0) ∧
          alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
          gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
          alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
          H.receipt.spine.target.strongResidualProducer.correctedOutput =
            alphaStrongDisplayed ℝ ∧
          (ckmCPDepthSum : ℝ) * H.receipt.spine.target.cpRunningSigma =
            cpRawPhaseClaim ℝ ∧
          cpDeltaCPClaim ℝ =
            cpTauProxy ℝ -
              (ckmCPDepthSum : ℝ) * H.receipt.spine.target.cpRunningSigma ∧
          (∀ p : ParameterVector ℝ,
            H.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
              ∀ y : YukawaParameter,
                p (yukawaSlot y) =
                  (H.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y) *
                    AffineRelaxation.realDecayResidual
                      (H.receipt.spine.target.sampled.yukawaLambda y)
                      ((H.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                            H.receipt.spine.target.sampled.zeroFree.selectedSeed y :
                            ℝ) *
                        H.receipt.spine.target.sampled.yukawaStep y)) := by
  intro h
  rcases physicalHolyGrailReceipt_nonempty_of_physicalAlphaRGMonotonicity h with
    ⟨H⟩
  exact ⟨H, H.holy_grail_receipt⟩

end StandardModelConstraint
end SaturationMonoid
