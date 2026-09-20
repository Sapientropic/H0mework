import H0mework.Physics.SourceContracts.P432

/-!
# Proposition 433: field-level central holy-grail constants

P432 opens the remaining input surface to one explicit field record.  This
file states the downstream payoff without hiding the central Standard-Model
claims behind the receipt predicate name.

From the opened field producer, Lean returns a strict-matrix holy-grail output
whose receipt explicitly carries:

* zero continuous free parameters;
* `theta_QCD = 0`;
* `alpha_em = 1/137`;
* `sin^2(theta_W) = 3/8`;
* `alpha_GUT^{-1} = 133/3`;
* the displayed strong-coupling closure;
* the CKM running-sigma phase closure;
* the sampled Yukawa residual law;
* the full 19-slot affine-relaxation carrier certificate.

This is still conditional on the field-level producer.  The point is that no
additional downstream wrapper remains between those fields and the central
holy-grail output.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Explicit central output from the field-level front door -/

/-- THEOREM 1: the opened field-level producer directly supplies the central
Standard-Model holy-grail constants and the unified 19-slot parameter-carrier
certificate. -/
theorem matrixGoodCoverPoincareUnified_field_central_holy_grail_constants
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    MatrixGoodCoverPoincareUnifiedProducerFields
        Index A CKMCarrier CoverIndex E F ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter,
        NoContinuousFreeParameters
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            p StandardModelParameter.qcd_theta = 0) ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        O.output.receipt.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) *
            O.output.receipt.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ ∧
        cpDeltaCPClaim ℝ =
          cpTauProxy ℝ -
            (ckmCPDepthSum : ℝ) *
              O.output.receipt.receipt.spine.target.cpRunningSigma ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            ∀ y : YukawaParameter,
              p (yukawaSlot y) =
                O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
                  AffineRelaxation.realDecayResidual
                    (O.output.receipt.receipt.spine.target.sampled.yukawaLambda y)
                    ((O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                        O.output.receipt.receipt.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
                      O.output.receipt.receipt.spine.target.sampled.yukawaStep y)) ∧
        Nonempty
          (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
        Function.Surjective yukawaPoincareSlot ∧
        IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (ParameterVector ℝ) ∧
        (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
          parameterVectorComponentsEquiv ℝ
              (AffineRelaxation.relaxModule target sigma x) =
            AffineRelaxation.relaxModule
              (parameterVectorComponentsEquiv ℝ target)
              sigma
              (parameterVectorComponentsEquiv ℝ x)) := by
  intro P
  rcases
    matrixGoodCoverPoincareUnified_field_holy_grail_normal_form P with
    ⟨O, _hfield, hreceipt, hparam, hconj⟩
  rcases hreceipt with
    ⟨hfree, htheta, halpha, hweak, hgut, hstrong, hcpRaw,
      hcpDelta, hyukawa⟩
  exact
    ⟨O, hfree, htheta, halpha, hweak, hgut, hstrong, hcpRaw,
      hcpDelta, hyukawa, O.generationSlotEquiv,
      O.yukawaPoincareSurjective, O.noFourthGeneration, hparam, hconj⟩

end StandardModelConstraint
end SaturationMonoid
