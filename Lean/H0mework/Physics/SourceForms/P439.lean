import H0mework.Physics.SourceForms.P438

/-!
# Proposition 439: zero-free sampled-clock holy-grail normal form

P438 removes the final corridor wrapper and states the current formal-exact
holy-grail front door as one primitive atom object plus two native physical
conditions.  P377/P378 had already shown that a primitive atom object is only
the opened form of:

* a zero-continuous-free 19-slot Standard-Model certificate;
* sampled Yukawa clocks whose rates equal the selected running sigma values.

This file composes those normal forms.  The current formal-exact holy-grail
front door is exactly:

* `zeroFree`;
* `yukawaLambda`;
* `yukawaStep`;
* the sampling equation;
* `zeroFree.running.fourPi = realFourPi`;
* every selected Yukawa sigma below the weak sigma endpoint.

That is the current Lean spine's naked producer surface: no primitive-atom,
matrix-table, corridor, geometry, or receipt wrapper remains.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The fully opened current producer surface: a zero-free 19-slot certificate,
sampled Yukawa clocks, and the two physical sigma-corridor fields. -/
def ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ zeroFree :
      ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier,
    ∃ yukawaLambda : YukawaParameter -> ℝ,
      ∃ yukawaStep : YukawaParameter -> ℝ,
        (∀ y : YukawaParameter,
          zeroFree.running.sigma (StandardModelScaleCode.yukawa y) =
            AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)) ∧
        zeroFree.running.fourPi = realFourPi ∧
        ∀ y : YukawaParameter,
          zeroFree.running.sigma (StandardModelScaleCode.yukawa y) ≤
            zeroFree.running.sigma StandardModelScaleCode.weak

/-- THEOREM 1: P438's naked primitive front door is exactly the zero-free
sampled-clock physical sigma-corridor surface. -/
theorem nakedPrimitive_iff_existsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor :
    ExistsNakedPrimitiveAtomNativeSigmaCorridor Index A CKMCarrier ↔
      ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  constructor
  · rintro ⟨atoms, hfour, hyukawa⟩
    exact
      ⟨atoms.toZeroFree,
        atoms.yukawaLambda,
        atoms.yukawaStep,
        atoms.selected_yukawa_sigma_sampled,
        by
          simpa [GrandUnificationPrimitiveProducerAtoms.toZeroFree,
            GrandUnificationPrimitiveProducerAtoms.toRunning]
            using hfour,
        by
          intro y
          simpa [GrandUnificationPrimitiveProducerAtoms.toZeroFree,
            GrandUnificationPrimitiveProducerAtoms.toRunning]
            using hyukawa y⟩
  · rintro ⟨zeroFree, yukawaLambda, yukawaStep, hsampled, hfour, hyukawa⟩
    let M : MinimalGrandUnificationProducerKernel Index A CKMCarrier :=
      { zeroFree := zeroFree
        yukawaLambda := yukawaLambda
        yukawaStep := yukawaStep
        selected_yukawa_sigma_sampled := hsampled }
    let atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier :=
      GrandUnificationPrimitiveProducerAtoms.ofMinimalProducerKernel M
    exact
      ⟨atoms,
        by
          simpa [atoms, M, GrandUnificationPrimitiveProducerAtoms.ofMinimalProducerKernel]
            using hfour,
        by
          intro y
          simpa [atoms, M, GrandUnificationPrimitiveProducerAtoms.ofMinimalProducerKernel]
            using hyukawa y⟩

/-- THEOREM 2: under the P435 formal-exact geometry audit, the current strict
good-cover holy-grail output exists exactly when the zero-free sampled-clock
physical sigma-corridor surface exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_under_currentFormalExactGeometry
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_nakedPrimitive_under_currentFormalExactGeometry.trans
      nakedPrimitive_iff_existsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor

/-- THEOREM 3: a fully opened zero-free sampled-clock physical sigma-corridor
surface directly supplies a formal-exact strict good-cover holy-grail output. -/
theorem zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_supplies_currentFormalExactGeometry_holyGrailOutput
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro h
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_under_currentFormalExactGeometry).mpr h

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
