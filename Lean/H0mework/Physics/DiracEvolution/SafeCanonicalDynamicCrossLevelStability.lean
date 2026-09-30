import H0mework.Physics.DiracEvolution.SafeCanonicalSameSourceGalerkinFamily

/-!
# Fixed P506 canonical dynamic cross-level stability

Canonical prefix inclusion preserves the complete spacetime trial field,
action response, and mother-action stiffness pairing.  Consequently any two
source-owned finite evolutions satisfy one exact difference action law on
every shared canonical test.  No limit, residual, target, or stability
certificate is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicCrossLevelStability

open MeasureTheory Set
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineHolonomicField
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false

local instance (priority := 10000) canonicalCoefficientAddCommGroup
    (modeCount : ℕ) :
    AddCommGroup (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Fin modeCount × MatterCoordinateIndex ↦ ℂ)).toAddCommGroup

local instance (priority := 10000) canonicalCoefficientModule
    (modeCount : ℕ) :
    Module ℝ (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedSpace 2 ℝ
    (fun _ : Fin modeCount × MatterCoordinateIndex ↦ ℂ)).toModule

/-- Prefix inclusion leaves the complete spacetime trial field unchanged. -/
theorem canonicalWeakSpatialCandidate_embedding
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterWeakSpatialCandidate
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
        (canonicalCoefficientEmbedding a b countMonotone coefficient) =
      fixedP506L0CauchySafeMatterWeakSpatialCandidate
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b firstCount)
        coefficient := by
  funext point
  let space :=
    (EuclideanSpace.equiv (Fin 3) ℝ) (canonicalSpatialProjection point)
  have spatialRead := canonicalCoefficientEmbedding_synthesis
    a b countMonotone coefficient space
  apply matterCoordinateEquiv.injective
  simpa only [fixedP506L0CauchySafeMatterWeakSpatialCandidate,
    cauchySafeMatterGalerkinSynthesis_coordinates,
    diracMatterSpatialGalerkinSynthesis_coordinates,
    fixedP506L0CauchySafeMatterWeakSpatialBasisLift, space] using
    congrArg matterCoordinateEquiv spatialRead

/-- The action-native response depends only on the synthesized trial field,
not on its finite-prefix coordinates. -/
theorem canonicalWeakActionResponse_embedding
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterWeakActionResponse
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
        time (canonicalCoefficientEmbedding a b countMonotone coefficient) =
      fixedP506L0CauchySafeMatterWeakActionResponse
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b firstCount)
        time coefficient := by
  unfold fixedP506L0CauchySafeMatterWeakActionResponse
  rw [canonicalWeakSpatialCandidate_embedding a b countMonotone coefficient]

/-- The mother-action stiffness pairing commutes exactly with canonical
prefix inclusion. -/
theorem canonicalWeakStiffnessForm_embedding
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (trial test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterWeakStiffnessForm
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b secondCount)
        time
        (canonicalCoefficientEmbedding a b countMonotone trial)
        (canonicalCoefficientEmbedding a b countMonotone test) =
      fixedP506L0CauchySafeMatterWeakStiffnessForm
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b firstCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b firstCount)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b firstCount)
        time trial test := by
  change
    (∫ space,
      -diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone test) space)
        (matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b secondCount)
            time
            (canonicalCoefficientEmbedding a b countMonotone trial)
            space))) =
    ∫ space,
      -diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b firstCount)
          test space)
        (matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b firstCount)
            time trial space))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun space ↦ by
    change
      -diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b secondCount)
            (canonicalCoefficientEmbedding a b countMonotone test) space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b secondCount)
              time
              (canonicalCoefficientEmbedding a b countMonotone trial)
              space)) =
        -diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b firstCount)
            test space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b firstCount)
              time trial space))
    rw [canonicalCoefficientEmbedding_synthesis a b countMonotone test space]
    rw [congrFun
      (canonicalWeakActionResponse_embedding
        time a b countMonotone trial) space]

/-- Two canonical finite evolutions satisfy the source-free difference action
law on every test already present in the smaller prefix. -/
theorem canonicalCoefficientCurve_crossLevel_sharedTest_weakEquation
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    let small := fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
      timeStart timeEnd timeOrder a b firstCount time
    let large := fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
      timeStart timeEnd timeOrder a b secondCount time
    let smallVelocity :=
      fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b firstCount time small
    let largeVelocity :=
      fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b secondCount time large
    let embeddedTest := canonicalCoefficientEmbedding
      a b countMonotone test
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount time
          (largeVelocity - canonicalCoefficientEmbedding
            a b countMonotone smallVelocity)
          embeddedTest +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b secondCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b secondCount)
          time
          (large - canonicalCoefficientEmbedding a b countMonotone small)
          embeddedTest = 0 := by
  dsimp only
  have largeEquation :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_weakEquation
      timeStart timeEnd timeOrder a b secondCount time timeMem
        (canonicalCoefficientEmbedding a b countMonotone test)
  have smallEquation :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_weakEquation
      timeStart timeEnd timeOrder a b firstCount time timeMem test
  have massEmbedding := canonicalWeakMassForm_embedding
    time a b countMonotone
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b firstCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
            timeStart timeEnd timeOrder a b firstCount time))
      test
  have stiffnessEmbedding := canonicalWeakStiffnessForm_embedding
    time a b countMonotone
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b firstCount time)
      test
  simp only [map_sub, sub_apply]
  rw [massEmbedding, stiffnessEmbedding]
  calc
    _ =
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
              a b secondCount time
              (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b secondCount time
                (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                  timeStart timeEnd timeOrder a b secondCount time))
              (canonicalCoefficientEmbedding a b countMonotone test) +
            fixedP506L0CauchySafeMatterWeakStiffnessForm
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b secondCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b secondCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b secondCount)
              time
              (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                timeStart timeEnd timeOrder a b secondCount time)
              (canonicalCoefficientEmbedding a b countMonotone test)) -
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
              a b firstCount time
              (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b firstCount time
                (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                  timeStart timeEnd timeOrder a b firstCount time))
              test +
            fixedP506L0CauchySafeMatterWeakStiffnessForm
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b firstCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b firstCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b firstCount)
              time
              (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
                timeStart timeEnd timeOrder a b firstCount time)
              test) := by ring
    _ = 0 := by rw [largeEquation, smallEquation, sub_self]

end


end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicCrossLevelStability
