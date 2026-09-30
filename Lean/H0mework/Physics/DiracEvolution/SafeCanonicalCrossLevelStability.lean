import H0mework.Physics.DiracEvolution.SafeCanonicalFiniteStep

/-!
# Fixed P506 canonical Galerkin cross-level stability

Canonical prefix inclusion induces one faithful coefficient embedding.  Its
physical synthesis and mother-action mass pairing are definitionally
independent of the chosen prefix representation.  The source mass projections
therefore form an exact nested orthogonal system with a Pythagorean energy law.
No approximation family, target limit, residual, or stability certificate is
supplied to these constructions.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open scoped ComplexOrder

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

private def scalarPrefixInclusion
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b firstCount →ₗ[ℝ]
      cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b secondCount :=
  Submodule.inclusion
    (cauchySafeMatterCanonicalInteriorScalarPrefixSpace_mono
      a b countMonotone)

/-- Coordinate transition from one canonical scalar prefix basis into a
larger canonical prefix basis. -/
def canonicalScalarPrefixTransition
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (firstMode : Fin
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b firstCount))
    (secondMode : Fin
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b secondCount)) : ℝ :=
  (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
      a b secondCount).repr
    (scalarPrefixInclusion a b countMonotone
      (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
        a b firstCount firstMode)) secondMode

theorem canonicalScalarPrefixTransition_synthesis
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (firstMode : Fin
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b firstCount))
    (space : DiracMatterSpatialCoordinates) :
    ∑ secondMode,
        canonicalScalarPrefixTransition a b countMonotone
            firstMode secondMode *
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount secondMode space =
      cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b firstCount firstMode space := by
  have expansion :=
    (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
      a b secondCount).sum_repr
      (scalarPrefixInclusion a b countMonotone
        (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
          a b firstCount firstMode))
  let inclusion :
      cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b secondCount
        →ₗ[ℝ] (DiracMatterSpatialCoordinates → ℝ) :=
    (Submodule.subtype
      (cauchySafeMatterCanonicalInteriorScalarTestSubmodule a b)).comp
      (Submodule.subtype
        (cauchySafeMatterCanonicalInteriorScalarPrefixSpace
          a b secondCount))
  have functions := congrArg inclusion expansion
  have evaluated := congrFun functions space
  simpa only [canonicalScalarPrefixTransition,
    scalarPrefixInclusion, map_sum, map_smul, inclusion,
    LinearMap.comp_apply, Submodule.subtype_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Submodule.coe_inclusion,
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis] using evaluated

/-- Exact coefficient embedding induced by inclusion of canonical prefix
spaces. -/
def canonicalCoefficientEmbedding
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount :=
  WithLp.toLp 2 fun index ↦
    ∑ firstMode,
      (canonicalScalarPrefixTransition a b countMonotone
        firstMode index.1 : ℂ) *
      coefficient (firstMode, index.2)

@[simp] theorem canonicalCoefficientEmbedding_apply
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount)
    (secondMode : Fin
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b secondCount))
    (coordinate : MatterCoordinateIndex) :
    canonicalCoefficientEmbedding a b countMonotone coefficient
        (secondMode, coordinate) =
      ∑ firstMode,
        (canonicalScalarPrefixTransition a b countMonotone
          firstMode secondMode : ℂ) *
        coefficient (firstMode, coordinate) := by
  rfl

theorem canonicalCoefficientEmbedding_synthesis
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b secondCount)
        (canonicalCoefficientEmbedding a b countMonotone coefficient)
        space =
      diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b firstCount)
        coefficient space := by
  apply matterCoordinateEquiv.injective
  rw [diracMatterSpatialGalerkinSynthesis_coordinates,
    diracMatterSpatialGalerkinSynthesis_coordinates]
  ext coordinate
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    diracMatterGalerkinCoefficientMode,
    canonicalCoefficientEmbedding_apply]
  change
    ∑ secondMode,
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b secondCount secondMode space : ℂ) *
          ∑ firstMode,
            (canonicalScalarPrefixTransition a b countMonotone
              firstMode secondMode : ℂ) *
              coefficient (firstMode, coordinate) =
      ∑ firstMode,
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b firstCount firstMode space : ℂ) *
          coefficient (firstMode, coordinate)
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstMode _
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast (by
    simpa only [mul_comm] using
      canonicalScalarPrefixTransition_synthesis
        a b countMonotone firstMode space)

/-- The exact prefix embedding as a real-linear map on canonical
coefficient carriers. -/
def canonicalCoefficientEmbeddingLinearMap
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b firstCount →ₗ[ℝ]
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount where
  toFun := canonicalCoefficientEmbedding a b countMonotone
  map_add' first second := by
    ext index
    change
      ∑ firstMode,
          (canonicalScalarPrefixTransition a b countMonotone
              firstMode index.1 : ℂ) *
            (first (firstMode, index.2) + second (firstMode, index.2)) =
        (∑ firstMode,
            (canonicalScalarPrefixTransition a b countMonotone
                firstMode index.1 : ℂ) *
              first (firstMode, index.2)) +
          ∑ firstMode,
            (canonicalScalarPrefixTransition a b countMonotone
                firstMode index.1 : ℂ) *
              second (firstMode, index.2)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' parameter coefficient := by
    ext index
    simp only [PiLp.smul_apply]
    change
      ∑ firstMode,
          (canonicalScalarPrefixTransition a b countMonotone
              firstMode index.1 : ℂ) *
            ((parameter : ℂ) * coefficient (firstMode, index.2)) =
        (parameter : ℂ) *
          ∑ firstMode,
            (canonicalScalarPrefixTransition a b countMonotone
                firstMode index.1 : ℂ) *
              coefficient (firstMode, index.2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro firstMode _
    ring

@[simp] theorem canonicalCoefficientEmbeddingLinearMap_apply
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    canonicalCoefficientEmbeddingLinearMap a b countMonotone coefficient =
      canonicalCoefficientEmbedding a b countMonotone coefficient :=
  rfl

/-- Inclusion of canonical prefix spaces is faithful on the finite
matter-coordinate coefficient carrier. -/
theorem canonicalCoefficientEmbeddingLinearMap_injective
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    Function.Injective
      (canonicalCoefficientEmbeddingLinearMap a b countMonotone) := by
  intro first second equality
  apply sub_eq_zero.mp
  by_contra differenceNonzero
  obtain ⟨space, synthesisNonzero⟩ :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
      a b firstCount (first - second) differenceNonzero
  have embeddedDifferenceZero :
      canonicalCoefficientEmbeddingLinearMap a b countMonotone
          (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  have synthesisEquality := canonicalCoefficientEmbedding_synthesis
    a b countMonotone (first - second) space
  have embeddedSynthesisZero :
      diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone (first - second))
          space = 0 := by
    rw [← canonicalCoefficientEmbeddingLinearMap_apply,
      embeddedDifferenceZero]
    apply matterCoordinateEquiv.injective
    rw [diracMatterSpatialGalerkinSynthesis_coordinates]
    rw [map_zero]
    apply Finset.sum_eq_zero
    intro mode _
    have modeZero :
        diracMatterGalerkinCoefficientMode (0 :
          FixedP506L0CauchySafeMatterCanonicalCoefficient a b secondCount)
            mode = 0 := by
      ext coordinate
      rfl
    rw [modeZero]
    simp
  exact synthesisNonzero (synthesisEquality.symm.trans embeddedSynthesisZero)

/-- The canonical mother-action mass pairing commutes exactly with prefix
inclusion. -/
theorem canonicalWeakMassForm_embedding
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (first second : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
        initialTime
        (canonicalCoefficientEmbedding a b countMonotone first)
        (canonicalCoefficientEmbedding a b countMonotone second) =
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b firstCount
        initialTime first second := by
  change
    (∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone first) space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone second) space)) =
    ∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b firstCount) first space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b firstCount) second space)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun space ↦ by
    change diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone first) space)
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone second) space) = _
    rw [canonicalCoefficientEmbedding_synthesis,
      canonicalCoefficientEmbedding_synthesis]

/-- Prefix inclusion is invisible after physical `L²` synthesis. -/
theorem canonicalSynthesis_embedding
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (coefficient : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b secondCount
        (canonicalCoefficientEmbedding a b countMonotone coefficient) =
      fixedP506L0CauchySafeMatterCanonicalSynthesis a b firstCount
        coefficient := by
  change
    fixedMatterTrialL2
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b secondCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b secondCount)
        (canonicalCoefficientEmbedding a b countMonotone coefficient) a b =
      fixedMatterTrialL2
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b firstCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b firstCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b firstCount)
        coefficient a b
  apply Lp.ext
  filter_upwards [
    fixedMatterTrialL2_coe_ae
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b secondCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount)
      (canonicalCoefficientEmbedding a b countMonotone coefficient) a b,
    fixedMatterTrialL2_coe_ae
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b firstCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b firstCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b firstCount)
      coefficient a b] with space largeRead smallRead
  rw [largeRead, smallRead]
  unfold fixedMatterTrialCoordinates
  rw [canonicalCoefficientEmbedding_synthesis]

/-- Small-mouth form of the generated initial mass law. -/
theorem canonicalInitialCoefficient_massFunctional
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)
        test =
      fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
        initialTime a b testCount test := by
  simpa only [fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
    fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional,
    ContinuousLinearMap.comp_apply] using
    fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massLaw
      initialTime a b testCount test

/-- Bound-independent integral readout of the canonical source projection
law.  The auxiliary operator-norm witness used to construct the finite Riesz
coefficient disappears at the mother-action pairing. -/
theorem canonicalInitialCoefficient_massIntegral
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)
        test =
      ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
            initialTime a b space)
          (fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test space)
        ∂volume.restrict (Icc a b) := by
  rw [canonicalInitialCoefficient_massFunctional]
  change fixedP506L0CauchySafeMatterL2MassForm initialTime a b _ _
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 initialTime a b)
      (fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount test) = _
  exact fixedP506L0CauchySafeMatterL2MassForm_eq_integral _ _ _ _ _ _ _

/-- The canonical finite initial coefficient is the ambient physical-mass
projection of the single source initial slice. -/
theorem canonicalInitialCoefficient_l2MassProjectionLaw
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        initialTime space‖ ≤ C)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)
        test =
      fixedP506L0CauchySafeMatterL2MassForm
        initialTime a b C operatorBound
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 initialTime a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount test) := by
  calc
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)
          test =
        ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
              initialTime a b space)
            (fixedP506L0CauchySafeMatterCanonicalSynthesis
              a b testCount test space)
          ∂volume.restrict (Icc a b) :=
      canonicalInitialCoefficient_massIntegral
        initialTime a b testCount test
    _ = fixedP506L0CauchySafeMatterL2MassForm
          initialTime a b C operatorBound
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 initialTime a b)
          (fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount test) :=
      (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
        initialTime a b C operatorBound _ _).symm

/-- The exact source initial mass functional is natural under canonical
prefix inclusion. -/
theorem canonicalInitialMassFunctional_embedding
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
        initialTime a b secondCount
        (canonicalCoefficientEmbedding a b countMonotone test) =
      fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
        initialTime a b firstCount test := by
  unfold fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
  simp only [ContinuousLinearMap.comp_apply]
  apply congrArg
  exact canonicalSynthesis_embedding a b countMonotone test

/-- Nested source projections are exactly orthogonal in the mother-action
mass form: the new prefix only adds a mass-orthogonal correction. -/
theorem canonicalInitialCoefficient_crossLevel_orthogonal
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b firstCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b secondCount -
          canonicalCoefficientEmbedding a b countMonotone
            (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
              initialTime a b firstCount))
        (canonicalCoefficientEmbedding a b countMonotone test) = 0 := by
  rw [map_sub]
  change
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone test) -
        fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
          initialTime
          (canonicalCoefficientEmbedding a b countMonotone
            (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
              initialTime a b firstCount))
          (canonicalCoefficientEmbedding a b countMonotone test) = 0
  rw [sub_eq_zero]
  rw [canonicalWeakMassForm_embedding initialTime a b countMonotone
    (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
      initialTime a b firstCount) test]
  calc
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b secondCount)
          (canonicalCoefficientEmbedding a b countMonotone test) =
        fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
          initialTime a b secondCount
          (canonicalCoefficientEmbedding a b countMonotone test) :=
      canonicalInitialCoefficient_massFunctional initialTime a b secondCount _
    _ = fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
          initialTime a b firstCount test :=
      canonicalInitialMassFunctional_embedding initialTime a b countMonotone
        test
    _ = fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b firstCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b firstCount)
          test :=
      (canonicalInitialCoefficient_massFunctional
        initialTime a b firstCount test).symm

private theorem continuousBilinear_pythagorean
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (form : E →L[ℝ] E →L[ℝ] ℝ)
    (first second : E)
    (orthogonal : form (first - second) second = 0)
    (symmetric : form second (first - second) =
      form (first - second) second) :
    form first first =
      form second second + form (first - second) (first - second) := by
  let difference := first - second
  have firstDecomposition : first = difference + second := by
    simp only [difference]
    abel
  calc
    form first first = form (difference + second) (difference + second) := by
      rw [firstDecomposition]
    _ = form difference difference + form difference second +
        (form second difference + form second second) := by
      rw [map_add form difference second]
      change
        form difference (difference + second) +
            form second (difference + second) = _
      rw [map_add, map_add]
    _ = form second second + form difference difference := by
      rw [show form difference second = 0 by
        simpa only [difference] using orthogonal]
      rw [show form second difference = 0 by
        rw [show form second difference = form difference second by
          simpa only [difference] using symmetric]
        simpa only [difference] using orthogonal]
      ring

/-- Exact Pythagorean stability of nested canonical source projections.
The mass energy gained at the larger prefix is precisely the energy of the
new mass-orthogonal correction. -/
theorem canonicalInitialCoefficient_crossLevel_massPythagorean
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b secondCount)
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b secondCount) =
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b firstCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b firstCount)
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b firstCount) +
        fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
          initialTime
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
              initialTime a b secondCount -
            canonicalCoefficientEmbedding a b countMonotone
              (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
                initialTime a b firstCount))
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
              initialTime a b secondCount -
            canonicalCoefficientEmbedding a b countMonotone
              (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
                initialTime a b firstCount)) := by
  let large := fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
    initialTime a b secondCount
  let small := fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
    initialTime a b firstCount
  let embedded := canonicalCoefficientEmbedding a b countMonotone small
  let form := fixedP506L0CauchySafeMatterCanonicalWeakMassForm
    a b secondCount initialTime
  have orthogonal : form (large - embedded) embedded = 0 := by
    simpa only [form, large, small, embedded] using
      canonicalInitialCoefficient_crossLevel_orthogonal
        initialTime a b countMonotone small
  have symmetric : form embedded (large - embedded) =
      form (large - embedded) embedded := by
    unfold form fixedP506L0CauchySafeMatterCanonicalWeakMassForm
    exact fixedP506L0CauchySafeMatterWeakMassForm_symm
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b secondCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount)
      initialTime embedded (large - embedded)
  have pythagorean := continuousBilinear_pythagorean
    form large embedded orthogonal symmetric
  rw [canonicalWeakMassForm_embedding initialTime a b countMonotone
    small small] at pythagorean
  simpa only [form, large, small, embedded] using pythagorean

/-- Canonical source-projection mass energy is monotone along the nested
prefixes. -/
theorem canonicalInitialCoefficient_crossLevel_massEnergy_mono
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b firstCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b firstCount)
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b firstCount) ≤
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b secondCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b secondCount)
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b secondCount) := by
  rw [canonicalInitialCoefficient_crossLevel_massPythagorean
    initialTime a b countMonotone]
  exact le_add_of_nonneg_right
    (fixedP506L0CauchySafeMatterWeakMassForm_nonnegative
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b secondCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b secondCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b secondCount)
      initialTime
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b secondCount -
        canonicalCoefficientEmbedding a b countMonotone
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b firstCount)))

private theorem continuousBilinear_projection_energy_le
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ambientForm : E →L[ℝ] E →L[ℝ] ℝ)
    (finiteForm : H →L[ℝ] H →L[ℝ] ℝ)
    (synthesis : H →L[ℝ] E)
    (source : E)
    (coefficient : H)
    (ambientSymm : ∀ first second,
      ambientForm first second = ambientForm second first)
    (ambientNonnegative : ∀ field, 0 ≤ ambientForm field field)
    (finiteRead : ∀ first second,
      finiteForm first second =
        ambientForm (synthesis first) (synthesis second))
    (projectionLaw : ∀ test,
      finiteForm coefficient test = ambientForm source (synthesis test)) :
    finiteForm coefficient coefficient ≤ ambientForm source source := by
  let projection := synthesis coefficient
  let difference := source - projection
  have projectionSelf :
      finiteForm coefficient coefficient =
        ambientForm projection projection := by
    simpa only [projection] using finiteRead coefficient coefficient
  have projectionRead :
      finiteForm coefficient coefficient = ambientForm source projection := by
    simpa only [projection] using projectionLaw coefficient
  have orthogonal : ambientForm difference projection = 0 := by
    rw [show difference = source - projection by rfl, map_sub]
    change ambientForm source projection -
        ambientForm projection projection = 0
    rw [← projectionRead, ← projectionSelf, sub_self]
  have reverseOrthogonal : ambientForm projection difference = 0 := by
    rw [ambientSymm projection difference, orthogonal]
  have decomposition : source = difference + projection := by
    simp only [difference]
    abel
  rw [projectionSelf]
  calc
    ambientForm projection projection ≤
        ambientForm difference difference +
          ambientForm projection projection :=
      le_add_of_nonneg_left (ambientNonnegative difference)
    _ = ambientForm source source := by
      rw [decomposition]
      simp only [map_add, add_apply]
      rw [orthogonal, reverseOrthogonal]
      ring

/-- A source-owned finite mass projection is the best approximation in the
ambient mass energy among fields synthesized by the same finite carrier. -/
theorem continuousBilinear_projection_bestApproximation
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ambientForm : E →L[ℝ] E →L[ℝ] ℝ)
    (finiteForm : H →L[ℝ] H →L[ℝ] ℝ)
    (synthesis : H →L[ℝ] E)
    (source : E)
    (coefficient trialCoefficient : H)
    (ambientSymm : ∀ first second,
      ambientForm first second = ambientForm second first)
    (ambientNonnegative : ∀ field, 0 ≤ ambientForm field field)
    (finiteRead : ∀ first second,
      finiteForm first second =
        ambientForm (synthesis first) (synthesis second))
    (projectionLaw : ∀ test,
      finiteForm coefficient test = ambientForm source (synthesis test)) :
    ambientForm (source - synthesis coefficient)
        (source - synthesis coefficient) ≤
      ambientForm (source - synthesis trialCoefficient)
        (source - synthesis trialCoefficient) := by
  let projection := synthesis coefficient
  let trial := synthesis trialCoefficient
  have projectionOrthogonal (test : H) :
      ambientForm (source - projection) (synthesis test) = 0 := by
    calc
      ambientForm (source - projection) (synthesis test) =
          ambientForm source (synthesis test) -
            ambientForm projection (synthesis test) := by
        exact congrArg (fun functional : E →L[ℝ] ℝ ↦ functional (synthesis test))
          (map_sub ambientForm source projection)
      _ = 0 := by
        rw [sub_eq_zero]
        calc
          ambientForm source (synthesis test) = finiteForm coefficient test :=
            (projectionLaw test).symm
          _ = ambientForm (synthesis coefficient) (synthesis test) :=
            finiteRead coefficient test
          _ = ambientForm projection (synthesis test) := rfl
  have synthesisDifference : projection - trial =
      synthesis (coefficient - trialCoefficient) := by
    exact (map_sub synthesis coefficient trialCoefficient).symm
  have reverseOrthogonal :
      ambientForm (projection - trial) (source - projection) = 0 := by
    calc
      ambientForm (projection - trial) (source - projection) =
          ambientForm (source - projection) (projection - trial) :=
        ambientSymm _ _
      _ = ambientForm (source - projection)
          (synthesis (coefficient - trialCoefficient)) :=
        congrArg (fun value ↦ ambientForm (source - projection) value)
          synthesisDifference
      _ = 0 := projectionOrthogonal (coefficient - trialCoefficient)
  have forwardOrthogonal :
      ambientForm (source - projection) (projection - trial) = 0 :=
    (ambientSymm _ _).trans reverseOrthogonal
  have decomposition : source - trial =
      (projection - trial) + (source - projection) := by
    abel
  have pythagorean :
      ambientForm (source - trial) (source - trial) =
        ambientForm (projection - trial) (projection - trial) +
          ambientForm (source - projection) (source - projection) := by
    calc
      ambientForm (source - trial) (source - trial) =
          ambientForm ((projection - trial) + (source - projection))
            ((projection - trial) + (source - projection)) :=
        congrArg (fun value ↦ ambientForm value value) decomposition
      _ = ambientForm (projection - trial) (projection - trial) +
          ambientForm (source - projection) (source - projection) := by
        simp only [map_add, add_apply, reverseOrthogonal, forwardOrthogonal]
        ring
  change ambientForm (source - projection) (source - projection) ≤
    ambientForm (source - trial) (source - trial)
  rw [pythagorean]
  exact le_add_of_nonneg_left (ambientNonnegative (projection - trial))

theorem fixedP506L0CauchySafeMatterL2MassForm_nonnegative
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (field : CauchySafeMatterSpatialL2 a b) :
    0 ≤ fixedP506L0CauchySafeMatterL2MassForm
      time a b C operatorBound field field := by
  rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
  apply integral_nonneg
  intro space
  change (0 : ℝ) ≤ matterFiberMassPairing
    (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
    (field space) (field space)
  rw [matterFiberMassPairing_apply,
    diracExteriorMatterEnergyPairing_self]
  exact diracExteriorMatterCoordinateEnergy_nonneg _
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
      time space).posSemidef _

/-- Source-owned physical mass energy that uniformly bounds every canonical
finite mass projection. -/
def fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) : ℝ :=
  ∫ space,
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
        initialTime a b space)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
        initialTime a b space)
    ∂volume.restrict (Icc a b)

theorem fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy_nonnegative
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    0 ≤ fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
      initialTime a b := by
  apply integral_nonneg
  intro space
  change (0 : ℝ) ≤ matterFiberMassPairing
    (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
      initialTime a b space)
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
      initialTime a b space)
  rw [matterFiberMassPairing_apply, diracExteriorMatterEnergyPairing_self]
  exact diracExteriorMatterCoordinateEnergy_nonneg _
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
      initialTime space).posSemidef _

/-- Every canonical source projection is bounded by the mass energy of the
single source initial slice, independently of the prefix size. -/
theorem fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massEnergy_le_source
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount) ≤
      fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
        initialTime a b := by
  obtain ⟨C, _, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      initialTime initialTime a b
  have timeMem : initialTime ∈ Icc initialTime initialTime := by simp
  let bound := operatorBound initialTime timeMem
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisContinuous := fun mode ↦
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount mode).continuous
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  let ambientForm := fixedP506L0CauchySafeMatterL2MassForm
    initialTime a b C bound
  let finiteForm := fixedP506L0CauchySafeMatterCanonicalWeakMassForm
    a b testCount initialTime
  let synthesis := fixedP506L0CauchySafeMatterCanonicalSynthesis
    a b testCount
  let source := fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
    initialTime a b
  let coefficient := fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
    initialTime a b testCount
  have ambientSymm : ∀ first second,
      ambientForm first second = ambientForm second first := by
    intro first second
    exact fixedP506L0CauchySafeMatterL2MassForm_symm
      initialTime a b C bound first second
  have ambientNonnegative : ∀ field, 0 ≤ ambientForm field field := by
    intro field
    exact fixedP506L0CauchySafeMatterL2MassForm_nonnegative
      initialTime a b C bound field
  have finiteRead : ∀ first second,
      finiteForm first second =
        ambientForm (synthesis first) (synthesis second) := by
    intro first second
    exact fixedP506L0CauchySafeMatterWeakMassForm_eq_l2MassForm_trial
      basis basisContinuous basisCompact initialTime a b
      (fun mode point outside ↦
        cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
          a b testCount mode point outside)
      C bound first second
  have projectionLaw : ∀ test,
      finiteForm coefficient test = ambientForm source (synthesis test) := by
    intro test
    have law :=
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massLaw
        initialTime a b testCount test
    calc
      finiteForm coefficient test = _ := law
      _ = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
            (source space) (synthesis test space)
          ∂volume.restrict (Icc a b) :=
        fixedP506L0CauchySafeMatterL2MassForm_eq_integral _ _ _ _ _ _ _
      _ = ambientForm source (synthesis test) :=
        (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
          initialTime a b C bound source (synthesis test)).symm
  have boundResult := continuousBilinear_projection_energy_le
    ambientForm finiteForm synthesis source coefficient ambientSymm
    ambientNonnegative finiteRead projectionLaw
  have sourceEnergy :
      ambientForm source source =
        fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
          initialTime a b := by
    calc
      ambientForm source source = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix initialTime space)
            (source space) (source space)
          ∂volume.restrict (Icc a b) :=
        fixedP506L0CauchySafeMatterL2MassForm_eq_integral
          initialTime a b C bound source source
      _ = fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
          initialTime a b := rfl
  exact boundResult.trans_eq sourceEnergy

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
