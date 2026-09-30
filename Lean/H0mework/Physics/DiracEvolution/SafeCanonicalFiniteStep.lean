import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis
import H0mework.Physics.DiracEvolution.SafeWeakSpatialGalerkinStiffness
import H0mework.Physics.DiracEvolution.SafeL2MassActualization
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Fixed P506 canonical finite Galerkin step

The fixed source initial slice is projected by the mother-action mass form
onto the canonical interior prefix.  The existing finite weak action operator
then generates a local coefficient evolution.  No approximation family,
target solution, or residual is supplied to this producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSymmetricHyperbolicFluxBalance
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open scoped ContDiff Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

local instance two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance (priority := 10000) canonicalCoefficientAddCommGroup
    (modeCount : ℕ) :
    AddCommGroup (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Fin modeCount × MatterCoordinateIndex => ℂ)).toAddCommGroup

local instance (priority := 10000) canonicalCoefficientModule
    (modeCount : ℕ) :
    Module ℝ (DiracMatterGalerkinCoefficient modeCount) :=
  (PiLp.normedSpace 2 ℝ
    (fun _ : Fin modeCount × MatterCoordinateIndex => ℂ)).toModule

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

/-- The fixed source's matter field on one canonical initial slice. -/
def fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
    (initialTime : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (Prepared.matter
      (diracMatterSpacetimeCoordinatePoint initialTime space))

theorem fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_contDiff
    (initialTime : ℝ) :
    ContDiff ℝ ∞
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
        initialTime) := by
  unfold fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth.2.2.2.2.2.2.2.1.comp
    (diracMatterSpacetimeCoordinatePoint_joint_contDiff.comp
      (contDiff_const.prodMk contDiff_id))

private theorem fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_memLp
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
        initialTime)
      2 (volume.restrict (Icc a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  have continuous :=
    (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_contDiff
      initialTime).continuous
  obtain ⟨C, bound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  apply MemLp.of_bound continuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

/-- The fixed P506/L0 source initial slice as a physical spatial `L²` field. -/
def fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b :=
  (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_memLp
    initialTime a b).toLp
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
        initialTime)

private def fixedMatterTrialL2LinearMap
    {modeCount : ℕ}
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (a b : DiracMatterSpatialCoordinates) :
    DiracMatterGalerkinCoefficient modeCount →ₗ[ℝ]
      CauchySafeMatterSpatialL2 a b where
  toFun coefficient :=
    fixedMatterTrialL2 basis basisContinuous basisCompact coefficient a b
  map_add' := fixedMatterTrialL2_add basis basisContinuous basisCompact
    (a := a) (b := b)
  map_smul' := fixedMatterTrialL2_real_smul basis basisContinuous basisCompact
    (a := a) (b := b)

/-- Finite dimensionality makes the canonical synthesis automatically
continuous; no external continuity certificate is stored in the stage. -/
def fixedP506L0CauchySafeMatterCanonicalSynthesis
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    DiracMatterGalerkinCoefficient
        (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
          a b testCount) →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  (fixedMatterTrialL2LinearMap
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    a b).toContinuousLinearMap

private structure CanonicalInitialMassCoordinateBoundData
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) where
  C : ℝ
  bound : ∀ space ∈ Icc a b,
    ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
      initialTime space‖ ≤ C

private def canonicalInitialMassCoordinateBoundData
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CanonicalInitialMassCoordinateBoundData initialTime a b := by
  let existence :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      initialTime initialTime a b
  let C := Classical.choose existence
  have specification := Classical.choose_spec existence
  exact {
    C := C
    bound := fun space spaceMem ↦
      specification.2 initialTime (by simp) space spaceMem }

/-- The source initial mass read pulled back to the canonical finite
coefficient carrier. -/
def fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    DiracMatterGalerkinCoefficient
        (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
          a b testCount) →L[ℝ] ℝ :=
  let bound := canonicalInitialMassCoordinateBoundData initialTime a b
  (fixedP506L0CauchySafeMatterL2MassForm
      initialTime a b bound.C bound.bound
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
        initialTime a b)).comp
    (fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount)

/-- Riesz vector of the exact finite source initial reads. -/
def fixedP506L0CauchySafeMatterCanonicalInitialMassRiesz
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) :=
  (InnerProductSpace.toDual ℝ
    (DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount))).symm
      (fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
        initialTime a b testCount)

/-- The canonical mass projection of the fixed source initial slice. -/
def fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) :=
  (galerkinWeakMassOperator
    (fixedP506L0CauchySafeMatterWeakMassForm
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount))
    initialTime).inverse
      (fixedP506L0CauchySafeMatterCanonicalInitialMassRiesz
        initialTime a b testCount)

private theorem inverseMassProjection_pairing
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (time : ℝ)
    (massInvertible :
      (galerkinWeakMassOperator massForm time).IsInvertible)
    (functional : H →L[ℝ] ℝ)
    (test : H) :
    massForm time
        ((galerkinWeakMassOperator massForm time).inverse
          ((InnerProductSpace.toDual ℝ H).symm functional))
        test =
      functional test := by
  rw [← real_inner_galerkinWeakMassOperator,
    massInvertible.self_apply_inverse]
  change ((InnerProductSpace.toDual ℝ H)
    ((InnerProductSpace.toDual ℝ H).symm functional)) test = functional test
  exact congrArg (fun map : H →L[ℝ] ℝ ↦ map test)
    ((InnerProductSpace.toDual ℝ H).apply_symm_apply functional)

/-- The generated initial coefficient is exactly the mother-action mass
projection of the fixed source initial slice against every finite test. -/
theorem fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massLaw
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount)) :
    let bound := canonicalInitialMassCoordinateBoundData initialTime a b
    fixedP506L0CauchySafeMatterWeakMassForm
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        initialTime
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)
        test =
      fixedP506L0CauchySafeMatterL2MassForm
        initialTime a b bound.C bound.bound
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
          initialTime a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular := fun mode ↦
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount mode
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  let massForm := fixedP506L0CauchySafeMatterWeakMassForm basis
    (fun mode ↦ (basisRegular mode).continuous) basisCompact
  have massInvertible :
      (galerkinWeakMassOperator massForm initialTime).IsInvertible := by
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      initialTime
  simpa only [massForm, basis, basisRegular, basisCompact,
    fixedP506L0CauchySafeMatterCanonicalInitialCoefficient,
    fixedP506L0CauchySafeMatterCanonicalInitialMassRiesz,
    fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional,
    ContinuousLinearMap.comp_apply] using
    inverseMassProjection_pairing massForm initialTime massInvertible
      (fixedP506L0CauchySafeMatterCanonicalInitialMassFunctional
        initialTime a b testCount)
      test

/-- The finite coefficient carrier generated by the first `testCount`
canonical interior tests. -/
abbrev FixedP506L0CauchySafeMatterCanonicalCoefficient
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :=
  DiracMatterGalerkinCoefficient
    (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount a b testCount)

/-- Canonical finite weak mass form of the fixed mother action. -/
def fixedP506L0CauchySafeMatterCanonicalWeakMassForm
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ℝ → FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ]
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ]
        ℝ :=
  fixedP506L0CauchySafeMatterWeakMassForm
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)

/-- Canonical finite stiffness operator of the fixed mother action. -/
def fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ℝ → FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ]
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  fixedP506L0CauchySafeMatterWeakStiffnessOperator
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)

/-- The canonical finite action velocity `-M⁻¹L`; it is generated only
from the fixed source and the canonical prefix. -/
def fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ℝ → FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →L[ℝ]
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  galerkinWeakActionOperator
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
      a b testCount)

/-- The exact canonical finite mother-action operator is continuous in time. -/
theorem fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Continuous
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount) := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  apply galerkinWeakActionOperator_continuous
  · exact galerkinWeakMassOperator_continuous _
      (fixedP506L0CauchySafeMatterWeakMassForm_continuous basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
  · exact fixedP506L0CauchySafeMatterWeakStiffnessOperator_continuous
      basis basisRegular basisCompact
  · intro time
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time

/-- The fixed source and canonical prefix generate a finite weak-action
evolution on the whole supplied source-time interval.  No approximation
family, endpoint state, or operator bound is supplied. -/
theorem exists_fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_on_Icc
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ∃ coefficient : ℝ →
        FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount,
      coefficient initialTime =
          fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount ∧
        ∀ time ∈ Icc initialTime timeEnd,
          HasDerivWithinAt coefficient
              (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                a b testCount time (coefficient time))
              (Icc initialTime timeEnd) time ∧
            galerkinWeakMassOperator
                  (fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                    a b testCount)
                  time
                  (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                    a b testCount time (coefficient time)) +
                fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
                  a b testCount time (coefficient time) = 0 := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
    fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
    basis, basisRegular, basisCompact] using
    exists_galerkinWeakCoefficientCurve_on_Icc
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact))
      (fixedP506L0CauchySafeMatterWeakStiffnessOperator
        basis basisRegular basisCompact)
      (galerkinWeakMassOperator_continuous _
        (fixedP506L0CauchySafeMatterWeakMassForm_continuous basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact))
      (fixedP506L0CauchySafeMatterWeakStiffnessOperator_continuous
        basis basisRegular basisCompact)
      (fun time ↦ fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
        basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
        (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
          a b testCount)
        time)
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount)
      initialTime timeEnd timeOrder

/-- Full-interval finite selector independence for one fixed source prefix. -/
theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_eqOn_Icc
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (first second : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (firstInitial : first initialTime =
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount)
    (secondInitial : second initialTime =
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount)
    (firstEvolution : ∀ time ∈ Icc initialTime timeEnd,
      HasDerivWithinAt first
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time (first time))
        (Icc initialTime timeEnd) time)
    (secondEvolution : ∀ time ∈ Icc initialTime timeEnd,
      HasDerivWithinAt second
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time (second time))
        (Icc initialTime timeEnd) time) :
    EqOn first second (Icc initialTime timeEnd) := by
  exact galerkinLinearCoefficientCurve_eqOn_Icc
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
      a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
      a b testCount)
    first second
    (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
      initialTime a b testCount)
    initialTime timeEnd timeOrder firstInitial secondInitial
    (by simpa [galerkinLinearVelocity] using firstEvolution)
    (by simpa [galerkinLinearVelocity] using secondEvolution)

/-- One finite action-owned step.  Its data are indexed only by the fixed
source slice and the canonical prefix; no approximation family, target field,
or residual is supplied. -/
structure FixedP506L0CauchySafeMatterCanonicalGalerkinStep
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) where
  bound : ℝ≥0
  coefficient : ℝ →
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount
  initialValue :
    coefficient initialTime =
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount
  operatorBound : ∀ time ∈
      Icc
        (initialTime - galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount))
        (initialTime + galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)),
    ‖fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time‖₊ ≤ bound
  evolution : ∀ time ∈
      Icc
        (initialTime - galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount))
        (initialTime + galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)),
    HasDerivWithinAt coefficient
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time (coefficient time))
      (Icc
        (initialTime - galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount))
        (initialTime + galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)))
      time
  weakEquation : ∀ time ∈
      Icc
        (initialTime - galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount))
        (initialTime + galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)),
    galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
          time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (coefficient time)) +
        fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
          a b testCount time (coefficient time) = 0
  forwardBound : ∀ time ∈
      Icc initialTime
        (initialTime + galerkinLinearLocalTimeRadius bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount)),
    ‖coefficient time‖ ≤
      ‖fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount‖ *
        Real.exp ((bound : ℝ) * (time - initialTime))

/-- The fixed source, canonical basis, exact mass projection, and mother-action
operator generate a finite Galerkin step without an externally supplied
family. -/
theorem nonempty_fixedP506L0CauchySafeMatterCanonicalGalerkinStep
    (initialTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Nonempty
      (FixedP506L0CauchySafeMatterCanonicalGalerkinStep
        initialTime a b testCount) := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
  let initial := fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
    initialTime a b testCount
  obtain ⟨bound, coefficient, initialValue, operatorBound,
      evolutionAndEquation, forwardBound⟩ :=
    exists_fixedP506L0CauchySafeMatterActionOwnedWeakGalerkinCoefficientCurve
      basis basisRegular basisCompact
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      initial initialTime
  refine ⟨⟨bound, coefficient, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact initialValue
  · simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
      fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
      basis, basisRegular, basisCompact, initial] using operatorBound
  · intro time timeMem
    simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
      fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
      basis, basisRegular, basisCompact, initial] using
      (evolutionAndEquation time timeMem).1
  · intro time timeMem
    simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
      fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
      fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
      basis, basisRegular, basisCompact, initial] using
      (evolutionAndEquation time timeMem).2
  · simpa only [initial] using forwardBound

/-- The common forward lifetime of two emitted finite steps. -/
def fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (first second : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount) : ℝ :=
  min
    (galerkinLinearLocalTimeRadius first.bound
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount))
    (galerkinLinearLocalTimeRadius second.bound
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount))

theorem fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius_pos
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (first second : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount) :
    0 < fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
      first second := by
  exact lt_min
    (galerkinLinearLocalTimeRadius_pos first.bound
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount))
    (galerkinLinearLocalTimeRadius_pos second.bound
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        initialTime a b testCount))

private theorem canonicalCommonForward_mem_stepInterval
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (first second : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount)
    (time : ℝ)
    (timeMem : time ∈ Icc initialTime
      (initialTime +
        fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
          first second)) :
    time ∈ Icc
      (initialTime - galerkinLinearLocalTimeRadius first.bound
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount))
      (initialTime + galerkinLinearLocalTimeRadius first.bound
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)) := by
  have radiusPos := galerkinLinearLocalTimeRadius_pos first.bound
    (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
      initialTime a b testCount)
  have commonLe :
      fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
          first second ≤
        galerkinLinearLocalTimeRadius first.bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount) := min_le_left _ _
  constructor <;> linarith [timeMem.1, timeMem.2]

private theorem canonicalCommonForward_mem_stepIco
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (first second : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount)
    (time : ℝ)
    (timeMem : time ∈ Ico initialTime
      (initialTime +
        fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
          first second)) :
    time ∈ Ico
      (initialTime - galerkinLinearLocalTimeRadius first.bound
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount))
      (initialTime + galerkinLinearLocalTimeRadius first.bound
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          initialTime a b testCount)) := by
  have radiusPos := galerkinLinearLocalTimeRadius_pos first.bound
    (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
      initialTime a b testCount)
  have commonLe :
      fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
          first second ≤
        galerkinLinearLocalTimeRadius first.bound
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            initialTime a b testCount) := min_le_left _ _
  constructor <;> linarith [timeMem.1, timeMem.2]

/-- Finite ODE selector independence: any two curves emitted from the same
fixed source and canonical prefix coincide on their common generated forward
time slice. -/
theorem fixedP506L0CauchySafeMatterCanonicalGalerkinStep_eqOn_commonForward
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (first second : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount) :
    EqOn first.coefficient second.coefficient
      (Icc initialTime
        (initialTime +
          fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
            first second)) := by
  let velocity : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount →
        FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
    fun time ↦ fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
      a b testCount time
  let lipschitzBound : ℝ≥0 := max first.bound second.bound
  apply ODE_solution_unique_of_mem_Icc_right
    (v := velocity) (s := fun _ ↦ univ) (K := lipschitzBound)
  · intro time timeMem
    have operatorBound := first.operatorBound time
      (canonicalCommonForward_mem_stepInterval first second time
        (Ico_subset_Icc_self timeMem))
    exact
      ((fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time).lipschitz.weaken
          (operatorBound.trans (le_max_left _ _))).lipschitzOnWith
  · intro time timeMem
    exact (first.evolution time
      (canonicalCommonForward_mem_stepInterval first second time timeMem)
      ).continuousWithinAt.mono
        (fun candidate candidateMem ↦
          canonicalCommonForward_mem_stepInterval
            first second candidate candidateMem)
  · intro time timeMem
    exact (first.evolution time
      (canonicalCommonForward_mem_stepInterval first second time
        (Ico_subset_Icc_self timeMem))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem
            (canonicalCommonForward_mem_stepIco first second time timeMem))
  · intro _ _
    trivial
  · intro time timeMem
    have timeMem' : time ∈ Icc initialTime
        (initialTime +
          fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
            second first) := by
      simpa only [
        fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius,
        min_comm] using timeMem
    exact (second.evolution time
      (canonicalCommonForward_mem_stepInterval second first time timeMem')
      ).continuousWithinAt.mono
        (fun candidate candidateMem ↦ by
          apply canonicalCommonForward_mem_stepInterval
            second first candidate
          simpa only [
            fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius,
            min_comm] using candidateMem)
  · intro time timeMem
    have timeMem' : time ∈ Ico initialTime
        (initialTime +
          fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius
            second first) := by
      simpa only [
        fixedP506L0CauchySafeMatterCanonicalGalerkinCommonForwardRadius,
        min_comm] using timeMem
    exact (second.evolution time
      (canonicalCommonForward_mem_stepInterval second first time
        (Ico_subset_Icc_self timeMem'))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem
            (canonicalCommonForward_mem_stepIco second first time timeMem'))
  · intro _ _
    trivial
  · rw [first.initialValue, second.initialValue]

/-- Every emitted finite field vanishes outside the same canonical open box;
the boundary condition is generated by the basis, not stored in the step. -/
theorem FixedP506L0CauchySafeMatterCanonicalGalerkinStep.spatialSynthesis_zeroOutside
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (step : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (step.coefficient time) space = 0 := by
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates,
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount _ space outside]

/-- The generated finite solution has zero spatial energy flux through every
face of the canonical box.  This is the finite boundary/no-inflow receipt. -/
theorem FixedP506L0CauchySafeMatterCanonicalGalerkinStep.energyFlux_zeroOnBoundary
    {initialTime : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {testCount : ℕ}
    (step : FixedP506L0CauchySafeMatterCanonicalGalerkinStep
      initialTime a b testCount)
    (time : ℝ) :
    DiracMatterSpatialFluxZeroOnBoxBoundary
      (diracMatterSpatialEnergyFlux fixedEvolutionPrincipal
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (step.coefficient time))
        time)
      a b := by
  intro direction point _
  have frontOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (b direction) point) := by
    intro frontInterior
    have strict := (frontInterior direction).2
    simp at strict
  have backOutside : ¬ DiracMatterSpatialBoxInterior a b
      (direction.insertNth (a direction) point) := by
    intro backInterior
    have strict := (backInterior direction).1
    simp at strict
  have frontFieldZero := step.spatialSynthesis_zeroOutside time
    (direction.insertNth (b direction) point) frontOutside
  have backFieldZero := step.spatialSynthesis_zeroOutside time
    (direction.insertNth (a direction) point) backOutside
  constructor
  · simp only [diracMatterSpatialEnergyFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, frontFieldZero]
    simp [diracMatterEnergyFlux, diracExteriorMatterCoordinateEnergy,
      diracExteriorMatterCoordinatePairing, dotProduct]
  · simp only [diracMatterSpatialEnergyFlux]
    rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice, backFieldZero]
    simp [diracMatterEnergyFlux, diracExteriorMatterCoordinateEnergy,
      diracExteriorMatterCoordinatePairing, dotProduct]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
