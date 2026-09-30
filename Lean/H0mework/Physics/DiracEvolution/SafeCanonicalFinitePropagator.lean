import H0mework.Physics.DiracEvolution.SafeCanonicalFiniteStep

/-!
# Fixed P506 canonical finite Galerkin propagator

The fixed mother-action operator generates a unique finite evolution from
every coefficient initial value.  Linearity and selector independence turn
that evolution into a continuous linear propagator.  The existing physical
energy estimate then supplies one spatial `L²` stability bound uniformly over
all canonical prefixes.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFinitePropagator

open Set
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField

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

private abbrev CanonicalCoefficient
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :=
  FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount

private theorem fixedP506L0CauchySafeMatterCanonicalSynthesis_apply
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient : CanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount coefficient =
      fixedMatterTrialL2
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode ↦
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        coefficient a b :=
  rfl

def fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (initial : CanonicalCoefficient a b testCount) :
    ℝ → CanonicalCoefficient a b testCount :=
  Classical.choose <|
    exists_galerkinLinearCoefficientCurve_on_Icc
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
        a b testCount)
      initial initialTime timeEnd timeOrder

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (initial : CanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder a b testCount initial
        initialTime = initial :=
  (Classical.choose_spec <|
    exists_galerkinLinearCoefficientCurve_on_Icc
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
        a b testCount)
      initial initialTime timeEnd timeOrder).1

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (initial : CanonicalCoefficient a b testCount)
    (time : ℝ)
    (timeMem : time ∈ Icc initialTime timeEnd) :
    HasDerivWithinAt
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder a b testCount initial)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
            a b testCount initial time))
      (Icc initialTime timeEnd) time := by
  simpa only [fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution, galerkinLinearVelocity] using
    (Classical.choose_spec <|
      exists_galerkinLinearCoefficientCurve_on_Icc
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount)
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
          a b testCount)
        initial initialTime timeEnd timeOrder).2 time timeMem

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_add
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (first second : CanonicalCoefficient a b testCount) :
    EqOn
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
        a b testCount (first + second))
      (fun time =>
        fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
            a b testCount first time +
          fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
            a b testCount second time)
      (Icc initialTime timeEnd) := by
  apply galerkinLinearCoefficientCurve_eqOn_Icc
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
      a b testCount)
    _ _ (first + second) initialTime timeEnd timeOrder
  · exact fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial
      initialTime timeEnd timeOrder a b testCount (first + second)
  · simp only [fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial]
  · intro time timeMem
    simpa [galerkinLinearVelocity] using
      fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution initialTime timeEnd timeOrder
        a b testCount (first + second) time timeMem
  · intro time timeMem
    change HasDerivWithinAt
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
          a b testCount first +
        fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
          a b testCount second)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
              a b testCount first time +
            fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
              a b testCount second time))
      (Icc initialTime timeEnd) time
    simpa only [galerkinLinearVelocity, map_add] using
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution initialTime timeEnd timeOrder
        a b testCount first time timeMem).add
        (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution initialTime timeEnd timeOrder
          a b testCount second time timeMem)

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_smul
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (parameter : ℝ)
    (initial : CanonicalCoefficient a b testCount) :
    EqOn
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
        a b testCount (parameter • initial))
      (fun time => parameter •
        fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
          a b testCount initial time)
      (Icc initialTime timeEnd) := by
  apply galerkinLinearCoefficientCurve_eqOn_Icc
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator_continuous
      a b testCount)
    _ _ (parameter • initial) initialTime timeEnd timeOrder
  · exact fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial
      initialTime timeEnd timeOrder a b testCount (parameter • initial)
  · simp only [fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial]
  · intro time timeMem
    simpa [galerkinLinearVelocity] using
      fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution initialTime timeEnd timeOrder
        a b testCount (parameter • initial) time timeMem
  · intro time timeMem
    change HasDerivWithinAt
      (parameter • fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
        a b testCount initial)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time
          (parameter • fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
            a b testCount initial time))
      (Icc initialTime timeEnd) time
    simpa only [galerkinLinearVelocity, map_smul] using
      (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution initialTime timeEnd timeOrder
        a b testCount initial time timeMem).const_smul parameter

def fixedP506L0CauchySafeMatterCanonicalCoefficientPropagatorLinearMap
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc initialTime timeEnd) :
    CanonicalCoefficient a b testCount →ₗ[ℝ] CanonicalCoefficient a b testCount where
  toFun initial :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder a b testCount initial time
  map_add' first second :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_add initialTime timeEnd timeOrder a b testCount
      first second timeMem
  map_smul' parameter initial :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_smul initialTime timeEnd timeOrder a b testCount
      parameter initial timeMem

def fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc initialTime timeEnd) :
    CanonicalCoefficient a b testCount →L[ℝ] CanonicalCoefficient a b testCount :=
  (fixedP506L0CauchySafeMatterCanonicalCoefficientPropagatorLinearMap
    initialTime timeEnd timeOrder a b testCount time timeMem).toContinuousLinearMap

@[simp] theorem fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator_apply
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc initialTime timeEnd)
    (initial : CanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator initialTime timeEnd timeOrder a b testCount
        time timeMem initial =
      fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
        a b testCount initial time :=
  rfl

@[simp] theorem fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator_initial_apply
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (initial : CanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator initialTime timeEnd timeOrder a b testCount
        initialTime (left_mem_Icc.mpr timeOrder) initial = initial :=
  fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial
    initialTime timeEnd timeOrder a b testCount initial

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_weakEquation
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (initial : CanonicalCoefficient a b testCount)
    (time : ℝ)
    (_timeMem : time ∈ Icc initialTime timeEnd)
    (test : CanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time
            (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
              a b testCount initial time)) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
            a b testCount initial time) test = 0 := by
  have massInvertible :
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).IsInvertible := by
    exact fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time
  have equation := galerkinWeakActionOperator_mass_equation
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
      a b testCount)
    time
    (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
      a b testCount initial time)
    massInvertible
  have tested := congrArg (fun value => inner ℝ value test) equation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator] at tested
  simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
    fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
    fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout,
    fixedP506L0CauchySafeMatterWeakStiffnessForm,
    diracMatterWeakStiffnessForm_apply] using tested

/-- The selected finite propagators inherit one pair of action-owned spatial
`L²` stability constants, uniformly over every canonical prefix and every
initial coefficient. -/
theorem exists_fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator_uniformSpatialL2BoundOnBox
    (initialTime timeEnd : ℝ)
    (timeOrder : initialTime ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 ≤ K ∧
      ∀ (testCount : ℕ)
        (initial : CanonicalCoefficient a b testCount)
        (time : ℝ)
        (timeMem : time ∈ Icc initialTime timeEnd),
        ‖fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
          (fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator initialTime timeEnd timeOrder
            a b testCount time timeMem initial)‖ ^ 2 ≤
          κ⁻¹ *
            (‖fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                a b testCount initialTime initial initial‖ *
              Real.exp (K * (time - initialTime))) := by
  obtain ⟨κ, K, κPositive, KNonnegative, spatialBound⟩ :=
    exists_fixedModeUniformGalerkinSpatialL2BoundOnBox
      initialTime timeEnd a b timeOrder boxOrder
  refine ⟨κ, K, κPositive, KNonnegative, ?_⟩
  intro testCount initial time timeMem
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
      a b testCount
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount
  let curve := fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution initialTime timeEnd timeOrder
    a b testCount initial
  let velocity := fun candidateTime =>
    fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
      a b testCount candidateTime (curve candidateTime)
  have bound := spatialBound
    (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount a b testCount)
    basis basisRegular basisCompact
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount)
    curve velocity
    (by
      intro candidateTime candidateTimeMem
      exact fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution
        initialTime timeEnd timeOrder a b testCount initial
        candidateTime candidateTimeMem)
    (by
      intro candidateTime candidateTimeMem
      exact fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_weakEquation
        initialTime timeEnd timeOrder a b testCount initial
        candidateTime candidateTimeMem (curve candidateTime))
    time timeMem
  have bound' :
      ‖fixedMatterTrialL2 basis (fun mode ↦ (basisRegular mode).continuous)
          basisCompact (curve time) a b‖ ^ 2 ≤
        κ⁻¹ *
          (‖galerkinWeakEnergy
              (fixedP506L0CauchySafeMatterWeakMassForm
                basis (fun mode ↦ (basisRegular mode).continuous)
                  basisCompact)
              curve initialTime‖ *
            Real.exp (K * (time - initialTime))) := by
    rw [fixedMatterTrialL2_norm_sq]
    simpa only [fixedMatterTrialCoordinates] using bound
  simpa only [fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator_apply,
    fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial, galerkinWeakEnergy,
    fixedP506L0CauchySafeMatterCanonicalSynthesis_apply, basis,
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm,
    basisRegular, basisCompact, curve, velocity] using bound'

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFinitePropagator
