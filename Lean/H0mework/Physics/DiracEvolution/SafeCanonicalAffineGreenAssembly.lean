import H0mework.Physics.DiracEvolution.SafeCanonicalAffinePhysicalActionTransport
import H0mework.Physics.DiracEvolution.SafeGreenRateL2Read

/-!
# Fixed P506/L0 canonical affine Green assembly

The ambient Green read of each source-generated affine Galerkin field is the
generated correction rate plus the dynamic mass rate of the fixed source
lift.  This identifies the exact finite read consumed by the physical weak
limit without changing the canonical approximation producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false

def canonicalSourceLiftMassRate
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  ∫ space in Icc a b,
    diracExteriorMatterEnergyPairing
      (fixedEvolutionPrincipalDirectionalDerivativeOnSlice
        canonicalLorentzianTimeDirection time space)
      diracSpinTwoMatterProbe
      (matterCoordinateEquiv.symm
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
          (diracMatterSpacetimeCoordinatePoint time space)))

private theorem sourceInitialL2_zero_coe_ae
    (a b : DiracMatterSpatialCoordinates) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space =
        matterCoordinateEquiv diracSpinTwoMatterProbe := by
  have sourceRead : ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space =
        fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates 0 space := by
    unfold fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
    exact MemLp.coeFn_toLp _
  filter_upwards [sourceRead] with space read
  rw [read, fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_zero]

private theorem boundaryLiftActionResponse_eq_constantFieldActionResponse
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    boundaryLiftActionResponse (time, space) =
      fixedP506L0CauchySafeMatterConstantFieldActionResponse
        diracSpinTwoMatterProbe time space := by
  unfold boundaryLiftActionResponse boundaryLiftCoefficient
  exact
    (fixedP506L0CauchySafeMatterConstantFieldActionResponse_eq_fixedConstant
      diracSpinTwoMatterProbe time space).symm

theorem canonicalSourceLift_greenRate
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (time : ℝ) :
    fixedP506L0CauchySafeMatterGreenRateL2Read
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
          a b test)
        time a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) =
      canonicalSourceLiftMassRate a b test time -
        boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) := by
  rw [fixedP506L0CauchySafeMatterGreenRateL2Read_eq_integral]
  rw [show (∫ space in Icc a b,
      fixedP506L0CauchySafeMatterGreenRateFiberRead
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (time, space)
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space)) =
      ∫ space in Icc a b,
        fixedP506L0CauchySafeMatterGreenRateFiberRead
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (time, space) (matterCoordinateEquiv diracSpinTwoMatterProbe) by
    apply integral_congr_ae
    filter_upwards [sourceInitialL2_zero_coe_ae a b] with space sourceRead
    rw [sourceRead]]
  have assembly :=
    fixedP506L0CauchySafeMatterGreenRateFiberRead_constantField_box
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
        a b testCount test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation
        a b testCount test entered)
      diracSpinTwoMatterProbe time a b boxOrder
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
        a b testCount)
  have stiffnessEq :
      diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun _coefficient space ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              diracSpinTwoMatterProbe time space)
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) 0 =
        boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) := by
    have responseEq :
        (fun (_coefficient :
            FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
            (space : DiracMatterSpatialCoordinates) ↦
          fixedP506L0CauchySafeMatterConstantFieldActionResponse
            diracSpinTwoMatterProbe time space) =
          (fun (_coefficient :
              FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
              (space : DiracMatterSpatialCoordinates) ↦
            boundaryLiftActionResponse (time, space)) := by
      funext _coefficient space
      exact
        (boundaryLiftActionResponse_eq_constantFieldActionResponse
          time space).symm
    change
      diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun _coefficient space ↦
            fixedP506L0CauchySafeMatterConstantFieldActionResponse
              diracSpinTwoMatterProbe time space)
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) 0 =
        diracMatterWeakStiffnessFormValue
          (fixedP506L0CauchySafeMatterWeakMassMatrix time)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun _coefficient space ↦ boundaryLiftActionResponse (time, space))
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) 0
    rw [responseEq]
  rw [assembly, stiffnessEq]
  rfl

def canonicalAffineCorrectionL2
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  fixedMatterTrialL2
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount time)
    a b

def canonicalAffineFiniteMatterL2
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b +
    canonicalAffineCorrectionL2
      timeEnd timeNonnegative a b testCount time

theorem canonicalAffineFiniteMatterL2_greenRate
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (time : ℝ) :
    fixedP506L0CauchySafeMatterGreenRateL2Read
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
          a b test)
        time a b
        (canonicalAffineFiniteMatterL2
          timeEnd timeNonnegative a b testCount time) =
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).rate time +
        canonicalSourceLiftMassRate a b test time := by
  have correctionRead :=
    fixedP506L0CauchySafeMatterGreenRateL2Read_fixedTrial
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
        a b testCount test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
        a b test)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation
        a b testCount test entered)
      time a b boxOrder
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
        a b testCount)
  have liftRead := canonicalSourceLift_greenRate
    a b boxOrder testCount test entered time
  have rateEq :
      (canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b testCount test).rate time =
        galerkinWeakTestPairingRate
            (fixedP506L0CauchySafeMatterWeakMassFormDerivative
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b testCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b testCount))
            (fixedP506L0CauchySafeMatterWeakStiffnessForm
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                a b testCount)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b testCount))
            (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
              timeEnd timeNonnegative a b testCount)
            (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
              a b testCount test)
            time -
          boundaryLiftStiffnessFunctional a b testCount time
            (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
              a b testCount test) := rfl
  unfold canonicalAffineFiniteMatterL2 canonicalAffineCorrectionL2
  rw [map_add, liftRead, correctionRead, rateEq]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly
