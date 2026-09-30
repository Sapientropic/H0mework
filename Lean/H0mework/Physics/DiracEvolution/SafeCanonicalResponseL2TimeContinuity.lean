import H0mework.Physics.DiracEvolution.SafeCanonicalDynamicMassProjection

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalResponseL2TimeContinuity

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDynamicBreakingVacuum

noncomputable section

set_option autoImplicit false

private theorem canonicalResponseL2_norm_sub_sq
    (time referenceTime : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    ‖fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b testCount coefficient -
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          referenceTime a b testCount coefficient‖ ^ 2 =
      ∫ space in Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              time coefficient space -
            fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              referenceTime coefficient space‖ ^ 2 := by
  rw [cauchySafeMatterSpatialL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub
      (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        time a b testCount coefficient)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        referenceTime a b testCount coefficient),
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
      time a b testCount coefficient,
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
      referenceTime a b testCount coefficient] with space subRead timeRead referenceRead
  rw [subRead]
  change
    ‖fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b testCount coefficient space -
        fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          referenceTime a b testCount coefficient space‖ ^ 2 = _
  rw [timeRead, referenceRead]

theorem fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_continuous
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    Continuous fun time ↦
      fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
        time a b testCount coefficient := by
  rw [continuous_iff_continuousAt]
  intro referenceTime
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have responseJoint :
      Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
        fixedP506L0CauchySafeMatterWeakActionResponse
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          input.1 coefficient input.2 :=
    fixedP506L0CauchySafeMatterWeakActionResponse_joint_continuous
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      coefficient
  have integralContinuous :
      Continuous fun time ↦
        ∫ space in Icc a b,
          ‖fixedP506L0CauchySafeMatterWeakActionResponse
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                  a b testCount)
                time coefficient space -
              fixedP506L0CauchySafeMatterWeakActionResponse
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                  a b testCount)
                referenceTime coefficient space‖ ^ 2 := by
    apply continuous_parametric_integral_of_continuous
      (hs := isCompact_Icc)
    fun_prop
  have squareTendsto :
      Tendsto
        (fun time ↦
          ‖fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
                time a b testCount coefficient -
              fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
                referenceTime a b testCount coefficient‖ ^ 2)
        (nhds referenceTime) (nhds 0) := by
    have integralAtReference :
        (∫ space in Icc a b,
          ‖fixedP506L0CauchySafeMatterWeakActionResponse
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                  a b testCount)
                referenceTime coefficient space -
              fixedP506L0CauchySafeMatterWeakActionResponse
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                  a b testCount)
              referenceTime coefficient space‖ ^ 2) = 0 := by
      simp
    have integralTendstoZero :
        Tendsto
          (fun time ↦
            ∫ space in Icc a b,
              ‖fixedP506L0CauchySafeMatterWeakActionResponse
                    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                      a b testCount)
                    time coefficient space -
                  fixedP506L0CauchySafeMatterWeakActionResponse
                    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                      a b testCount)
                    referenceTime coefficient space‖ ^ 2)
          (nhds referenceTime) (nhds 0) := by
      have integralTendsto :=
        integralContinuous.continuousAt (x := referenceTime)
      change Tendsto _ (nhds referenceTime) (nhds
        ((fun time ↦
          ∫ space in Icc a b,
            ‖fixedP506L0CauchySafeMatterWeakActionResponse
                  (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                    a b testCount)
                  time coefficient space -
                fixedP506L0CauchySafeMatterWeakActionResponse
                  (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                    a b testCount)
                  referenceTime coefficient space‖ ^ 2) referenceTime)) at integralTendsto
      have endpointEq :
          ((fun time ↦
            ∫ space in Icc a b,
              ‖fixedP506L0CauchySafeMatterWeakActionResponse
                    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                      a b testCount)
                    time coefficient space -
                  fixedP506L0CauchySafeMatterWeakActionResponse
                    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                      a b testCount)
                    referenceTime coefficient space‖ ^ 2) referenceTime) = 0 :=
        integralAtReference
      rw [endpointEq] at integralTendsto
      exact integralTendsto
    exact integralTendstoZero.congr'
      (Filter.Eventually.of_forall fun time ↦
        (canonicalResponseL2_norm_sub_sq
          time referenceTime a b testCount coefficient).symm)
  have sqrtTendsto :=
    Real.continuous_sqrt.continuousAt.tendsto.comp squareTendsto
  have sqrtTendstoZero :
      Tendsto
        ((fun value : ℝ ↦ √value) ∘
          fun time ↦
            ‖fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
                  time a b testCount coefficient -
                fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
                  referenceTime a b testCount coefficient‖ ^ 2)
        (nhds referenceTime) (nhds 0) := by
    simpa only [Real.sqrt_zero] using sqrtTendsto
  exact sqrtTendstoZero.congr'
    (Filter.Eventually.of_forall fun time ↦ by
      simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalResponseL2TimeContinuity
