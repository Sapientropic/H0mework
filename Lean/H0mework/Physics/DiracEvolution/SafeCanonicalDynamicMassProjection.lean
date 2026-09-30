import H0mework.Physics.DiracEvolution.SafeCanonicalDynamicCrossLevelStability

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection

open MeasureTheory Set
open DiracExteriorMatterAction
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineHolonomicField
open scoped ComplexOrder

noncomputable section

set_option autoImplicit false

private theorem canonicalWeakActionResponse_memLp
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    MemLp
      (fixedP506L0CauchySafeMatterWeakActionResponse
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b testCount)
        time coefficient)
      2 (volume.restrict (Icc a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  have continuous :=
    fixedP506L0CauchySafeMatterWeakActionResponse_continuous
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount)
      time coefficient
  obtain ⟨C, bound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  apply MemLp.of_bound continuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

/-- The native action response of one canonical finite state, realized in
the physical spatial `L²` carrier on the same source box. -/
def fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    CauchySafeMatterSpatialL2 a b :=
  (canonicalWeakActionResponse_memLp time a b testCount coefficient).toLp
    (fixedP506L0CauchySafeMatterWeakActionResponse
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      time coefficient)

theorem fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b testCount coefficient space =
        fixedP506L0CauchySafeMatterWeakActionResponse
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          time coefficient space := by
  exact (canonicalWeakActionResponse_memLp
    time a b testCount coefficient).coeFn_toLp

theorem canonicalWeakActionOperator_massIntegral
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient test :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time coefficient)
        test =
      ∫ space,
        diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              time coefficient space))
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space) := by
  have equation := galerkinWeakActionOperator_mass_equation
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
      a b testCount)
    time coefficient
    (fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode =>
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time)
  have tested := congrArg (fun value => inner ℝ value test) equation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator] at tested
  unfold fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator at tested
  rw [fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout] at tested
  change _ +
      (∫ space,
        -diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              time coefficient space))) = 0 at tested
  rw [integral_neg] at tested
  calc
    _ = ∫ space,
        diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              time coefficient space)) := by
      have tested' :
          fixedP506L0CauchySafeMatterCanonicalWeakMassForm
                a b testCount time
                (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                  a b testCount time coefficient)
                test +
              -(∫ space,
                diracExteriorMatterEnergyPairing
                  (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
                  (diracMatterSpatialGalerkinSynthesis
                    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                      a b testCount)
                    test space)
                  (matterCoordinateEquiv.symm
                    (fixedP506L0CauchySafeMatterWeakActionResponse
                      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                        a b testCount)
                      time coefficient space))) = 0 := by
        simpa only [fixedP506L0CauchySafeMatterCanonicalWeakActionOperator,
          fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator]
          using tested
      linarith
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with space
      exact diracExteriorMatterEnergyPairing_symm _
        (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
          time space).isHermitian _ _

private theorem canonicalTrial_zero_outside_box
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b testCount)
        test space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    exact ⟨fun direction ↦ (spaceInterior direction).1.le,
      fun direction ↦ (spaceInterior direction).2.le⟩
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates,
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount _ space outsideInterior]

private theorem canonicalWeakActionResponse_integral_eq_restrict
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient test :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    (∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            time coefficient space))
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          test space)) =
      ∫ space,
        diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (matterCoordinateEquiv.symm
            (fixedP506L0CauchySafeMatterWeakActionResponse
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              time coefficient space))
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space)
        ∂volume.restrict (Icc a b) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
  intro space outside
  rw [canonicalTrial_zero_outside_box a b testCount test space outside]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

private theorem canonicalWeakActionResponse_restrictIntegral_eq_l2MassForm
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (coefficient test :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    (∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (matterCoordinateEquiv.symm
          (fixedP506L0CauchySafeMatterWeakActionResponse
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            time coefficient space))
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          test space)
      ∂volume.restrict (Icc a b)) =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b testCount coefficient)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  have synthesisRead :
      ∀ᵐ space ∂volume.restrict (Icc a b),
        fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test space =
          fixedMatterTrialCoordinates
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space := by
    change ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedMatterTrialL2
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun mode ↦
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
              a b testCount mode).continuous)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          test a b space = _
    exact fixedMatterTrialL2_coe_ae
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      test a b
  rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2_coe_ae
      time a b testCount coefficient,
    synthesisRead] with space responseRead trialRead
  rw [responseRead, trialRead, matterFiberMassPairing_apply]
  unfold fixedMatterTrialCoordinates
  rw [matterCoordinateEquiv.symm_apply_apply]

/-- The finite action velocity is the physical-mass projection of the native
Volterra response onto the same canonical prefix. -/
theorem canonicalWeakActionOperator_l2MassProjectionLaw
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (coefficient test :
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time coefficient)
        test =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (fixedP506L0CauchySafeMatterCanonicalWeakActionResponseL2
          time a b testCount coefficient)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) :=
  (canonicalWeakActionOperator_massIntegral
    time a b testCount coefficient test).trans
      ((canonicalWeakActionResponse_integral_eq_restrict
        time a b testCount coefficient test).trans
          (canonicalWeakActionResponse_restrictIntegral_eq_l2MassForm
            time a b C operatorBound testCount coefficient test))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection
