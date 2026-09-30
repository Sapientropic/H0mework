import H0mework.Physics.DiracEvolution.SafeCanonicalResponseL2TimeContinuity

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeMassGeometry

open MeasureTheory Set
open DiracExteriorMatterAction
open StageEightSourceGeneratedMatter
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

local instance fixedMatterCoordinateCarrierNontrivial :
    Nontrivial MatterCoordinateCarrier := by
  refine ⟨⟨0, matterCoordinateEquiv diracSpinTwoMatterProbe, ?_⟩⟩
  intro coordinatesZero
  apply diracSpinTwoMatterProbe_nonzero
  apply matterCoordinateEquiv.injective
  simpa using coordinatesZero.symm

/-- The source-owned positive matter mass energy has one strict coercivity
constant on a whole compact time-space box, before any finite Galerkin level
is selected. -/
theorem exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnTimeSpaceBox
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
          κ * ‖field‖ ^ 2 ≤
            fixedP506L0CauchySafeMatterFiberMassEnergy
              (time, space) field := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty := by
    exact ⟨(timeStart, a), left_mem_Icc.mpr timeOrder,
      left_mem_Icc.mpr boxOrder⟩
  obtain ⟨κ, κPositive, pointwise⟩ :=
    exists_modeUniformQuadraticCoercivity carrier carrierCompact
      carrierNonempty fixedP506L0CauchySafeMatterFiberMassEnergy
      fixedP506L0CauchySafeMatterFiberMassEnergy_joint_continuous
      (fun point pointMem field fieldNonzero ↦
        fixedP506L0CauchySafeMatterFiberMassEnergy_positive
          point field fieldNonzero)
      fixedP506L0CauchySafeMatterFiberMassEnergy_real_smul
  refine ⟨κ, κPositive, ?_⟩
  intro time timeMem space spaceMem field
  exact pointwise (time, space) ⟨timeMem, spaceMem⟩ field

/-- Pointwise source-mass coercivity lifts to the physical spatial `L²`
mass form with the same constant. -/
theorem fixedP506L0CauchySafeMatterL2MassForm_coercive_of_pointwise
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (κ : ℝ)
    (pointwiseCoercivity :
      ∀ space ∈ Icc a b, ∀ field : MatterCoordinateCarrier,
        κ * ‖field‖ ^ 2 ≤
          fixedP506L0CauchySafeMatterFiberMassEnergy
            (time, space) field)
    (field : CauchySafeMatterSpatialL2 a b) :
    κ * ‖field‖ * ‖field‖ ≤
      fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound field field := by
  change κ * ‖field‖ * ‖field‖ ≤ inner ℝ
    (fixedP506L0CauchySafeMatterL2MassAction
      time a b C operatorBound field) field
  rw [L2.inner_def]
  have normSquareIntegrable : Integrable
      (fun space ↦ ‖field space‖ ^ 2)
      (volume.restrict (Icc a b)) := by
    have innerIntegrable := memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp field) (Lp.memLp field))
    refine innerIntegrable.congr ?_
    exact ae_of_all _ fun space ↦ real_inner_self_eq_norm_sq (field space)
  have massInnerIntegrable : Integrable
      (fun space ↦ inner ℝ
        ((fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field) space)
        (field space))
      (volume.restrict (Icc a b)) := by
    exact memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1
        (Lp.memLp (fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field))
        (Lp.memLp field))
  calc
    κ * ‖field‖ * ‖field‖ = κ * ‖field‖ ^ 2 := by ring
    _ = κ * ∫ space, ‖field space‖ ^ 2
        ∂volume.restrict (Icc a b) := by
      rw [cauchySafeMatterSpatialL2_norm_sq_eq_integral]
    _ = ∫ space, κ * ‖field space‖ ^ 2
        ∂volume.restrict (Icc a b) := by
      rw [integral_const_mul]
    _ ≤ ∫ space, inner ℝ
        ((fixedP506L0CauchySafeMatterL2MassAction
          time a b C operatorBound field) space)
        (field space) ∂volume.restrict (Icc a b) := by
      apply integral_mono_ae (normSquareIntegrable.const_mul κ)
        massInnerIntegrable
      filter_upwards [
          fixedP506L0CauchySafeMatterL2MassAction_coe_ae
            time a b C operatorBound field,
          ae_restrict_mem measurableSet_Icc] with space actionEq spaceMem
      rw [actionEq, matterFiberMassRiesz_pairing]
      exact pointwiseCoercivity space spaceMem (field space)

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeMassGeometry
