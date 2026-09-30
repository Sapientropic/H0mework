import H0mework.Physics.DiracEvolution.SafeTemporalJetReduction

/-!
# Fixed P506/L0 commuted Volterra evolution

Differentiating the fixed mother action sends every spatial derivative through
the same source-owned Volterra operator.  The only forcing is the already
generated coefficient changed-read, transported by the generated inverse time
principal.  On each fixed spacetime box this forcing is uniformly controlled
by the value-plus-spatial first jet.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedVolterraEvolution

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open Set

open scoped ContDiff

noncomputable section

set_option autoImplicit false

local instance commutedVolterraMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private def coordinateMatterField
    (field : BasePoint → MatterCoordinateCarrier) :
    BasePoint → DiracExteriorMatterCarrier :=
  fun point ↦ matterCoordinateEquiv.symm (field point)

private theorem spatialDerivativeField_contDiff_one
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (direction : Fin 3) :
    ContDiff ℝ 1
      (fun point ↦ fieldDirectionalDerivative field point direction.succ) := by
  unfold fieldDirectionalDerivative
  exact
    (fieldSmooth.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const

theorem fixedSpatialDerivative_temporalVolterraDefect
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (actionZero :
      ∀ point,
        matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field point = 0)
    (point : BasePoint)
    (spatialDirection : Fin 3) :
    fieldDirectionalDerivative
          (fun candidate ↦
            fieldDirectionalDerivative field candidate spatialDirection.succ)
          point 0 -
        cauchySafeMatterVolterraVelocity Current
          (coordinateMatterField (fun candidate ↦
            fieldDirectionalDerivative field candidate spatialDirection.succ))
          point =
      -fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
        (fixedMatterCoefficientChangedReadCLM point
          (matterCoordinateFirstJetAt field point) spatialDirection.succ) := by
  let derivativeField : BasePoint → MatterCoordinateCarrier :=
    fun candidate ↦
      fieldDirectionalDerivative field candidate spatialDirection.succ
  have derivativeFieldRegular : ContDiff ℝ 1 derivativeField :=
    spatialDerivativeField_contDiff_one field fieldSmooth spatialDirection
  have actionFieldEq :
      (fun candidate ↦
        matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field candidate) = 0 := by
    funext candidate
    exact actionZero candidate
  have actionDerivativeZero :
      fieldDirectionalDerivative
          (matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field)
          point spatialDirection.succ = 0 := by
    change fieldDirectionalDerivative
      (fun candidate ↦
        matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field candidate)
      point spatialDirection.succ = 0
    rw [actionFieldEq]
    simp [fieldDirectionalDerivative]
  have commuted :=
    fixedMatterFirstOrderOperator_directionalDerivative_eq_changedRead
      field fieldSmooth point spatialDirection.succ
  have derivativeAction :
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          derivativeField point =
        -fixedMatterCoefficientChangedReadCLM point
          (matterCoordinateFirstJetAt field point) spatialDirection.succ := by
    rw [actionDerivativeZero] at commuted
    exact eq_neg_of_add_eq_zero_left commuted.symm
  have normalForm :=
    fixedMatterFirstOrderOperator_eq_temporalVolterraDefect
      derivativeField point
        ((derivativeFieldRegular.differentiable (by norm_num)).differentiableAt)
  rw [normalForm] at derivativeAction
  have mapped := congrArg
    (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point)
    derivativeAction
  simp only [map_neg,
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM_left] at mapped
  exact mapped

theorem exists_fixedTemporalPrincipalInverseBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ‖fixedEvolutionTemporalPrincipalInverseCoordinateCLM
            (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have operatorContinuous : Continuous (fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      fixedEvolutionTemporalPrincipalInverseCoordinateCLM
        (diracMatterSpacetimeCoordinatePoint input.1 input.2)) :=
    fixedEvolutionTemporalPrincipalInverseCoordinateCLM_continuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
  obtain ⟨C, bound⟩ :=
    carrierCompact.exists_bound_of_continuousOn
      operatorContinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro time timeMem space spaceMem
  exact (bound (time, space) ⟨timeMem, spaceMem⟩).trans
    (le_max_left _ _)

/-- On a fixed spacetime box, the source-generated forcing in the commuted
Volterra equation is controlled by the value-plus-spatial first jet. -/
theorem exists_fixedCommutedVolterraForcingSpatialJetBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (field : BasePoint → MatterCoordinateCarrier),
        ContDiff ℝ 2 field →
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field (diracMatterSpacetimeCoordinatePoint time space) = 0 →
            ∀ spatialDirection : Fin 3,
              ‖fixedEvolutionTemporalPrincipalInverseCoordinateCLM
                (diracMatterSpacetimeCoordinatePoint time space)
                (fixedMatterCoefficientChangedReadCLM
                  (diracMatterSpacetimeCoordinatePoint time space)
                  (matterCoordinateFirstJetAt field
                    (diracMatterSpacetimeCoordinatePoint time space))
                  spatialDirection.succ)‖ ≤
                C * ‖matterCoordinateSpatialJetAt field
                  (diracMatterSpacetimeCoordinatePoint time space)‖ := by
  obtain ⟨inverseBound, inverseBoundNonnegative, inverseEstimate⟩ :=
    exists_fixedTemporalPrincipalInverseBoundOnBox
      timeStart timeEnd a b
  obtain ⟨coefficientBound, coefficientBoundNonnegative,
      coefficientEstimate⟩ :=
    exists_fixedMatterCoefficientChangedReadBoundOnBox
      timeStart timeEnd a b
  obtain ⟨jetBound, jetBoundNonnegative, jetEstimate⟩ :=
    exists_fixedOnShellFirstJetBoundOnBox timeStart timeEnd a b
  refine ⟨inverseBound * coefficientBound * jetBound,
    mul_nonneg (mul_nonneg inverseBoundNonnegative
      coefficientBoundNonnegative) jetBoundNonnegative, ?_⟩
  intro field fieldSmooth time timeMem space spaceMem actionZero
    spatialDirection
  let point := diracMatterSpacetimeCoordinatePoint time space
  let changedRead := fixedMatterCoefficientChangedReadCLM point
    (matterCoordinateFirstJetAt field point) spatialDirection.succ
  have changedReadBound : ‖changedRead‖ ≤
      coefficientBound * (jetBound *
        ‖matterCoordinateSpatialJetAt field point‖) := by
    calc
      ‖changedRead‖ ≤
          ‖fixedMatterCoefficientChangedReadCLM point
            (matterCoordinateFirstJetAt field point)‖ := by
        simpa [changedRead] using
          PiLp.norm_apply_le
            (fixedMatterCoefficientChangedReadCLM point
              (matterCoordinateFirstJetAt field point))
            spatialDirection.succ
      _ ≤ coefficientBound *
          ‖matterCoordinateFirstJetAt field point‖ :=
        fixedMatterCoefficientChangedReadCLM_apply_norm_le_onBox
          timeStart timeEnd a b coefficientBound coefficientEstimate
          time timeMem space spaceMem (matterCoordinateFirstJetAt field point)
      _ ≤ coefficientBound *
          (jetBound * ‖matterCoordinateSpatialJetAt field point‖) :=
        mul_le_mul_of_nonneg_left
          (matterCoordinateFirstJetAt_norm_le_spatialJet_onBox
            timeStart timeEnd a b jetBound jetEstimate field
            (fieldSmooth.differentiable (by norm_num))
            time timeMem space spaceMem actionZero)
          coefficientBoundNonnegative
  calc
    ‖fixedEvolutionTemporalPrincipalInverseCoordinateCLM point changedRead‖ ≤
        inverseBound * ‖changedRead‖ :=
      (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point).le_opNorm
          changedRead |>.trans
        (mul_le_mul_of_nonneg_right
          (inverseEstimate time timeMem space spaceMem)
          (norm_nonneg changedRead))
    _ ≤ inverseBound *
        (coefficientBound *
          (jetBound * ‖matterCoordinateSpatialJetAt field point‖)) :=
      mul_le_mul_of_nonneg_left changedReadBound inverseBoundNonnegative
    _ = (inverseBound * coefficientBound * jetBound) *
        ‖matterCoordinateSpatialJetAt field point‖ := by ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedVolterraEvolution
