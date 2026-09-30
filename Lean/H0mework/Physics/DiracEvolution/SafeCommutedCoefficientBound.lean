import H0mework.Physics.DiracEvolution.SafeCommutedAction

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound

open Set
open ProofFreeRicherAnholonomicSource
open StageNineDiracMatterCoordinateCalculus
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance commutedBoundMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

abbrev MatterCoordinateFirstJetCarrier :=
  MatterCoordinateCarrier ×
    WithLp 2 (LorentzianIndex → MatterCoordinateCarrier)

abbrev MatterCoordinateCommutedReadCarrier :=
  WithLp 2 (LorentzianIndex → MatterCoordinateCarrier)

/-- All source-owned coefficient changed-reads acting on one matter first jet. -/
def fixedMatterCoefficientChangedReadLinear :
    BasePoint →
      MatterCoordinateFirstJetCarrier →ₗ[ℝ]
        MatterCoordinateCommutedReadCarrier :=
  fun point =>
    { toFun := fun jet => WithLp.toLp 2 fun commutedDirection =>
          (∑ direction : LorentzianIndex,
            (fieldDirectionalDerivative
                (fixedEvolutionPrincipalCoordinateCLM direction) point
                commutedDirection)
              (jet.2 direction)) +
          (fieldDirectionalDerivative fixedMatterLowerCoefficient point
              commutedDirection)
            jet.1
      map_add' := by
        intro first second
        apply PiLp.ext
        intro commutedDirection
        simp only [Prod.fst_add, Prod.snd_add, WithLp.ofLp_add,
          Pi.add_apply, map_add, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro parameter jet
        apply PiLp.ext
        intro commutedDirection
        simp only [Prod.smul_fst, Prod.smul_snd, WithLp.ofLp_smul,
          Pi.smul_apply, map_smul, RingHom.id_apply]
        rw [smul_add, Finset.smul_sum] }

def fixedMatterCoefficientChangedReadCLM
    (point : BasePoint) :
    MatterCoordinateFirstJetCarrier →L[ℝ]
      MatterCoordinateCommutedReadCarrier :=
  ⟨fixedMatterCoefficientChangedReadLinear point,
    (fixedMatterCoefficientChangedReadLinear point
      ).continuous_of_finiteDimensional⟩

private theorem principalCoefficientDerivative_contDiff_zero
    (direction commutedDirection : LorentzianIndex) :
    ContDiff ℝ 0 (fun point =>
      fieldDirectionalDerivative
        (fixedEvolutionPrincipalCoordinateCLM direction) point
        commutedDirection) := by
  unfold fieldDirectionalDerivative
  exact
    ((fixedEvolutionPrincipalCoordinateCLM_contDiff direction).fderiv_right
      (m := 0) (by norm_num)).clm_apply contDiff_const

private theorem lowerCoefficientDerivative_contDiff_zero
    (commutedDirection : LorentzianIndex) :
    ContDiff ℝ 0 (fun point =>
      fieldDirectionalDerivative fixedMatterLowerCoefficient point
        commutedDirection) := by
  unfold fieldDirectionalDerivative
  exact
    (fixedMatterLowerCoefficient_contDiff_one.fderiv_right
      (m := 0) (by norm_num)).clm_apply contDiff_const

theorem fixedMatterCoefficientChangedReadCLM_continuous :
    Continuous fixedMatterCoefficientChangedReadCLM := by
  rw [continuous_clm_apply]
  intro jet
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro commutedDirection
  have principalTermContinuous (direction : LorentzianIndex) :
      Continuous (fun point =>
        (fieldDirectionalDerivative
            (fixedEvolutionPrincipalCoordinateCLM direction) point
            commutedDirection)
          (jet.2 direction)) :=
    ((principalCoefficientDerivative_contDiff_zero direction
      commutedDirection).clm_apply contDiff_const).continuous
  have lowerTermContinuous : Continuous (fun point =>
      (fieldDirectionalDerivative fixedMatterLowerCoefficient point
          commutedDirection)
        jet.1) :=
    ((lowerCoefficientDerivative_contDiff_zero commutedDirection).clm_apply
      contDiff_const).continuous
  exact (_root_.continuous_finsetSum _ fun direction _ =>
      principalTermContinuous direction).add
    lowerTermContinuous

def matterCoordinateFirstJetAt
    (field : BasePoint → MatterCoordinateCarrier)
  (point : BasePoint) : MatterCoordinateFirstJetCarrier :=
  (field point, WithLp.toLp 2 fun direction =>
    fieldDirectionalDerivative field point direction)

@[simp] theorem fixedMatterCoefficientChangedReadCLM_apply
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fixedMatterCoefficientChangedReadCLM point
        (matterCoordinateFirstJetAt field point) commutedDirection =
      (∑ direction : LorentzianIndex,
        (fieldDirectionalDerivative
            (fixedEvolutionPrincipalCoordinateCLM direction) point
            commutedDirection)
          (fieldDirectionalDerivative field point direction)) +
      (fieldDirectionalDerivative fixedMatterLowerCoefficient point
          commutedDirection)
        (field point) :=
  rfl

/-- The complete commuted action reads the same generated coefficient block. -/
theorem fixedMatterFirstOrderOperator_directionalDerivative_eq_changedRead
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (point : BasePoint)
    (commutedDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          field)
        point commutedDirection =
      matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fun candidate =>
            fieldDirectionalDerivative field candidate commutedDirection)
          point +
        fixedMatterCoefficientChangedReadCLM point
          (matterCoordinateFirstJetAt field point) commutedDirection := by
  rw [fixedMatterFirstOrderOperator_directionalDerivative
    field fieldSmooth point commutedDirection]
  rw [fixedMatterCoefficientChangedReadCLM_apply]
  abel

/-- On every fixed spacetime box, one source-owned constant bounds all
coefficient changed-reads at once. -/
theorem exists_fixedMatterCoefficientChangedReadBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ‖fixedMatterCoefficientChangedReadCLM
            (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have fieldContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates =>
      fixedMatterCoefficientChangedReadCLM
        (diracMatterSpacetimeCoordinatePoint point.1 point.2)) := by
    exact fixedMatterCoefficientChangedReadCLM_continuous.comp
      diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
  obtain ⟨C, normBound⟩ :=
    carrierCompact.exists_bound_of_continuousOn fieldContinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro time timeMem space spaceMem
  exact (normBound (time, space) ⟨timeMem, spaceMem⟩).trans
    (le_max_left _ _)

theorem fixedMatterCoefficientChangedReadCLM_apply_norm_le_onBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (bound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedMatterCoefficientChangedReadCLM
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spaceMem : space ∈ Icc a b)
    (jet : MatterCoordinateFirstJetCarrier) :
    ‖fixedMatterCoefficientChangedReadCLM
        (diracMatterSpacetimeCoordinatePoint time space) jet‖ ≤
      C * ‖jet‖ := by
  exact (fixedMatterCoefficientChangedReadCLM
      (diracMatterSpacetimeCoordinatePoint time space)).le_opNorm jet |>.trans
    (mul_le_mul_of_nonneg_right
      (bound time timeMem space spaceMem) (norm_nonneg jet))

/-- The source-owned coefficient budget is exactly the forcing bound for the
spacetime-commuted matter action on the same box. -/
theorem fixedMatterCommutedActionDefect_norm_le_onBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (bound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedMatterCoefficientChangedReadCLM
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤ C)
    (field : BasePoint → MatterCoordinateCarrier)
    (fieldSmooth : ContDiff ℝ 2 field)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spaceMem : space ∈ Icc a b)
    (commutedDirection : LorentzianIndex) :
    ‖fieldDirectionalDerivative
          (matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field)
          (diracMatterSpacetimeCoordinatePoint time space)
          commutedDirection -
        matterCoordinateFirstOrderOperator
          fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
          (fun candidate =>
            fieldDirectionalDerivative field candidate commutedDirection)
          (diracMatterSpacetimeCoordinatePoint time space)‖ ≤
      C * ‖matterCoordinateFirstJetAt field
        (diracMatterSpacetimeCoordinatePoint time space)‖ := by
  rw [fixedMatterFirstOrderOperator_directionalDerivative_eq_changedRead
    field fieldSmooth
    (diracMatterSpacetimeCoordinatePoint time space) commutedDirection,
    add_sub_cancel_left]
  exact (PiLp.norm_apply_le
      (fixedMatterCoefficientChangedReadCLM
        (diracMatterSpacetimeCoordinatePoint time space)
        (matterCoordinateFirstJetAt field
          (diracMatterSpacetimeCoordinatePoint time space)))
      commutedDirection).trans
    (fixedMatterCoefficientChangedReadCLM_apply_norm_le_onBox
      timeStart timeEnd a b C bound time timeMem space spaceMem
      (matterCoordinateFirstJetAt field
        (diracMatterSpacetimeCoordinatePoint time space)))

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
