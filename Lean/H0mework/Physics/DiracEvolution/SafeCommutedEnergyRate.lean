import H0mework.Physics.DiracEvolution.SafeCommutedVolterraEvolution
import H0mework.Physics.DiracEvolution.SafeFiniteL2MassRead
import H0mework.Physics.DiracEvolution.SafeWeakEnergyRate

/-!
# Fixed P506/L0 commuted matter energy rate

The source-generated commuted Volterra forcing contributes one controlled
mass-pairing term to the ordinary fixed-action energy rate.  On every compact
spacetime box, the complete pointwise rate is bounded by the physical energy
and the spatial first-jet norm, with no auxiliary closure field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedEnergyRate

open ProofFreeRicherAnholonomicSource
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedCoefficientBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedVolterraEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDiracMatterFiberMassRiesz
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open Set

noncomputable section

set_option autoImplicit false

local instance commutedEnergyMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def fixedCoordinatePointwiseEnergy
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (coordinates : MatterCoordinateCarrier) : ℝ :=
  fixedPointwiseEnergy (time, space)
    (matterCoordinateFiberCoefficientCLM coordinates)

def fixedCoordinatePointwiseRate
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (coordinates : MatterCoordinateCarrier) : ℝ :=
  fixedPointwiseRate (time, space)
    (matterCoordinateFiberCoefficientCLM coordinates)

def fixedCoordinatePointwiseMassPairing
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (first second : MatterCoordinateCarrier) : ℝ :=
  fixedPointwiseEnergyFormValue time space
    (matterCoordinateFiberCoefficientCLM first)
    (matterCoordinateFiberCoefficientCLM second)

private theorem fixedCoordinatePointwiseMassPairing_eq_fiberMassPairing
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (first second : MatterCoordinateCarrier) :
    fixedCoordinatePointwiseMassPairing time space first second =
      matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        first second := by
  unfold fixedCoordinatePointwiseMassPairing fixedPointwiseEnergyFormValue
    diracMatterWeakMassDensity
  rw [fixedPointwiseConstantSpatialSynthesis,
    fixedPointwiseConstantSpatialSynthesis]
  rfl

private theorem matterCoordinateFiberCoefficientCLM_norm
    (coordinates : MatterCoordinateCarrier) :
    ‖matterCoordinateFiberCoefficientCLM coordinates‖ = ‖coordinates‖ := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  rw [PiLp.norm_eq_sum (by norm_num)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp [matterCoordinateFiberCoefficientCLM,
    matterCoordinateFiberCoefficientLinear]

private theorem fixedCoordinatePointwiseEnergy_nonnegative
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (coordinates : MatterCoordinateCarrier) :
    0 ≤ fixedCoordinatePointwiseEnergy time space coordinates := by
  by_cases coordinatesZero : coordinates = 0
  · subst coordinates
    simp [fixedCoordinatePointwiseEnergy, fixedPointwiseEnergy]
  · exact (fixedPointwiseEnergy_positive (time, space)
      (matterCoordinateFiberCoefficientCLM coordinates)
      (fun coefficientZero ↦ coordinatesZero <| by
        have coefficientNormZero :
            ‖matterCoordinateFiberCoefficientCLM coordinates‖ = 0 := by
          rw [coefficientZero, norm_zero]
        rw [matterCoordinateFiberCoefficientCLM_norm] at coefficientNormZero
        exact norm_eq_zero.mp coefficientNormZero)).le

def fixedCommutedVolterraForcing
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (spatialDirection : Fin 3) : MatterCoordinateCarrier :=
  -fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
    (fixedMatterCoefficientChangedReadCLM point
      (matterCoordinateFirstJetAt field point) spatialDirection.succ)

private theorem fixedCoordinatePointwiseMassPairing_norm_le
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (bound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (space : DiracMatterSpatialCoordinates)
    (spaceMem : space ∈ Icc a b)
    (first second : MatterCoordinateCarrier) :
    ‖fixedCoordinatePointwiseMassPairing time space first second‖ ≤
      C * ‖first‖ * ‖second‖ := by
  rw [fixedCoordinatePointwiseMassPairing_eq_fiberMassPairing]
  calc
    ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        first second‖ ≤
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space) first‖ *
          ‖second‖ :=
      (matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space) first).le_opNorm _
    _ ≤
        (‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ *
          ‖first‖) * ‖second‖ := by
      gcongr
      exact (matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)).le_opNorm _
    _ ≤
        (C * ‖first‖) * ‖second‖ := by
      gcongr
      exact bound time timeMem space spaceMem
    _ = C * ‖first‖ * ‖second‖ := rfl

private theorem spatialDerivative_norm_le_spatialJet
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint)
    (spatialDirection : Fin 3) :
    ‖fieldDirectionalDerivative field point spatialDirection.succ‖ ≤
      ‖matterCoordinateSpatialJetAt field point‖ := by
  exact (PiLp.norm_apply_le
    (matterCoordinateSpatialJetAt field point).2 spatialDirection).trans
      (norm_snd_le (matterCoordinateSpatialJetAt field point))

/-- The exact commuted Volterra energy rate is controlled by the ordinary
source-owned rate plus one quadratic value-and-spatial-jet budget. -/
theorem exists_fixedCommutedVolterraEnergyRateBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (field : BasePoint → MatterCoordinateCarrier),
        ContDiff ℝ 2 field →
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            matterCoordinateFirstOrderOperator
              fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
              field (diracMatterSpacetimeCoordinatePoint time space) = 0 →
            ∀ spatialDirection : Fin 3,
              ‖fixedCoordinatePointwiseRate time space
                    (fieldDirectionalDerivative field
                      (diracMatterSpacetimeCoordinatePoint time space)
                      spatialDirection.succ) +
                  2 * fixedCoordinatePointwiseMassPairing time space
                    (fixedCommutedVolterraForcing field
                      (diracMatterSpacetimeCoordinatePoint time space)
                      spatialDirection)
                    (fieldDirectionalDerivative field
                      (diracMatterSpacetimeCoordinatePoint time space)
                      spatialDirection.succ)‖ ≤
                K *
                  (fixedCoordinatePointwiseEnergy time space
                      (fieldDirectionalDerivative field
                        (diracMatterSpacetimeCoordinatePoint time space)
                        spatialDirection.succ) +
                    ‖matterCoordinateSpatialJetAt field
                      (diracMatterSpacetimeCoordinatePoint time space)‖ ^ 2) := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty :=
    ⟨(timeStart, a), ⟨⟨le_rfl, timeOrder⟩, ⟨le_rfl, boxOrder⟩⟩⟩
  obtain ⟨ordinaryRate, ordinaryRateNonnegative, ordinaryRateBound⟩ :=
    exists_fixedModeUniformPointwiseEnergyRateBound
      carrier carrierCompact carrierNonempty
  obtain ⟨massBound, massBoundNonnegative, massEstimate⟩ :=
    exists_fixedMassPairingOperatorBoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨forcingBound, forcingBoundNonnegative, forcingEstimate⟩ :=
    exists_fixedCommutedVolterraForcingSpatialJetBoundOnBox
      timeStart timeEnd a b
  let forcingRate := 2 * massBound * forcingBound
  let K := max ordinaryRate forcingRate
  have forcingRateNonnegative : 0 ≤ forcingRate := by
    dsimp [forcingRate]
    positivity
  refine ⟨K, ordinaryRateNonnegative.trans (le_max_left _ _), ?_⟩
  intro field fieldSmooth time timeMem space spaceMem actionZero
    spatialDirection
  let point := diracMatterSpacetimeCoordinatePoint time space
  let derivative :=
    fieldDirectionalDerivative field point spatialDirection.succ
  let forcing := fixedCommutedVolterraForcing field point spatialDirection
  let jet := matterCoordinateSpatialJetAt field point
  have rateBound :
      ‖fixedCoordinatePointwiseRate time space derivative‖ ≤
        ordinaryRate * fixedCoordinatePointwiseEnergy time space derivative := by
    exact ordinaryRateBound (time, space) ⟨timeMem, spaceMem⟩
      (matterCoordinateFiberCoefficientCLM derivative)
  have forcingNorm : ‖forcing‖ ≤ forcingBound * ‖jet‖ := by
    simpa [forcing, fixedCommutedVolterraForcing, point, jet] using
      forcingEstimate field fieldSmooth time timeMem space spaceMem actionZero
        spatialDirection
  have derivativeNorm : ‖derivative‖ ≤ ‖jet‖ :=
    spatialDerivative_norm_le_spatialJet field point spatialDirection
  have pairingBound :
      ‖fixedCoordinatePointwiseMassPairing time space forcing derivative‖ ≤
        massBound * (forcingBound * ‖jet‖) * ‖jet‖ := by
    calc
      ‖fixedCoordinatePointwiseMassPairing time space forcing derivative‖ ≤
          massBound * ‖forcing‖ * ‖derivative‖ :=
        fixedCoordinatePointwiseMassPairing_norm_le
          timeStart timeEnd a b massBound massEstimate
          time timeMem space spaceMem forcing derivative
      _ ≤ massBound * (forcingBound * ‖jet‖) * ‖jet‖ := by
        gcongr
  have energyNonnegative :
      0 ≤ fixedCoordinatePointwiseEnergy time space derivative :=
    fixedCoordinatePointwiseEnergy_nonnegative time space derivative
  calc
    ‖fixedCoordinatePointwiseRate time space derivative +
        2 * fixedCoordinatePointwiseMassPairing time space forcing derivative‖ ≤
        ‖fixedCoordinatePointwiseRate time space derivative‖ +
          ‖2 * fixedCoordinatePointwiseMassPairing time space forcing derivative‖ :=
      norm_add_le _ _
    _ = ‖fixedCoordinatePointwiseRate time space derivative‖ +
        2 * ‖fixedCoordinatePointwiseMassPairing time space forcing derivative‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ ordinaryRate * fixedCoordinatePointwiseEnergy time space derivative +
        2 * (massBound * (forcingBound * ‖jet‖) * ‖jet‖) :=
      add_le_add rateBound (mul_le_mul_of_nonneg_left pairingBound (by norm_num))
    _ = ordinaryRate * fixedCoordinatePointwiseEnergy time space derivative +
        forcingRate * ‖jet‖ ^ 2 := by
      dsimp [forcingRate]
      ring
    _ ≤ K * fixedCoordinatePointwiseEnergy time space derivative +
        K * ‖jet‖ ^ 2 := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = K * (fixedCoordinatePointwiseEnergy time space derivative +
        ‖jet‖ ^ 2) := by ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedEnergyRate
