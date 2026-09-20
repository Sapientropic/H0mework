import H0mework.Physics.Matter.SU7ExteriorMatterFieldVariations
import H0mework.Physics.Gauge.SU7ExteriorBreakingVariations
import H0mework.Physics.Gauge.SU7ExteriorMotherCurrentVariation
import H0mework.Physics.Gauge.SU7ExteriorGeometryVariations

/-!
# Stage-8D finite-link matter regressions

Concrete nonzero current/stress witnesses and typed negative regressions for
mirror matter, absent breaking, hand-filled mass, and non-equivariant Yukawa.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations

open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open SU7ExteriorBreakingYukawa

noncomputable section

def stageEightNonzeroCurrentConfigurationAt
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (breakingScalar : ExteriorBreakingScalarCarrier) :
    StageEightVariationConfiguration :=
  stageEightVariationConfigurationOfActual
    geometry connection nonzeroLocalLinkMatterJet breakingScalar

def stageEightNonzeroCurrentConfiguration :
    StageEightVariationConfiguration :=
  stageEightNonzeroCurrentConfigurationAt
    identityCoframeMatterGeometry zeroMotherGaugeConnection
    (0 : ExteriorBreakingScalarCarrier)

def stageEightIdentityMotherVariation :
    LorentzianIndex → DiracMatterEnd :=
  fun direction =>
    if direction = 0 then LinearMap.id else 0

theorem stageEightNonzeroMotherCurrentAt_eq_I
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (breakingScalar : ExteriorBreakingScalarCarrier)
    (coframe_eq_one : geometry.coframe = 1) :
    stageEightMotherCurrent
        (stageEightNonzeroCurrentConfigurationAt
          geometry connection breakingScalar)
        stageEightIdentityMotherVariation = Complex.I := by
  simp [stageEightMotherCurrent, stageEightNonzeroCurrentConfigurationAt,
    stageEightVariationConfigurationOfActual,
    stageEightGeometryReadoutOfActual, stageEightIdentityMotherVariation,
    nonzeroLocalLinkMatterJet, Fin.sum_univ_four, coframe_eq_one]
  change
    diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma geometry 0)
          diracSpinTwoMatterProbe) = 1
  have gammaIdentity :
      inverseCoframeDiracGamma geometry 0 = diracGammaZero := by
    simp [inverseCoframeDiracGamma, coframe_eq_one,
      inv_one, Fin.sum_univ_four, diracGamma]
  rw [gammaIdentity, diracGammaZero_maps_spinTwoProbe,
    diracSpinZeroMatterCoordinate_probe]

theorem stageEightNonzeroMotherCurrent_eq_I :
    stageEightMotherCurrent stageEightNonzeroCurrentConfiguration
        stageEightIdentityMotherVariation = Complex.I := by
  exact stageEightNonzeroMotherCurrentAt_eq_I
    identityCoframeMatterGeometry zeroMotherGaugeConnection
    (0 : ExteriorBreakingScalarCarrier)
    (by simp [identityCoframeMatterGeometry])

theorem stageEightNonzeroMotherCurrent_ne_zero :
    stageEightMotherCurrent stageEightNonzeroCurrentConfiguration ≠ 0 := by
  intro currentZero
  have atVariation := congrFun currentZero
    stageEightIdentityMotherVariation
  rw [stageEightNonzeroMotherCurrent_eq_I] at atVariation
  simp at atVariation

theorem stageEightNonzeroVolumeStress_eq_I :
    stageEightVolumeStress stageEightNonzeroCurrentConfiguration =
      Complex.I := by
  have actionValue := stageEightMatterAction_ofActual_eq_link_add_yukawa
    identityCoframeMatterGeometry zeroMotherGaugeConnection
    nonzeroLocalLinkMatterJet (0 : ExteriorBreakingScalarCarrier)
  rw [zeroMotherLinkFamily_eq_identity,
    nonzeroLocalLinkMatterJet_actionDensity] at actionValue
  simpa [stageEightMatterAction, stageEightVolumeStress,
    stageEightNonzeroCurrentConfiguration,
    stageEightNonzeroCurrentConfigurationAt,
    stageEightVariationConfigurationOfActual,
    stageEightGeometryReadoutOfActual, stageEightActualYukawaDensity,
    identityCoframeMatterGeometry, nonzeroLocalLinkMatterJet] using actionValue

theorem stageEightNonzeroVolumeStress_ne_zero :
    stageEightVolumeStress stageEightNonzeroCurrentConfiguration ≠ 0 := by
  rw [stageEightNonzeroVolumeStress_eq_I]
  exact Complex.I_ne_zero

/-! ## Negative representation, breaking, mass, and equivariance regressions -/

def mirrorExteriorSpinorDegree (index : Fin 3) : ℕ :=
  conjugateExteriorDegree (exteriorSpinorDegree index)

theorem mirrorExteriorSpinorDegree_ne_actual :
    mirrorExteriorSpinorDegree ≠ exteriorSpinorDegree := by
  intro signaturesEqual
  have atDegreeSix := congrFun signaturesEqual (0 : Fin 3)
  norm_num [mirrorExteriorSpinorDegree, exteriorSpinorDegree,
    conjugateExteriorDegree] at atDegreeSix

def MatchesSelectedGeneratedMass
    (candidate : ExteriorDegreeTwoMatterCarrier →ₗ[ℂ]
      ExteriorDegreeSixMatterCarrier) : Prop :=
  candidate = exteriorYukawaMassMap exteriorBreakingScalar

theorem selectedGeneratedMass_rejects_handFilledZero :
    ¬ MatchesSelectedGeneratedMass
      (0 : ExteriorDegreeTwoMatterCarrier →ₗ[ℂ]
        ExteriorDegreeSixMatterCarrier) := by
  intro hmatch
  have atProbe := LinearMap.congr_fun hmatch exteriorYukawaDegreeTwoProbe
  simp only [LinearMap.zero_apply] at atProbe
  exact exteriorYukawaProbe_massMap_ne_zero atProbe.symm

def FormallyTypedYukawa :=
  ExteriorBreakingScalarCarrier →
    ExteriorDegreeTwoMatterCarrier →ₗ[ℂ]
      ExteriorDegreeSixMatterCarrier

def IsSU7EquivariantYukawa
    (candidate : FormallyTypedYukawa) : Prop :=
  ∀ (groupElement : SU7MotherGroup)
      (scalar : ExteriorBreakingScalarCarrier)
      (matter : ExteriorDegreeTwoMatterCarrier),
    candidate
        (exteriorBreakingScalarRepresentation groupElement scalar)
        (su7ExteriorPowerRepresentation 2 groupElement matter) =
      su7ExteriorPowerRepresentation 6 groupElement
        (candidate scalar matter)

/-- This candidate has the right carrier-level type but illegally ignores the
breaking input.  The quarter-turn witness below rejects it. -/
def constantBreakingYukawa : FormallyTypedYukawa :=
  fun _ => exteriorYukawaMassMap exteriorBreakingScalar

theorem exteriorYukawaDegreeTwoProbe_quarterTurn :
    su7ExteriorPowerRepresentation 2 hyperchargeQuarterTurn
        exteriorYukawaDegreeTwoProbe =
      exteriorYukawaDegreeTwoProbe := by
  rw [exteriorYukawaDegreeTwoProbe,
    hyperchargeQuarterTurn_exterior_basis,
    exteriorHyperchargeCharacter_eq_zpow]
  simp [exteriorHyperchargeWeight, exteriorYukawaDegreeTwoIndex,
    exteriorYukawaDegreeTwoSubset, weakZeroIndex, weakOneIndex,
    fundamentalHyperchargeWeight]

theorem exteriorYukawaProbe_output_quarterTurn :
    su7ExteriorPowerRepresentation 6 hyperchargeQuarterTurn
        (exteriorYukawaMassMap exteriorBreakingScalar
          exteriorYukawaDegreeTwoProbe) =
      Complex.I •
        exteriorYukawaMassMap exteriorBreakingScalar
          exteriorYukawaDegreeTwoProbe := by
  have equivariant := exteriorYukawaMassMap_su7_equivariant
    hyperchargeQuarterTurn exteriorBreakingScalar
    exteriorYukawaDegreeTwoProbe
  rw [exteriorBreakingScalar_quarterTurn,
    exteriorYukawaDegreeTwoProbe_quarterTurn] at equivariant
  simpa [exteriorYukawaMassMap] using equivariant.symm

theorem constantBreakingYukawa_not_su7Equivariant :
    ¬ IsSU7EquivariantYukawa constantBreakingYukawa := by
  intro equivariant
  have atQuarterTurn := equivariant hyperchargeQuarterTurn
    (0 : ExteriorBreakingScalarCarrier) exteriorYukawaDegreeTwoProbe
  simp only [constantBreakingYukawa,
    exteriorYukawaDegreeTwoProbe_quarterTurn] at atQuarterTurn
  rw [exteriorYukawaProbe_output_quarterTurn] at atQuarterTurn
  have annihilated :
      ((1 : ℂ) - Complex.I) •
          exteriorYukawaMassMap exteriorBreakingScalar
            exteriorYukawaDegreeTwoProbe = 0 := by
    calc
      _ = (1 : ℂ) •
            exteriorYukawaMassMap exteriorBreakingScalar
              exteriorYukawaDegreeTwoProbe -
          Complex.I •
            exteriorYukawaMassMap exteriorBreakingScalar
              exteriorYukawaDegreeTwoProbe :=
        sub_smul (1 : ℂ) Complex.I _
      _ = _ := by
        rw [one_smul, sub_eq_zero]
        exact atQuarterTurn
  rcases smul_eq_zero.mp annihilated with coefficientZero | massZero
  · have realPart := congrArg Complex.re coefficientZero
    norm_num at realPart
  · exact exteriorYukawaProbe_massMap_ne_zero massZero

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
