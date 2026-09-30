import H0mework.Physics.DiracEvolution.WeakSpatialGalerkinStiffness
import H0mework.Physics.DiracEvolution.SafeWeakSpatialGalerkinMass

/-!
# Fixed P506/L0 action-owned weak spatial stiffness

The canonical spatial basis is lifted constantly along Cauchy time lines and
read by the exact post-EC mother-action velocity.  Pairing that velocity with
the positive time principal generates the complete finite weak stiffness
operator and hence the actual weak Galerkin coefficient curve.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open scoped ContDiff Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

private abbrev Input : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

/-- Lift a spatial test basis constantly along the canonical time lines. -/
def fixedP506L0CauchySafeMatterWeakSpatialBasisLift
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (mode : Fin modeCount)
    (point : BasePoint) : ℝ :=
  basis mode
    ((EuclideanSpace.equiv (Fin 3) ℝ) (canonicalSpatialProjection point))

theorem fixedP506L0CauchySafeMatterWeakSpatialBasisLift_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (mode : Fin modeCount) :
    ContDiff ℝ 1
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift basis mode) := by
  unfold fixedP506L0CauchySafeMatterWeakSpatialBasisLift
  exact (basisRegular mode).comp
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearEquiv.contDiff.comp
      canonicalSpatialProjection.contDiff)

/-- The finite spatial trial field read by the fixed mother action. -/
def fixedP506L0CauchySafeMatterWeakSpatialCandidate
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    BasePoint → DiracExteriorMatterCarrier :=
  cauchySafeMatterGalerkinSynthesis
    (fixedP506L0CauchySafeMatterWeakSpatialBasisLift basis) coefficient

theorem fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient
        (diracMatterSpacetimeCoordinatePoint time space) =
      diracMatterSpatialGalerkinSynthesis basis coefficient space := by
  apply matterCoordinateEquiv.injective
  simp only [fixedP506L0CauchySafeMatterWeakSpatialCandidate,
    cauchySafeMatterGalerkinSynthesis_coordinates,
    diracMatterSpatialGalerkinSynthesis_coordinates]
  apply Finset.sum_congr rfl
  intro mode _
  congr 1
  unfold fixedP506L0CauchySafeMatterWeakSpatialBasisLift
  unfold diracMatterSpacetimeCoordinatePoint
  rw [canonicalSpatialProjection_slice]
  rfl

/-- Same-source action velocity of a finite spatial trial field. -/
def fixedP506L0CauchySafeMatterWeakActionResponse
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  cauchySafeMatterVolterraVelocity Input
    (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient)
    (diracMatterSpacetimeCoordinatePoint time space)

theorem fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    Differentiable ℝ (fun point ↦ matterCoordinateEquiv
      (fixedP506L0CauchySafeMatterWeakSpatialCandidate basis coefficient point)) := by
  exact fun point ↦ cauchySafeMatterGalerkinSynthesis_differentiableAt
    (fixedP506L0CauchySafeMatterWeakSpatialBasisLift basis)
    (fun mode ↦
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift_contDiff_one basis
        basisRegular mode).differentiable (by norm_num)) coefficient point

theorem fixedP506L0CauchySafeMatterWeakActionResponse_add
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (time : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    fixedP506L0CauchySafeMatterWeakActionResponse basis time (first + second) =
      fixedP506L0CauchySafeMatterWeakActionResponse basis time first +
        fixedP506L0CauchySafeMatterWeakActionResponse basis time second := by
  funext space
  unfold fixedP506L0CauchySafeMatterWeakActionResponse
  rw [show fixedP506L0CauchySafeMatterWeakSpatialCandidate basis
      (first + second) =
      fixedP506L0CauchySafeMatterWeakSpatialCandidate basis first +
        fixedP506L0CauchySafeMatterWeakSpatialCandidate basis second by
    unfold fixedP506L0CauchySafeMatterWeakSpatialCandidate
    exact cauchySafeMatterGalerkinSynthesis_add _ first second]
  simpa only [Pi.add_apply] using
    cauchySafeMatterVolterraVelocity_add Input _ _ _
      (fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
        basisRegular first _)
      (fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
        basisRegular second _)

theorem fixedP506L0CauchySafeMatterWeakActionResponse_real_smul
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (time : ℝ)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    fixedP506L0CauchySafeMatterWeakActionResponse basis time
        (parameter • coefficient) =
      parameter • fixedP506L0CauchySafeMatterWeakActionResponse basis time
        coefficient := by
  funext space
  unfold fixedP506L0CauchySafeMatterWeakActionResponse
  rw [show fixedP506L0CauchySafeMatterWeakSpatialCandidate basis
      (parameter • coefficient) =
      parameter • fixedP506L0CauchySafeMatterWeakSpatialCandidate basis
        coefficient by
    unfold fixedP506L0CauchySafeMatterWeakSpatialCandidate
    exact cauchySafeMatterGalerkinSynthesis_real_smul _ parameter coefficient]
  simpa only [Pi.smul_apply] using
    cauchySafeMatterVolterraVelocity_real_smul Input _ parameter _
      (fixedP506L0CauchySafeMatterWeakSpatialCandidate_differentiable basis
        basisRegular coefficient _)

theorem fixedP506L0CauchySafeMatterWeakActionResponse_joint_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakActionResponse basis input.1 coefficient
        input.2 := by
  have full :=
    (fixedP506L0CauchySafeMatterGalerkinInputActual_volterraVelocity_contDiff_zero
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift basis)
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift_contDiff_one basis
        basisRegular) coefficient).continuous
  exact full.comp
    diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous

theorem fixedP506L0CauchySafeMatterWeakActionResponse_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    Continuous
      (fixedP506L0CauchySafeMatterWeakActionResponse basis time coefficient) := by
  unfold fixedP506L0CauchySafeMatterWeakActionResponse
  have full :=
    (fixedP506L0CauchySafeMatterGalerkinInputActual_volterraVelocity_contDiff_zero
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift basis)
      (fixedP506L0CauchySafeMatterWeakSpatialBasisLift_contDiff_one basis
        basisRegular) coefficient).continuous
  exact full.comp
    (diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id))

def fixedP506L0CauchySafeMatterWeakStiffnessForm
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    ℝ → DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      (DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ) :=
  fun time ↦
    diracMatterWeakStiffnessForm
      (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
      (fixedP506L0CauchySafeMatterWeakActionResponse basis time)
      (diracMatterWeakMassMatrix_spatial_continuous
        fixedP506L0CauchySafeMatterWeakMassMatrix
        fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time)
      (fun mode ↦ (basisRegular mode).continuous)
      basisCompact
      (fixedP506L0CauchySafeMatterWeakActionResponse_continuous basis
        basisRegular time)
      (fixedP506L0CauchySafeMatterWeakActionResponse_add basis basisRegular time)
      (fixedP506L0CauchySafeMatterWeakActionResponse_real_smul basis
        basisRegular time)

theorem fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    Continuous
      (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular
        basisCompact) := by
  unfold fixedP506L0CauchySafeMatterWeakStiffnessForm
  exact diracMatterWeakStiffnessForm_time_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    (fixedP506L0CauchySafeMatterWeakActionResponse basis)
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    (fun mode ↦ (basisRegular mode).continuous) basisCompact
    (fixedP506L0CauchySafeMatterWeakActionResponse_joint_continuous basis
      basisRegular)
    (fixedP506L0CauchySafeMatterWeakActionResponse_add basis basisRegular)
    (fixedP506L0CauchySafeMatterWeakActionResponse_real_smul basis basisRegular)

def fixedP506L0CauchySafeMatterWeakStiffnessOperator
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    ℝ → DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      DiracMatterGalerkinCoefficient modeCount :=
  diracMatterWeakStiffnessOperator
    (fixedP506L0CauchySafeMatterWeakStiffnessForm basis basisRegular basisCompact)

theorem fixedP506L0CauchySafeMatterWeakStiffnessOperator_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    Continuous
      (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis basisRegular
        basisCompact) :=
  diracMatterWeakStiffnessOperator_continuous _
    (fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous basis basisRegular
      basisCompact)

theorem fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ)
    (trial test : DiracMatterGalerkinCoefficient modeCount) :
    inner ℝ
        (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis basisRegular
          basisCompact time trial) test =
      diracMatterWeakStiffnessFormValue
        (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
        (fixedP506L0CauchySafeMatterWeakActionResponse basis time) test trial := by
  unfold fixedP506L0CauchySafeMatterWeakStiffnessOperator
  rw [real_inner_diracMatterWeakStiffnessOperator]
  rfl

/-- The fixed mother action now supplies both finite weak legs; no arbitrary
stiffness operator remains in the existence mouth. -/
theorem exists_fixedP506L0CauchySafeMatterActionOwnedWeakGalerkinCoefficientCurve
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (initial : DiracMatterGalerkinCoefficient modeCount)
    (initialTime : ℝ) :
    ∃ bound : ℝ≥0,
      ∃ coefficient : ℝ → DiracMatterGalerkinCoefficient modeCount,
        coefficient initialTime = initial ∧
          ((∀ time ∈
              Set.Icc
                (initialTime - galerkinLinearLocalTimeRadius bound initial)
                (initialTime + galerkinLinearLocalTimeRadius bound initial),
              ‖galerkinWeakActionOperator
                  (galerkinWeakMassOperator
                    (fixedP506L0CauchySafeMatterWeakMassForm basis
                      (fun mode ↦ (basisRegular mode).continuous) basisCompact))
                  (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis
                    basisRegular basisCompact) time‖₊ ≤ bound) ∧
            ((∀ time ∈
                Set.Icc
                  (initialTime - galerkinLinearLocalTimeRadius bound initial)
                  (initialTime + galerkinLinearLocalTimeRadius bound initial),
                HasDerivWithinAt coefficient
                  (galerkinWeakActionOperator
                    (galerkinWeakMassOperator
                      (fixedP506L0CauchySafeMatterWeakMassForm basis
                        (fun mode ↦ (basisRegular mode).continuous) basisCompact))
                    (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis
                      basisRegular basisCompact) time (coefficient time))
                  (Set.Icc
                    (initialTime - galerkinLinearLocalTimeRadius bound initial)
                    (initialTime + galerkinLinearLocalTimeRadius bound initial))
                  time ∧
                galerkinWeakMassOperator
                      (fixedP506L0CauchySafeMatterWeakMassForm basis
                        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
                      time
                      (galerkinWeakActionOperator
                        (galerkinWeakMassOperator
                          (fixedP506L0CauchySafeMatterWeakMassForm basis
                            (fun mode ↦ (basisRegular mode).continuous)
                            basisCompact))
                        (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis
                          basisRegular basisCompact) time (coefficient time)) +
                    fixedP506L0CauchySafeMatterWeakStiffnessOperator basis
                      basisRegular basisCompact time (coefficient time) = 0) ∧
              ∀ time ∈
                Set.Icc initialTime
                  (initialTime + galerkinLinearLocalTimeRadius bound initial),
                ‖coefficient time‖ ≤
                  ‖initial‖ * Real.exp ((bound : ℝ) * (time - initialTime)))) := by
  exact exists_fixedP506L0CauchySafeMatterWeakGalerkinCoefficientCurve
    basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    synthesisFaithful
    (fixedP506L0CauchySafeMatterWeakStiffnessOperator basis basisRegular
      basisCompact)
    (fixedP506L0CauchySafeMatterWeakStiffnessOperator_continuous basis
      basisRegular basisCompact)
    initial initialTime

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
