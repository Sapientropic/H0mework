import H0mework.Physics.DiracEvolution.WeakGalerkinEnergy
import H0mework.Physics.DiracEvolution.SafeGalerkinEvolution
import H0mework.Physics.SafeCauchy.FixedGlobalRegularity

/-!
# Fixed P506/L0 Cauchy-safe weak spatial Galerkin mass

The exact post-EC action actual supplies its coordinate-time Dirac principal
on every spatial slice. Compactly supported finite synthesis integrates that
principal into a continuous strictly positive weak mass form, whose Riesz
operator then generates the finite weak evolution for every continuous
stiffness leg.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalRegularity
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise NNReal

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

private abbrev Input : StageNineHolonomicConfiguration :=
  fixedP506L0CauchySafeMatterGalerkinInputActual

private abbrev Safe : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

theorem fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe :
    Input.coframe =
      fixedP506L0CartanECConstraintCauchySafeGlobalActual.coframe := by
  change fixedP506L0CauchySafeMatterGalerkinInputActual.coframe = _
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_eq_actionWrite,
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
  rfl

def fixedP506L0CauchySafeMatterWeakMassMatrix
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : DiracMatrix :=
  coframeCoordinateDiracEvolutionPrincipal
    (Input.coframe (diracMatterSpacetimeCoordinatePoint time space)) 0

theorem fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    Matrix.PosDef (fixedP506L0CauchySafeMatterWeakMassMatrix time space) := by
  unfold fixedP506L0CauchySafeMatterWeakMassMatrix Input
  rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]
  exact
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_coordinateTimeEvolutionPrincipal_posDef
      (diracMatterSpacetimeCoordinatePoint time space)

private theorem safeCoframe_contDiff : ContDiff ℝ ∞ Safe.coframe :=
  holonomicCoframe_contDiff Safe
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_smooth

theorem fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff
    (row column : DiracSpinorIndex) :
    ContDiff ℝ ∞ fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix input.1 input.2 row column := by
  rw [contDiff_iff_contDiffAt]
  intro input
  let point := diracMatterSpacetimeCoordinatePoint input.1 input.2
  have coframePathContDiff : ContDiff ℝ ∞
      (fun candidate : ℝ × DiracMatterSpatialCoordinates ↦
        Safe.coframe
          (diracMatterSpacetimeCoordinatePoint candidate.1 candidate.2)) :=
    safeCoframe_contDiff.comp diracMatterSpacetimeCoordinatePoint_joint_contDiff
  have gammaPathContDiffAt : ContDiffAt ℝ ∞
      (fun candidate : ℝ × DiracMatterSpatialCoordinates ↦
        inverseCoframeDiracGamma
          { coframe := Safe.coframe
              (diracMatterSpacetimeCoordinatePoint candidate.1 candidate.2),
            derivative := 0 }
          0) input := by
    have outer := inverseCoframeDiracGamma_contDiffAt (Safe.coframe point)
      (fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate point)
      0
    change ContDiffAt ℝ ∞
      ((fun coframe : LorentzianCoframe ↦
          inverseCoframeDiracGamma { coframe := coframe, derivative := 0 } 0) ∘
        (fun candidate : ℝ × DiracMatterSpatialCoordinates ↦
          Safe.coframe
            (diracMatterSpacetimeCoordinatePoint candidate.1 candidate.2))) input
    exact outer.comp input coframePathContDiff.contDiffAt
  have principalEntryContDiffAt : ContDiffAt ℝ ∞
      (fun candidate : ℝ × DiracMatterSpatialCoordinates ↦
        coframeCoordinateDiracEvolutionPrincipal
          (Safe.coframe
            (diracMatterSpacetimeCoordinatePoint candidate.1 candidate.2))
          0 row column) input := by
    unfold coframeCoordinateDiracEvolutionPrincipal
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro middle _
    apply contDiffAt_const.mul
    apply contDiffAt_const.mul
    exact contDiffAt_pi.mp (contDiffAt_pi.mp gammaPathContDiffAt middle) column
  rw [show (fun candidate : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix candidate.1 candidate.2 row column) =
      (fun candidate ↦
        coframeCoordinateDiracEvolutionPrincipal
          (Safe.coframe
            (diracMatterSpacetimeCoordinatePoint candidate.1 candidate.2))
          0 row column) by
    funext candidate
    unfold fixedP506L0CauchySafeMatterWeakMassMatrix Input Safe
    rw [fixedP506L0CauchySafeMatterGalerkinInputActual_coframe_eq_cauchySafe]]
  exact principalEntryContDiffAt

theorem fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    (row column : DiracSpinorIndex) :
    Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterWeakMassMatrix input.1 input.2 row column :=
  (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column).continuous

def fixedP506L0CauchySafeMatterWeakMassForm
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    ℝ → DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      (DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ) :=
  fun time ↦
    diracMatterWeakMassForm
      (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
      (diracMatterWeakMassMatrix_spatial_continuous
        fixedP506L0CauchySafeMatterWeakMassMatrix
        fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time)
      basisContinuous basisCompact

theorem fixedP506L0CauchySafeMatterWeakMassForm_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    Continuous
      (fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous
        basisCompact) := by
  exact diracMatterWeakMassForm_time_continuous
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    basisContinuous basisCompact

theorem fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    ContDiff ℝ 1
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact) := by
  exact diracMatterWeakMassForm_time_contDiff_one
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    (fun row column ↦
      (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column).of_le
        (by norm_num))
    basisRegular basisCompact

def fixedP506L0CauchySafeMatterWeakMassFormDerivative
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ) :
    DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      (DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ) :=
  deriv
    (fixedP506L0CauchySafeMatterWeakMassForm basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact)
    time

theorem fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ) :
    HasDerivAt
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
        basisCompact time)
      time := by
  exact
    (fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one basis basisRegular
      basisCompact).differentiable one_ne_zero time |>.hasDerivAt

/-- Applying the generated mass-form derivative reads the spatial integral of
the mother-action time-principal derivative. -/
theorem fixedP506L0CauchySafeMatterWeakMassFormDerivative_apply
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    fixedP506L0CauchySafeMatterWeakMassFormDerivative basis basisRegular
        basisCompact time first second =
      diracMatterWeakMassFormValueTimeDerivative
        fixedP506L0CauchySafeMatterWeakMassMatrix basis first second time := by
  have formDerivative :=
    fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt basis basisRegular
      basisCompact time
  have firstConstant : HasDerivAt
      (fun _ : ℝ ↦ first) 0 time := hasDerivAt_const time first
  have secondConstant : HasDerivAt
      (fun _ : ℝ ↦ second) 0 time := hasDerivAt_const time second
  have appliedDerivative :=
    (formDerivative.clm_apply firstConstant).clm_apply secondConstant
  have integralDerivative :=
    diracMatterWeakMassFormValue_time_hasDerivAt
      fixedP506L0CauchySafeMatterWeakMassMatrix basis
      (fun row column ↦
        (fixedP506L0CauchySafeMatterWeakMassMatrix_joint_contDiff row column).of_le
          (by norm_num))
      basisRegular basisCompact first second time
  simpa using appliedDerivative.unique integralDerivative

theorem fixedP506L0CauchySafeMatterWeakMassForm_symm
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous basisCompact
        time first second =
      fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous basisCompact
        time second first := by
  unfold fixedP506L0CauchySafeMatterWeakMassForm
  exact diracMatterWeakMassFormValue_symm
    (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
    (fun space =>
      (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef time space).isHermitian)
    first second

theorem fixedP506L0CauchySafeMatterWeakMassForm_nonnegative
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    0 ≤ fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous
      basisCompact time coefficient coefficient := by
  exact diracMatterWeakMassForm_nonnegative
    (fixedP506L0CauchySafeMatterWeakMassMatrix time) basis
    (diracMatterWeakMassMatrix_spatial_continuous
      fixedP506L0CauchySafeMatterWeakMassMatrix
      fixedP506L0CauchySafeMatterWeakMassMatrix_continuous time)
    basisContinuous basisCompact
    (fun space ↦
      (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef time space).posSemidef)
    coefficient

theorem fixedP506L0CauchySafeMatterWeakMassForm_positive
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (coefficientNonzero : coefficient ≠ 0) :
    0 < fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous
      basisCompact time coefficient coefficient := by
  exact diracMatterWeakMassForm_time_positive
    fixedP506L0CauchySafeMatterWeakMassMatrix basis
    fixedP506L0CauchySafeMatterWeakMassMatrix_continuous
    basisContinuous basisCompact
    fixedP506L0CauchySafeMatterWeakMassMatrix_posDef synthesisFaithful
    time coefficient coefficientNonzero

theorem fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (time : ℝ) :
    (galerkinWeakMassOperator
      (fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous basisCompact)
      time).IsInvertible := by
  exact galerkinWeakMassOperator_isInvertible _ time
    (fixedP506L0CauchySafeMatterWeakMassForm_positive basis basisContinuous
      basisCompact synthesisFaithful time)

theorem exists_fixedP506L0CauchySafeMatterWeakGalerkinCoefficientCurve
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (stiffness : ℝ → DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      DiracMatterGalerkinCoefficient modeCount)
    (stiffnessContinuous : Continuous stiffness)
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
                      basisContinuous basisCompact))
                  stiffness time‖₊ ≤ bound) ∧
            ((∀ time ∈
                Set.Icc
                  (initialTime - galerkinLinearLocalTimeRadius bound initial)
                  (initialTime + galerkinLinearLocalTimeRadius bound initial),
                HasDerivWithinAt coefficient
                  (galerkinWeakActionOperator
                    (galerkinWeakMassOperator
                      (fixedP506L0CauchySafeMatterWeakMassForm basis
                        basisContinuous basisCompact))
                    stiffness time (coefficient time))
                  (Set.Icc
                    (initialTime - galerkinLinearLocalTimeRadius bound initial)
                    (initialTime + galerkinLinearLocalTimeRadius bound initial))
                  time ∧
                galerkinWeakMassOperator
                      (fixedP506L0CauchySafeMatterWeakMassForm basis
                        basisContinuous basisCompact) time
                      (galerkinWeakActionOperator
                        (galerkinWeakMassOperator
                          (fixedP506L0CauchySafeMatterWeakMassForm basis
                            basisContinuous basisCompact))
                        stiffness time (coefficient time)) +
                    stiffness time (coefficient time) = 0) ∧
              ∀ time ∈
                Set.Icc initialTime
                  (initialTime + galerkinLinearLocalTimeRadius bound initial),
                ‖coefficient time‖ ≤
                  ‖initial‖ * Real.exp ((bound : ℝ) * (time - initialTime)))) := by
  exact exists_galerkinWeakCoefficientCurve_of_positiveMassForm
    (fixedP506L0CauchySafeMatterWeakMassForm basis basisContinuous basisCompact)
    stiffness
    (fixedP506L0CauchySafeMatterWeakMassForm_continuous basis basisContinuous
      basisCompact)
    stiffnessContinuous
    (fixedP506L0CauchySafeMatterWeakMassForm_positive basis basisContinuous
      basisCompact synthesisFaithful)
    initial initialTime

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
