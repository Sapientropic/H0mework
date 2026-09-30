import H0mework.Physics.DiracEvolution.SafeVolterraOperator
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterVolterraLocalRegularity

open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance localP286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance localP286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance localP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

theorem cauchySafeMatterVolterraVelocity_contDiffAt_of_local
    {order : ℕ}
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ order current.coframe point)
    (connectionRegular : ∀ direction internalOut internalIn,
      ContDiffAt ℝ order (fun target ↦
        current.gravityConnection target direction internalOut internalIn)
        point)
    (scalarRegular : ContDiffAt ℝ order current.scalar point)
    (candidateRegular : ContDiffAt ℝ (order + 1)
      (fun target ↦ matterCoordinateEquiv (candidate target)) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ order (fun target ↦
        p286CoordinateEquiv (current.gaugeConnection target direction)) point) :
    ContDiffAt ℝ order
      (cauchySafeMatterVolterraVelocity current candidate) point := by
  let actual := cauchySafeMatterCandidateActual current candidate
  have candidateContinuous : ContDiffAt ℝ order
      (fun target ↦ matterCoordinateEquiv (candidate target)) point :=
    candidateRegular.of_le (by exact_mod_cast Nat.le_succ order)
  have derivativeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ order (fun target ↦
        fieldDirectionalDerivative
          (fun position ↦ matterCoordinateEquiv (candidate position))
          target direction) point := by
    intro direction
    unfold fieldDirectionalDerivative
    exact candidateRegular.fderiv_right_succ.clm_apply
      contDiffAt_const
  have spinMatrixRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ order (fun target ↦
        diracSpinConnectionLift
          (current.gravityConnection target) direction) point := by
    intro direction
    apply contDiffAt_pi'
    intro row
    apply contDiffAt_pi'
    intro column
    unfold diracSpinConnectionLift loweredLorentzConnectionCoefficient
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply ContDiffAt.sum
    intro pair _
    have realRegular : ContDiffAt ℝ order (fun target ↦
        minkowskiInternalSign (lorentzBivectorFirst pair) *
          current.gravityConnection target direction
            (lorentzBivectorFirst pair) (lorentzBivectorSecond pair)) point :=
      contDiffAt_const.mul
        (connectionRegular direction (lorentzBivectorFirst pair)
          (lorentzBivectorSecond pair))
    have complexRegular : ContDiffAt ℝ order (fun target ↦
        ((minkowskiInternalSign (lorentzBivectorFirst pair) *
          current.gravityConnection target direction
            (lorentzBivectorFirst pair)
            (lorentzBivectorSecond pair) : ℝ) : ℂ)) point :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp point realRegular
    exact (contDiffAt_const.mul complexRegular).mul contDiffAt_const
  have matterCovariantRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
        (holonomicMatterCovariantDerivative actual target direction)) point := by
    intro direction
    have spinActionRegular : ContDiffAt ℝ order (fun target ↦
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (current.gravityConnection target) direction)
            (candidate target))) point := by
      have composed :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.contDiffAt.comp point (spinMatrixRegular direction)).clm_apply
            candidateContinuous
      change ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (current.gravityConnection target) direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (candidate target))))) point at composed
      simpa only [matterCoordinateEquiv.symm_apply_apply] using composed
    have gaugeActionRegular : ContDiffAt ℝ order (fun target ↦
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed (current.gaugeConnection target direction))
            (candidate target))) point := by
      have composed :=
        (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.contDiff
          |>.contDiffAt.comp point (gaugeRegular direction)).clm_apply
            candidateContinuous
      change ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
        (diracExteriorMotherLieAction
          (p286LieBlockEmbed
            (p286CoordinateEquiv.symm
              (p286CoordinateEquiv
                (current.gaugeConnection target direction))))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (candidate target))))) point at composed
      simpa only [p286CoordinateEquiv.symm_apply_apply,
        matterCoordinateEquiv.symm_apply_apply] using composed
    unfold holonomicMatterCovariantDerivative actual
      cauchySafeMatterCandidateActual
    simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
    exact (derivativeRegular direction).add spinActionRegular
      |>.add gaugeActionRegular
  have inverseGammaRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ order (fun target ↦
        inverseCoframeDiracGamma
          { coframe := current.coframe target, derivative := 0 } direction)
        point := by
    intro direction
    exact ((inverseCoframeDiracGamma_contDiffAt
      (current.coframe point) nondegenerate direction).of_le
        (show (order : WithTop ℕ∞) ≤ ∞ from mod_cast le_top)).comp
          point coframeRegular
  have kineticDirectionRegular : ∀ direction : Fin 3,
      ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := current.coframe target, derivative := 0 }
            direction.succ)
          (holonomicMatterCovariantDerivative actual target
            direction.succ))) point := by
    intro direction
    have composed :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point (inverseGammaRegular direction.succ)).clm_apply
          (matterCovariantRegular direction.succ)
    change ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
      (diracMatrixMatterAction
        (inverseCoframeDiracGamma
          { coframe := current.coframe target, derivative := 0 }
          direction.succ)
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv
            (holonomicMatterCovariantDerivative actual target
              direction.succ))))) point at composed
    simpa only [matterCoordinateEquiv.symm_apply_apply] using composed
  have kineticRegular : ContDiffAt ℝ order (fun target ↦
      Complex.I • ∑ direction : Fin 3, matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := current.coframe target, derivative := 0 }
            direction.succ)
          (holonomicMatterCovariantDerivative actual target
            direction.succ))) point := by
    exact (contDiffAt_const : ContDiffAt ℝ order
      (fun _ : BasePoint ↦ (Complex.I : ℂ)) point).smul
        (ContDiffAt.sum fun direction _ ↦
          kineticDirectionRegular direction)
  have yukawaRegular : ContDiffAt ℝ order (fun target ↦
      matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (current.scalar target))
          (candidate target))) point := by
    have composed :=
      (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp point scalarRegular).clm_apply candidateContinuous
    change ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
      (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (current.scalar target))
        (matterCoordinateEquiv.symm
          (matterCoordinateEquiv (candidate target))))) point at composed
    simpa only [matterCoordinateEquiv.symm_apply_apply] using composed
  have knownRegular : ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
      (holonomicDiracDualCurrentCoframeMatterKnownVector actual target))
      point := by
    unfold holonomicDiracDualCurrentCoframeMatterKnownVector actual
      cauchySafeMatterCandidateActual
    simp only [map_add, map_smul, map_sum]
    exact kineticRegular.add yukawaRegular
  have qRealRegular : ContDiffAt ℝ order (fun target ↦
      coframeTemporalPrincipalScalar (current.coframe target)) point := by
    have inverseRegular : ContDiffAt ℝ order
        (fun target ↦ (current.coframe target)⁻¹) point :=
      ((coframe_inv_contDiffAt (current.coframe point) nondegenerate).of_le
        (show (order : WithTop ℕ∞) ≤ ∞ from mod_cast le_top)).comp
          point coframeRegular
    unfold coframeTemporalPrincipalScalar
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro internal _
    exact contDiffAt_const.mul
      ((contDiffAt_pi.mp
        (contDiffAt_pi.mp inverseRegular (0 : LorentzianIndex)) internal).pow 2)
  have qInverseRegular : ContDiffAt ℝ order (fun target ↦
      (((coframeTemporalPrincipalScalar
        (current.coframe target) : ℝ) : ℂ)⁻¹)) point := by
    have complexRegular : ContDiffAt ℝ order (fun target ↦
        ((coframeTemporalPrincipalScalar
          (current.coframe target) : ℝ) : ℂ)) point :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp point qRealRegular
    exact complexRegular.inv (by exact_mod_cast noncharacteristic)
  have generatedTimeRegular : ContDiffAt ℝ order (fun target ↦
      matterCoordinateEquiv
        (actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
          actual target)) point := by
    have gammaKnownRegular : ContDiffAt ℝ order (fun target ↦
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := current.coframe target, derivative := 0 } 0)
            (holonomicDiracDualCurrentCoframeMatterKnownVector
              actual target))) point := by
      have composed :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.contDiffAt.comp point (inverseGammaRegular 0)).clm_apply
            knownRegular
      change ContDiffAt ℝ order (fun target ↦ matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := current.coframe target, derivative := 0 } 0)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicDiracDualCurrentCoframeMatterKnownVector
                actual target))))) point at composed
      simpa only [matterCoordinateEquiv.symm_apply_apply] using composed
    unfold
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
      actionGeneratedCurrentCoframeMatterTemporalDerivative
      currentCoframeMatterTemporalPrincipalInverse
      currentCoframeMatterTemporalPrincipal actual
      cauchySafeMatterCandidateActual
    simp only [LinearMap.smul_apply, map_neg, map_smul]
    exact (qInverseRegular.smul
      ((contDiffAt_const : ContDiffAt ℝ order
        (fun _ : BasePoint ↦ (Complex.I : ℂ)) point).smul
          gammaKnownRegular)).neg
  have connectionActionRegular : ContDiffAt ℝ order (fun target ↦
      matterCoordinateEquiv
        (holonomicMatterConnectionAction actual target
          canonicalLorentzianTimeDirection)) point := by
    rw [show (fun target ↦ matterCoordinateEquiv
      (holonomicMatterConnectionAction actual target
        canonicalLorentzianTimeDirection)) =
      fun target ↦ matterCoordinateEquiv
          (holonomicMatterCovariantDerivative actual target
            canonicalLorentzianTimeDirection) -
        fieldDirectionalDerivative
          (fun position ↦ matterCoordinateEquiv (candidate position))
          target canonicalLorentzianTimeDirection by
      funext target
      unfold holonomicMatterConnectionAction holonomicMatterCovariantDerivative
        actual cauchySafeMatterCandidateActual
      simp only [map_add, matterCoordinateEquiv.apply_symm_apply]
      module]
    exact (matterCovariantRegular canonicalLorentzianTimeDirection).sub
      (derivativeRegular canonicalLorentzianTimeDirection)
  unfold cauchySafeMatterVolterraVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
  simp only [map_sub]
  exact generatedTimeRegular.sub connectionActionRegular

/-- Backward-compatible continuity specialization of the order-polymorphic
local regularity theorem. -/
theorem cauchySafeMatterVolterraVelocity_contDiffAt_zero_of_local
    (current : StageNineHolonomicConfiguration)
    (candidate : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe point) ≠ 0)
    (coframeRegular : ContDiffAt ℝ 0 current.coframe point)
    (connectionRegular : ∀ direction internalOut internalIn,
      ContDiffAt ℝ 0 (fun target ↦
        current.gravityConnection target direction internalOut internalIn)
        point)
    (scalarRegular : ContDiffAt ℝ 0 current.scalar point)
    (candidateRegular : ContDiffAt ℝ 1
      (fun target ↦ matterCoordinateEquiv (candidate target)) point)
    (gaugeRegular : ∀ direction : LorentzianIndex,
      ContDiffAt ℝ 0 (fun target ↦
        p286CoordinateEquiv (current.gaugeConnection target direction)) point) :
    ContDiffAt ℝ 0
      (cauchySafeMatterVolterraVelocity current candidate) point :=
  cauchySafeMatterVolterraVelocity_contDiffAt_of_local
    current candidate point nondegenerate noncharacteristic coframeRegular
    connectionRegular scalarRegular candidateRegular gaugeRegular

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterVolterraLocalRegularity
