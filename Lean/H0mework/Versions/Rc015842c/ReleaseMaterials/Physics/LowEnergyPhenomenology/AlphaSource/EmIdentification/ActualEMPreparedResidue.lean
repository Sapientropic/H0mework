import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMResidueTensor
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedDetector

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationVacuumNativePoleTensor
open PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalCommonCurrentStaticRead
open PreparationPhysicalActualPolarizationResponse PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalFinitePoleVertices Electromagnetic.CanonicalCoframe
open PreparationVacuumElectromagneticIdentity PreparationVacuumFullPoleContinuation
open PreparationVacuumPhysicalQuantumLockedCharge
open Filter Set
open scoped Matrix BigOperators Topology

/-- The actual five-mode source reader, before multiplying its pole cofactor. -/
def emModeReadLinear (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun := nativeModeForcing epsilon s n
  map_add' v w := by
    funext i
    simp only [nativeModeForcing, activeForcing, Matrix.mulVec_add, Pi.add_apply]
  map_smul' c v := by
    funext i
    simp only [nativeModeForcing, activeForcing, Matrix.mulVec_smul, Pi.smul_apply]
    rfl

/-- This linear reader exposes all five cofactor rows and cancels their common physical slope. -/
def emCofactorRead (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289 → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ((extendedTensor epsilon s n).adjugate *ᵥ emModeReadLinear epsilon s n f)
    (residueIndex branch) / (extendedTensor epsilon s n).adjugate (residueIndex branch) (residueIndex branch)
  map_add' f g := by
    simp only [map_add,Matrix.mulVec_add,Pi.add_apply,add_div]
  map_smul' c f := by
    simp only [map_smul,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

theorem em_cofactor_read_generated (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach, ∀ f : Fin 289 → ℂ,
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n f =
        emCofactorRead branch e.val (sourceSheet branch n unit e.val) n f := by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit)] with e simple
  intro f
  unfold sourcePhotonLeftReader sourceNativePoleCoefficient sourceResidue
  change _ = ((extendedTensor e.val (sourceSheet branch n unit e.val) n).adjugate *ᵥ
    nativeModeForcing e.val (sourceSheet branch n unit e.val) n f) (residueIndex branch) /
      (extendedTensor e.val (sourceSheet branch n unit e.val) n).adjugate (residueIndex branch) (residueIndex branch)
  simp only [Matrix.smul_mulVec,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr simple.1))

/-- The source coefficient for an actual preparation keeps every eight-by-eight current entry. -/
theorem em_prepared_cofactor_all64 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (branch : Fin 2)
    (epsilon s : ℝ) (n : PhysicalMomentum) :
    emCofactorRead branch epsilon s n (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) =
      ∑a : RestStateIndex, ∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 sL eL sR eR a b *
          emCofactorRead branch epsilon s n (returnedCurrentWindow q pL pR a b lambda T) := by
  simp only [sourceActualPreparedCurrent,map_sum,map_smul,smul_eq_mul]

/-- Both original prepared currents consume the same complete source frequency residue. -/
theorem em_prepared_frequency_factor (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (dSL dEL dSR dER : Fin 2) (lambda : ℂ) (T : ℝ)
    (qs : PhysicalResponsePoint) (pSL pSR : PhysicalMomentum) (sSL sEL sSR sER : Fin 2)
    (mu : ℂ) (S : ℝ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceActualPreparedDetector qd pDL pDR dSL dEL dSR dER lambda T
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S) =
      emCofactorRead branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S) *
      sourceActualPreparedDetector qd pDL pDR dSL dEL dSR dER lambda T
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) := by
  filter_upwards [sourceActualPreparedDetector_frequency qd pDL pDR dSL dEL dSR dER lambda T
    qs pSL pSR sSL sEL sSR sER mu S branch n unit,
    em_cofactor_read_generated branch n unit] with e factor cofactor
  rw [factor,cofactor]

attribute [local irreducible] sourceQuantumChargedRead sourceActualPreparedKernel
  sourceActualPreparedCurrent sourceActualPreparedDetector sourceWholePhotonFrequencyResidue
  sourceNativeFrequencyPolarization emCofactorRead

private theorem em_neg_factor (a b c d v : ℂ)
    (source : d = -a) (mode : v = -b) (factor : d = c*v) : a = c*b := by
  linear_combination -factor + source - c*mode

/-- The computed coefficient is consumed by the unchanged ordinary full kernel on the actual electron/neutral preparations. -/
theorem em_prepared_ordinary_return (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (dSL dEL dSR dER : Fin 2) (lambda : ℂ) (T : ℝ)
    (qs : PhysicalResponsePoint) (pSL pSR : PhysicalMomentum) (sSL sEL sSR sER : Fin 2)
    (mu : ℂ) (S : ℝ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : qd.z.im ≠ 0) (hwd : qd.w.im ≠ 0) :
    ∀ᶠ e in scaleApproach,
      sourceQuantumChargedRead qd dSL dEL dSR dER
        (sourceActualPreparedKernel qd pDL pDR lambda T
          (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
            sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S)) =
      emCofactorRead branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S) *
      sourceQuantumChargedRead qd dSL dEL dSR dER
        (sourceActualPreparedKernel qd pDL pDR lambda T
          (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)) := by
  filter_upwards [em_prepared_frequency_factor qd pDL pDR dSL dEL dSR dER lambda T
    qs pSL pSR sSL sEL sSR sER mu S branch n unit] with e factor
  have sourceReturn := sourceActualPreparedDetector_action qd pDL pDR dSL dEL dSR dER lambda T
    (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
      sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S) hzd hwd
  have modeReturn := sourceActualPreparedDetector_action qd pDL pDR dSL dEL dSR dER lambda T
    (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) hzd hwd
  exact em_neg_factor _ _ _ _ _ sourceReturn modeReturn factor


/-- The same all64 prepared source returns the computed EM four-vector while keeping its complete propagated field. -/
theorem em_prepared_frequency_projection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach, ∀ mu : Fin 4,
      (emInsertion.transpose *ᵥ
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)) mu =
      emCofactorRead branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) *
      emFrequencyProjection branch e.val (sourceSheet branch n unit e.val) n mu := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit,
    em_cofactor_read_generated branch n unit] with e factor cofactor
  intro mu
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,cofactor,smul_comm,
    ←sourceNativeFrequencyPolarization,Matrix.mulVec_smul]
  change _ * (emInsertion.transpose *ᵥ sourceNativeFrequencyPolarization branch e.val _ n) mu = _
  rw [em_frequency_projection_generated branch e.val _ n e.property.1.ne' mu]

end LowEnergy.GaussComposite.ActualEMCarrierOwn
