import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInfrared

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumWholeOrigin PreparationVacuumFullSlowFieldResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumSoftPoleSelection
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalCurvatureSheetLimit
open CanonicalGradedSpatialSource Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourcePhotonLeftReader sourceCurvatureEmitterInput
  sourceWholePhotonFrequencyResidue sourceNativeFrequencyPolarization

private def movingPoleLeft (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289 → ℂ) →ₗ[ℂ] ℂ where
  toFun f := sourcePhotonLeftReader branch epsilon s n f
  map_add' f g := by
    unfold sourcePhotonLeftReader sourceNativePoleCoefficient
    rw [show nativeModeForcing epsilon s n (f+g) =
      nativeModeForcing epsilon s n f + nativeModeForcing epsilon s n g from
        (emModeReadLinear epsilon s n).map_add f g]
    simp only [Matrix.mulVec_add,Pi.add_apply,add_div]
  map_smul' c f := by
    unfold sourcePhotonLeftReader sourceNativePoleCoefficient
    rw [show nativeModeForcing epsilon s n (c • f) = c • nativeModeForcing epsilon s n f from
      (emModeReadLinear epsilon s n).map_smul c f]
    simp only [Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

private def movingOriginLeft (branch : Fin 2) : (Fin 289 → ℂ) →ₗ[ℂ] ℂ where
  toFun f := sourceCurvatureEmitterInput f (residueIndex branch)
  map_add' f g := by
    simp only [sourceCurvatureEmitterInput,activeForcing,Matrix.mulVec_add,Pi.add_apply,
      regularScaling,Matrix.mulVec_diagonal,mul_add]
  map_smul' c f := by
    simp only [sourceCurvatureEmitterInput,activeForcing,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,
      regularScaling,Matrix.mulVec_diagonal]
    ring

private theorem moving_read_expansion (L : (Fin 289 → ℂ) →ₗ[ℂ] ℂ) (f : Fin 289 → ℂ) :
    L f = ∑ j : Fin 289, f j * L (Pi.single j 1) := by
  have expansion : f = ∑ j : Fin 289, f j • Pi.single j (1:ℂ) := by
    funext i
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
  conv_lhs => rw [expansion]
  simp only [map_sum,map_smul,smul_eq_mul]

/-- A varying source family pays its own limit; the fixed-force left-reader theorem is not substituted pointwise. -/
theorem em_moving_left_reader_limit (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : scaleDomain → Fin 289 → ℂ) (origin : Fin 289 → ℂ)
    (generated : Tendsto forcing scaleApproach (𝓝 origin)) :
    Tendsto (fun e : scaleDomain => (e.val:ℂ)^2 *
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (forcing e))
      scaleApproach (𝓝 (sourceCurvatureEmitterInput origin (residueIndex branch))) := by
  have entry (j : Fin 289) := (tendsto_pi_nhds.mp generated j).mul
    (sourcePhotonLeftReader_sheet branch n unit (Pi.single j 1))
  have result := tendsto_finsetSum Finset.univ (fun j _ => entry j)
  have limit := moving_read_expansion (movingOriginLeft branch) origin
  change sourceCurvatureEmitterInput origin (residueIndex branch) =
    ∑j : Fin 289,origin j*sourceCurvatureEmitterInput (Pi.single j 1) (residueIndex branch) at limit
  rw [←limit] at result
  apply result.congr'
  filter_upwards [] with e
  have exactRead := moving_read_expansion (movingPoleLeft branch e.val (sourceSheet branch n unit e.val) n) (forcing e)
  change sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (forcing e) =
    ∑j : Fin 289, forcing e j * sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n (Pi.single j 1) at exactRead
  rw [exactRead,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full moving actual current is paired with the paid EM output before its infrared limit. -/
theorem em_moving_current_response_ir (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : scaleDomain → Fin 289 → ℂ) (origin : Fin 289 → ℂ)
    (generated : Tendsto forcing scaleApproach (𝓝 origin)) (mu : Fin 4) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ))*
      (emInsertion.transpose *ᵥ (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ forcing e)) mu)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput origin (residueIndex branch)*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
        (softCoefficient branch:ℂ))) := by
  have left := em_moving_left_reader_limit branch n unit forcing origin generated
  have right := em_right_projection_limit branch n unit mu
  have result := left.mul right
  have scalar (a b c : ℂ) : a*(b*c)=a*b*c := by ring
  rw [scalar] at result
  apply result.congr'
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,factor,smul_comm,
    ←sourceNativeFrequencyPolarization,Matrix.mulVec_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  have ne : (e.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

/-- The unchanged whole frequency residue also has its original frequency-normalized full-field limit for moving sources. -/
theorem em_moving_whole_response_ir (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (forcing : scaleDomain → Fin 289 → ℂ) (origin : Fin 289 → ℂ)
    (generated : Tendsto forcing scaleApproach (𝓝 origin)) :
    Tendsto (fun e : scaleDomain => (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
      (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ forcing e))
      scaleApproach (𝓝 (leadingNativeResponse branch origin)) := by
  have result := softResponse_limit branch n unit forcing origin generated
  apply result.congr'
  filter_upwards [] with e
  rw [sourceWholePhotonFrequencyResidue,Matrix.smul_mulVec,sourceWholePhotonResidue_apply]
  have cast (v : Fin 289 → ℂ) : (e.val^2:ℝ) • v = (e.val:ℂ)^2 • v := by
    funext i
    simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]
  rw [cast]
  exact (native_soft_normalization e.val _ n e.property.1.ne' (forcing e)).symm

end LowEnergy.GaussComposite.ActualEMCarrierOwn
