import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualOriginRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSlowCoupling
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumCausalPoleResponse
open PreparationVacuumQuantumSlowResidue PreparationVacuumOriginalGreenFeedback
open PreparationVacuumNativePoleTensor
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceNativeReader fullNativeOrigin

/-- The common slow parameter uses the original time and spatial Fourier coordinates. -/
theorem sourcePhysicalRay_generated (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) :
    fixedMomentum (d • n) ((d:ℂ)*zeta)=(d:ℂ) • fixedMomentum n zeta := by
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · rfl
  · change Complex.I*((d*n j : ℝ):ℂ)=(d:ℂ)*(Complex.I*(n j:ℂ))
    push_cast
    ring

private theorem real_positive_complex_punctured :
    Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with d hd
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,Complex.ofReal_eq_zero] using ne_of_gt hd

theorem sourcePhysicalReader_slope (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>(d:ℂ)⁻¹ •
      (sourceNativeReader (fixedMomentum (d • n) ((d:ℂ)*zeta))-fullNativeOrigin.transpose))
      (𝓝[>] 0) (𝓝 (sourceNativeReaderFirst (fixedMomentum n zeta))) := by
  simpa only [Function.comp_def,sourcePhysicalRay_generated] using
    (sourceNativeReader_slope (fixedMomentum n zeta)).comp real_positive_complex_punctured

private theorem reader_split (L L0 : Matrix (Fin 289) (Fin 289) ℂ) (J : Fin 289→ℂ)
    (z : ℂ) (nonzero : z≠0) :
    z • (L*ᵥJ)=L0*ᵥ(z • J)+(z⁻¹ • (L-L0))*ᵥ(z^2 • J) := by
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.mulVec_smul,Matrix.sub_mulVec]
  rw [smul_smul]
  have scalar : z⁻¹*z^2=z := by field_simp
  rw [scalar,smul_sub]
  module

/-- The full native effective forcing uses exactly the same original current and field source reader. -/
def sourceActualNativeForcing (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) : Fin 289→ℂ :=
  rawEffectiveReader (fixedMomentum (d • n) ((d:ℂ)*zeta))*ᵥ
    activeForcing (fixedMomentum (d • n) ((d:ℂ)*zeta))
      (returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))

theorem sourceActualNativeForcing_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) :
    sourceActualNativeForcing q n zeta l r d=
      sourceNativeReader (fixedMomentum (d • n) ((d:ℂ)*zeta))*ᵥ
        returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta) := by
  simp only [sourceActualNativeForcing,sourceNativeReader,activeForcing,Matrix.mulVec_mulVec,mul_assoc]

/-- The moving source reader couples its first jet to the complete second-order current residue. -/
def sourceActualNativeResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceOriginCurrentResidue q n zeta l r+
    sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥsourceFullCurrentResidue q n zeta l r

theorem sourceActualNative_split (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) (nonzero : d≠0) :
    (d:ℂ) • sourceActualNativeForcing q n zeta l r d=
      fullNativeOrigin.transpose*ᵥ((d:ℂ) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))+
      ((d:ℂ)⁻¹ • (sourceNativeReader (fixedMomentum (d • n) ((d:ℂ)*zeta))-fullNativeOrigin.transpose))*ᵥ
        (((d:ℂ)^2) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta)) := by
  rw [sourceActualNativeForcing_generated]
  exact reader_split _ _ _ _ (Complex.ofReal_ne_zero.mpr nonzero)

/-- Full source-generated coupling: no bounded first-order nongauge current is assumed. -/
theorem sourceActualNative_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceActualNativeForcing q n zeta l r d)
      (𝓝[>] 0) (𝓝 (sourceActualNativeResidue q n zeta l r)) := by
  have origin:=sourceActualOrigin_residue q n zeta positive l r nonrealL nonrealR
  have slope:=sourcePhysicalReader_slope n zeta
  have current:=sourceFullCurrent_residue q n zeta positive l r nonrealL nonrealR
  have product:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (slope.prodMk_nhds current)
  have result:=origin.add product
  apply result.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (sourceActualNative_split q n zeta l r d (ne_of_gt hd)).symm

private theorem matrix_slope_price (L L0 L1 : Matrix (Fin 289) (Fin 289) ℂ)
    (z : ℂ) (nonzero : z≠0) (C : ℝ) (bound : ‖L-L0-z • L1‖≤C*‖z‖^2) :
    ‖z⁻¹ • (L-L0)-L1‖≤C*‖z‖ := by
  have identity : z⁻¹ • (L-L0)-L1=z⁻¹ • (L-L0-z • L1) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  rw [identity,norm_smul,norm_inv]
  calc
    _≤‖z‖⁻¹*(C*‖z‖^2) := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg z))
    _=C*‖z‖ := by have nz:=norm_ne_zero_iff.mpr nonzero;field_simp

/-- The full nongauge contribution has the source Taylor price against the actual second-order current. -/
theorem sourceActualNative_error (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) (nonzero : d≠0)
    (small : abs d ≤ sourceReaderRadius (fixedMomentum n zeta)) :
    ‖(d:ℂ) • sourceActualNativeForcing q n zeta l r d-
      fullNativeOrigin.transpose*ᵥ((d:ℂ) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))-
      sourceNativeReaderFirst (fixedMomentum n zeta)*ᵥ
        (((d:ℂ)^2) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))‖≤
      sourceReaderErrorBudget (fixedMomentum n zeta)*abs d*
        ‖((d:ℂ)^2) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta)‖ := by
  have bound:=sourceNativeReader_error (d:ℂ) (fixedMomentum n zeta)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using small)
  rw [←sourcePhysicalRay_generated] at bound
  have slope:=matrix_slope_price _ _ _ (d:ℂ) (Complex.ofReal_ne_zero.mpr nonzero) _ bound
  rw [sourceActualNative_split q n zeta l r d nonzero,add_sub_cancel_left,←Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using slope) (norm_nonneg _))

end LowEnergy.PreparationVacuumNativeSlowCoupling
