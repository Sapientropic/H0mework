import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePhotonEmitter

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePolarizationEmitter
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalJointGeneratorEnergyReturn
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace FullQuantum.PerturbedGreen Filter
open scoped InnerProductSpace BigOperators Matrix Topology
attribute [local irreducible] complexCoefficients complexFrequencyCoefficients complexMixedCoefficients
  realReaderCoefficients realMixedCoefficients sourcePreparedScatteringPair sourceActualScatteringRead

private def extendCoefficient (L : Field289→ₗ[ℝ] FiberOperators) (v : Fin 289→ℂ) : FiberOperators :=
  L (fun i=>(v i).re)+Complex.I • L (fun i=>(v i).im)

private theorem extendCoefficient_smul (L : Field289→ₗ[ℝ] FiberOperators) (z : ℂ) (v : Fin 289→ℂ) :
    extendCoefficient L (z • v)=z • extendCoefficient L v := by
  have real : (fun i=>((z • v) i).re)=z.re • (fun i=>(v i).re)-z.im • (fun i=>(v i).im) := by
    funext i
    simp [Complex.mul_re,smul_eq_mul]
  have imaginary : (fun i=>((z • v) i).im)=z.re • (fun i=>(v i).im)+z.im • (fun i=>(v i).re) := by
    funext i
    simp [Complex.mul_im,smul_eq_mul]
  rw [extendCoefficient,real,imaginary,map_sub,map_add,map_smul,map_smul,map_smul,map_smul]
  simp only [extendCoefficient]
  conv_rhs => rw [←Complex.re_add_im z]
  simp only [smul_add,smul_smul,add_smul,add_mul,mul_assoc,Complex.I_mul_I,mul_neg_one]
  module

private theorem density_complex_smul (z : ℂ) (v : Fin 289→ℂ) :
    complexCoefficients (originalComplexDirection (z • v))=z • complexCoefficients (originalComplexDirection v) := by
  funext i
  have source (w : Fin 289→ℂ) : complexCoefficients (originalComplexDirection w) i=
      extendCoefficient (realDensityCoefficients i) w := by
    simp only [complexCoefficients,originalComplexDirection,extendCoefficient,realDensityCoefficients_source]
  simp only [source,extendCoefficient_smul,Pi.smul_apply]

private theorem frequency_complex_smul (z : ℂ) (v : Fin 289→ℂ) :
    complexFrequencyCoefficients (originalComplexDirection (z • v))=z • complexFrequencyCoefficients (originalComplexDirection v) := by
  funext i
  have source (w : Fin 289→ℂ) : complexFrequencyCoefficients (originalComplexDirection w) i=
      extendCoefficient (realFrequencyCoefficients i) w := by
    simp only [complexFrequencyCoefficients,originalComplexDirection,extendCoefficient,realFrequencyCoefficients_source]
  simp only [source,extendCoefficient_smul,Pi.smul_apply]

private def extendBilinear (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) : FiberOperators :=
  L (fun i=>(v i).re) (fun i=>(w i).re)-L (fun i=>(v i).im) (fun i=>(w i).im)+
    Complex.I • (L (fun i=>(v i).re) (fun i=>(w i).im)+L (fun i=>(v i).im) (fun i=>(w i).re))

private theorem bilinear_left (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) :
    extendBilinear L v w=extendCoefficient
      (L.flip (fun i=>(w i).re)+Complex.I • L.flip (fun i=>(w i).im)) v := by
  simp only [extendBilinear,extendCoefficient,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply,
    smul_add,smul_smul,Complex.I_mul_I]
  module

private theorem bilinear_right (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) :
    extendBilinear L v w=extendCoefficient
      (L (fun i=>(v i).re)+Complex.I • L (fun i=>(v i).im)) w := by
  simp only [extendBilinear,extendCoefficient,LinearMap.add_apply,LinearMap.smul_apply,
    smul_add,smul_smul,Complex.I_mul_I]
  module

private theorem bilinear_smul_left (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (z : ℂ) (v w : Fin 289→ℂ) :
    extendBilinear L (z • v) w=z • extendBilinear L v w := by
  rw [bilinear_left,extendCoefficient_smul,←bilinear_left]

private theorem bilinear_smul_right (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (z : ℂ) (v w : Fin 289→ℂ) :
    extendBilinear L v (z • w)=z • extendBilinear L v w := by
  rw [bilinear_right,extendCoefficient_smul,←bilinear_right]

private theorem mixed_complex_smul (a b : ℂ) (v w : Fin 289→ℂ) :
    complexMixedCoefficients (originalComplexDirection (a • v)) (originalComplexDirection (b • w))=
      (a*b) • complexMixedCoefficients (originalComplexDirection v) (originalComplexDirection w) := by
  funext i
  have source (x y : Fin 289→ℂ) : complexMixedCoefficients (originalComplexDirection x) (originalComplexDirection y) i=
      extendBilinear (realMixedCoefficientBilinear i) x y := by
    simp only [complexMixedCoefficients,originalComplexDirection,extendBilinear,realMixedCoefficientBilinear_source]
  simp only [source,bilinear_smul_left,bilinear_smul_right,smul_smul,Pi.smul_apply,mul_comm]

private theorem shift_add (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) :
    shiftCoefficients (A+B) shift=shiftCoefficients A shift+shiftCoefficients B shift := by
  funext i
  induction i using Fin.cases with
  | zero=>simp only [shiftCoefficients,Fin.cases_zero,Pi.add_apply,smul_add,Finset.sum_add_distrib];abel
  | succ j=>simp only [shiftCoefficients,Fin.cases_succ,Pi.add_apply]

private theorem shift_smul (z : ℂ) (A : Fin 4→FiberOperators) (shift : Fin 3→ℝ) :
    shiftCoefficients (z • A) shift=z • shiftCoefficients A shift := funext (shiftCoefficients_smul z A shift)

private theorem adjoint_smul (z : ℂ) (A : Fin 4→FiberOperators) :
    adjointCoefficients (z • A)=star z • adjointCoefficients A := by
  funext i
  simp only [adjointCoefficients,Pi.smul_apply,map_smulₛₗ,starRingEnd_apply]

private theorem word_smul_left (z : ℂ) (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord (z • A) B shift time age=z • orderedWord A B shift time age := by
  simp only [orderedWord,orderedLeft,shiftCoefficients_smul,ContinuousLinearMap.smul_compLpL,
    mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

private theorem word_smul_right (z : ℂ) (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord A (z • B) shift time age=z • orderedWord A B shift time age := by
  simp only [orderedWord,orderedRight,Pi.smul_apply,ContinuousLinearMap.smul_compLpL,
    mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

private theorem word_add_left (A C B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord (A+C) B shift time age=orderedWord A B shift time age+orderedWord C B shift time age := by
  simp only [orderedWord,orderedLeft,shift_add,Pi.add_apply,ContinuousLinearMap.add_compLpL,
    mul_add,add_mul,Finset.sum_add_distrib]

private theorem word_add_right (A B C : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (time age : ℝ) :
    orderedWord A (B+C) shift time age=orderedWord A B shift time age+orderedWord A C shift time age := by
  simp only [orderedWord,orderedRight,Pi.add_apply,ContinuousLinearMap.add_compLpL,
    mul_add,add_mul,Finset.sum_add_distrib]

private theorem contact_add (A B : Fin 4→FiberOperators) (time : ℝ) :
    contactWord (A+B) time=contactWord A time+contactWord B time := by
  simp only [contactWord,Pi.add_apply,ContinuousLinearMap.add_compLpL,mul_add,add_mul,Finset.sum_add_distrib]

/-- Independent positive/negative photon sources retain their complex and conjugate coefficients. -/
def sourceEmitterMonomials (ap an bp bn : ℂ) : Fin 4→ℂ :=
  ![an*star bn,star ap*star bn,an*bp,star ap*bp]

private def polarizationTensor (mode : Fin 289→ℂ) (sideL edgeL sideR edgeR : Fin 2)
    (shift : Fin 3→ℝ) (time age : ℝ) : Fin 4→ℂ × ℂ :=
  let D:=complexCoefficients (originalComplexDirection mode)
  let F:=complexFrequencyCoefficients (originalComplexDirection mode)
  let J:=adjointCoefficients (shiftCoefficients D (-shift))
  let W:=shiftCoefficients (adjointCoefficients F) shift
  let C:=complexMixedCoefficients (originalComplexDirection mode) (originalComplexDirection mode)
  let read:=sourceActualScatteringRead sideL edgeL sideR edgeR
  ![(Complex.I*(2:ℂ)⁻¹*read (orderedWord W D (-shift) age time),0),
    (Complex.I*(2:ℂ)⁻¹*read (orderedWord W J (-shift) age time),(2:ℂ)⁻¹*read (contactWord (adjointCoefficients C) time)),
    (-Complex.I*(2:ℂ)⁻¹*read (orderedWord D F shift time age),(2:ℂ)⁻¹*read (contactWord C time)),
    (-Complex.I*(2:ℂ)⁻¹*read (orderedWord J F shift time age),0)]

private theorem polarization_pair_tensor (mode : Fin 289→ℂ) (ap an bp bn : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) (shift : Fin 3→ℝ) (time age : ℝ) :
    sourcePreparedScatteringPair sideL edgeL sideR edgeR
      (originalTransferPair (ap • mode) (an • mode)) (originalTransferPair (bp • mode) (bn • mode)) shift time age=
      ∑i : Fin 4,sourceEmitterMonomials ap an bp bn i • polarizationTensor mode sideL edgeL sideR edgeR shift time age i := by
  have reader : realReaderCoefficients (originalTransferPair (ap • mode) (an • mode)) shift=
      (2:ℂ)⁻¹ • (an • complexCoefficients (originalComplexDirection mode)+
        star ap • adjointCoefficients (shiftCoefficients (complexCoefficients (originalComplexDirection mode)) (-shift))) := by
    funext i
    simp only [realReaderCoefficients,originalTransferPair,density_complex_smul,shift_smul,adjoint_smul,
      Pi.smul_apply,Pi.add_apply]
  have mixed : realMixedCoefficients (originalTransferPair (ap • mode) (an • mode))
      (originalTransferPair (bp • mode) (bn • mode))=
      (2:ℂ)⁻¹ • ((an*bp) • complexMixedCoefficients (originalComplexDirection mode) (originalComplexDirection mode)+
        star (ap*bn) • adjointCoefficients (complexMixedCoefficients (originalComplexDirection mode) (originalComplexDirection mode))) := by
    funext i
    simp only [realMixedCoefficients,originalTransferPair,mixed_complex_smul,Pi.smul_apply,
      Pi.add_apply,adjointCoefficients,map_smulₛₗ,starRingEnd_apply]
  simp only [sourcePreparedScatteringPair,fieldTwoTimeKernel,fieldMixedContact]
  simp only [reader,mixed]
  simp only [originalTransferPair,frequency_complex_smul,adjoint_smul,shift_smul,word_smul_left,word_smul_right,
    word_add_left,word_add_right,contactWord_smul,contact_add]
  apply Prod.ext <;>
    simp only [polarizationTensor,sourceEmitterMonomials,Fin.sum_univ_four,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
      Prod.smul_mk,Prod.fst_add,Prod.snd_add,smul_eq_mul,
      sourceActualScatteringRead_source,smul_apply,add_apply,sub_apply,
      inner_smul_right,inner_add_right,inner_sub_right,star_mul,mul_zero,add_zero]
  all_goals ring

/-- Four entries retain both full ordered frequency branches and both original direct-contact contributions. -/
def sourceNativeScatteringTensor (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) (time age : ℝ) : Fin 4→ℂ × ℂ :=
  polarizationTensor (sourceNativePolarization branch epsilon s n) sideL edgeL sideR edgeR (epsilon^2 • n) time age

/-- Actual source amplitudes, including conjugation, contract the polarization tensor in the same original quantum state. -/
theorem sourcePhotonScatteringResidue_emitterTensor (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonScatteringResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val (sourceSheet branch n unit e.val) n time age=
        ∑i : Fin 4,sourceEmitterMonomials
          (sourcePhotonEmitter Ap branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter An branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter Bp branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter Bn branch e.val (sourceSheet branch n unit e.val) n) i •
            sourceNativeScatteringTensor branch e.val (sourceSheet branch n unit e.val) n sideL edgeL sideR edgeR time age i := by
  filter_upwards [sourcePhotonResidue_factor branch n unit] with e factor
  rw [sourcePhotonScatteringResidue,sourcePhotonResidueTransfer,sourcePhotonResidueTransfer,
    factor Ap,factor An,factor Bp,factor Bn]
  exact polarization_pair_tensor _ _ _ _ _ _ _ _ _ _ _ _

/-- The actual physical-frequency response keeps the source epsilon-fourth factor on the complete tensor contraction. -/
theorem sourcePhotonScatteringFrequencyResidue_emitterTensor (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val (sourceSheet branch n unit e.val) n time age=
        (e.val:ℂ)^4 • ∑i : Fin 4,sourceEmitterMonomials
          (sourcePhotonEmitter Ap branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter An branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter Bp branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEmitter Bn branch e.val (sourceSheet branch n unit e.val) n) i •
            sourceNativeScatteringTensor branch e.val (sourceSheet branch n unit e.val) n sideL edgeL sideR edgeR time age i := by
  filter_upwards [sourcePhotonScatteringResidue_emitterTensor sideL edgeL sideR edgeR Ap An Bp Bn branch n unit time age]
    with e tensor
  rw [sourcePhotonScattering_frequencyScale,tensor]

end LowEnergy.PreparationPhysicalNativePolarizationEmitter
