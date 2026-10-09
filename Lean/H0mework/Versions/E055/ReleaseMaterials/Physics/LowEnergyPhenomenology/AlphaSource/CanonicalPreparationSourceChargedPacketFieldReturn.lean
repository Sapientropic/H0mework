import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePacketGreenTail
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargedFieldRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedPacketGreen
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumNativeSlowCoupling
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open PreparationVacuumStaticPoleResponse PreparationVacuumWholeOrigin
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumQuantumSlowResidue PreparationVacuumSourceFieldFamily
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumMixedFieldReturn
open PreparationVacuumActualSpatialPacket PreparationVacuumObservedPoleTensor
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame unrestrictedGreen slowFastFrame
  sourceNativeReader sourceActualNativeForcing returnedHalfCurrent

private theorem five_smul (z : ℂ) (v : Fin 5→ℂ) : fiveVector (z • v)=z • fiveVector v := by
  funext i
  by_cases inside : i.val<5
  · simp only [fiveVector,dif_pos inside,Pi.smul_apply]
  · simp only [fiveVector,dif_neg inside,Pi.smul_apply,smul_zero]

private theorem five_continuous : Continuous (fiveVector : (Fin 5→ℂ)→Fin 289→ℂ) := by
  apply continuous_pi
  intro i
  unfold fiveVector
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

private theorem corner_scaled (d : ℝ) (nonzero : d≠0) (f : Fin 289→ℂ) :
    ((d:ℂ)^3) • sourceCornerRead d f=sourceReducedRead d ((d:ℂ) • f) := by
  funext i
  simp only [sourceCornerRead,sourceReducedRead,wideRayScaling,Matrix.mulVec_diagonal,Pi.smul_apply,
    Matrix.mulVec_smul,smul_eq_mul,fiveIndex,i.isLt,if_true]
  split_ifs <;> field_simp [Complex.ofReal_ne_zero.mpr nonzero]

private theorem reduced_continuous : Continuous (fun p : ℝ×(Fin 289→ℂ)=>sourceReducedRead p.1 p.2) := by
  apply continuous_pi
  intro i
  unfold sourceReducedRead
  split_ifs <;> fun_prop

private theorem point_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>fixedMomentum (d • n) ((d:ℂ)*zeta)) (𝓝[>] 0) (𝓝 0) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [sourcePhysicalRay_generated,zero_smul] using scalar.smul (tendsto_const_nhds (x:=fixedMomentum n zeta))

private theorem matrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem regular_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>sourceRegularMatrix (fixedMomentum (d • n) ((d:ℂ)*zeta))) (𝓝[>] 0)
      (𝓝 (sourceRegularMatrix 0)) := by
  have point:=point_limit n zeta
  have changeLimit:=(matrix_continuous originalChangeTerms).continuousAt.tendsto.comp point
  have contact:=(matrix_continuous contactInverseTerms).continuousAt.tendsto.comp point
  have readback : Continuous originalReadback := by
    unfold originalReadback originalChange
    exact ((matrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose
  have read:=readback.continuousAt.tendsto.comp point
  have green:=unrestrictedGreen_smooth_origin.continuousAt.tendsto.comp point
  exact changeLimit.mul ((contact.mul read).add ((green.mul tendsto_const_nhds).mul read))

/-- The original complete field has two contributions at its first charged order: the native frame jet and the original regular/contact response. -/
def sourceChargedSecondField (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceChargedActualFieldJet q n zeta l r+
    sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n zeta l r

private theorem scaled_coordinates (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>fiveVector ((sourceCausalNormalized n zeta.val d)⁻¹*ᵥ
      (((d:ℂ)^3) • sourceCornerRead d (sourceActualNativeForcing q n zeta.val l r d))))
      (𝓝[>] 0) (𝓝 (sourceChargedFrameInput q n zeta.val l r)) := by
  have forcing:=sourceActualNative_residue q n zeta.val zeta.property.1 l r nonrealL nonrealR
  have realScalar : Tendsto (fun d : ℝ=>d) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have reduced:=reduced_continuous.continuousAt.tendsto.comp (realScalar.prodMk_nhds forcing)
  have origin : sourceReducedRead 0 (sourceActualNativeResidue q n zeta.val l r)=
      sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) := by
    funext i
    simp only [sourceReducedRead,sourceSlowRead,Complex.ofReal_zero]
    split_ifs <;> simp only [one_mul,zero_mul]
  rw [origin] at reduced
  have input : Tendsto (fun d : ℝ=>((d:ℂ)^3) • sourceCornerRead d (sourceActualNativeForcing q n zeta.val l r d))
      (𝓝[>] 0) (𝓝 (sourceSlowRead (sourceActualNativeResidue q n zeta.val l r))) := by
    apply reduced.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (corner_scaled d (ne_of_gt hd) _).symm
  have coordinates:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    ((sourceCausalInverse_limit n zeta).prodMk_nhds input)
  exact five_continuous.continuousAt.tendsto.comp coordinates

private theorem charged_scaled (d : ℂ) (nonzero : d≠0) (A : Matrix (Fin 289) (Fin 289) ℂ)
    (v : Fin 289→ℂ) (mu : Fin 4) :
    d^2*sourceChargedCoefficient (A*ᵥv) mu=
      sourceChargedCoefficient ((d⁻¹ • (A-fullNativeOrigin*slowFastFrame))*ᵥ(d^3 • v)) mu := by
  have origin : sourceChargedCoefficient ((fullNativeOrigin*slowFastFrame)*ᵥv) mu=0 := by
    rw [←Matrix.mulVec_mulVec]
    exact sourceChargedNativeOrigin_slot _ mu
  rw [Matrix.smul_mulVec,Matrix.mulVec_smul,Matrix.sub_mulVec]
  change d^2*sourceChargedCoefficient (A*ᵥv) mu=
    d⁻¹*(d^3*(sourceChargedCoefficient (A*ᵥv) mu-sourceChargedCoefficient ((fullNativeOrigin*slowFastFrame)*ᵥv) mu))
  rw [origin,sub_zero]
  field_simp

/-- The first non-leading charged field is produced from the original complete causal field, with its regular/contact contribution retained. -/
theorem sourceChargedSecondField_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (mu : Fin 4)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceChargedCoefficient (sourceJointCausalField q n zeta.val l r d) mu)
      (𝓝[>] 0) (𝓝 (sourceChargedCoefficient (sourceChargedSecondField q n zeta.val l r) mu)) := by
  have slope:=sourceChargedNativeFrame_slope (fixedMomentum n zeta.val)
  have physical : Tendsto (fun d : ℝ=>(d:ℂ)⁻¹ •
      (sourceNativeFrame (fixedMomentum (d • n) ((d:ℂ)*zeta.val))-fullNativeOrigin*slowFastFrame))
      (𝓝[>] 0) (𝓝 (sourceChargedNativeFrameJet (fixedMomentum n zeta.val))) := by
    simpa only [sourcePhysicalRay_generated] using slope
  have native:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (physical.prodMk_nhds (scaled_coordinates q n zeta l r nonrealL nonrealR))
  have regular:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    ((regular_limit n zeta.val).prodMk_nhds
      (sourceFullCurrent_residue q n zeta.val zeta.property.1 l r nonrealL nonrealR))
  have coordinates:=(continuous_apply (lorentzSlot mu (sourceSpinSlot 2))).continuousAt.tendsto.comp (native.add regular)
  change Tendsto _ _ (𝓝 (sourceChargedCoefficient (sourceChargedSecondField q n zeta.val l r) mu)) at coordinates
  apply coordinates.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have nonzero : (d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
  have rescaled:=charged_scaled (d:ℂ) nonzero
    (sourceNativeFrame (fixedMomentum (d • n) ((d:ℂ)*zeta.val)))
    (fiveVector ((sourceCausalNormalized n zeta.val d)⁻¹*ᵥ
      sourceCornerRead d (sourceActualNativeForcing q n zeta.val l r d))) mu
  simp only [sourceJointCausalField,sourceCausalFullExpression,←sourceActualNativeForcing_generated]
  simp only [Matrix.mulVec_smul,five_smul] at rescaled ⊢
  change sourceChargedCoefficient _ mu+sourceChargedCoefficient _ mu=
    (d:ℂ)^2*(sourceChargedCoefficient _ mu+sourceChargedCoefficient _ mu)
  rw [mul_add,rescaled]
  congr 1 <;> simp only [sourceChargedCoefficient,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]

private theorem charged_observed (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (F : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart F)=
      ∑mu : Fin 4,sourceChargedCoefficient F mu*sourceAmputatedFieldVertex q pL pR a b (sourceChargedLockedField mu) := by
  simp only [sourceAmputatedFieldVertex,sourceChargedFieldPart,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

/-- The actual independently amputated detector consumes the generated charged order on both original material legs. -/
theorem sourceChargedSecondField_observed (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*sourceAmputatedFieldVertex q pL pR a b
      (sourceChargedFieldPart (sourceJointCausalField q n zeta.val l r d)))
      (𝓝[>] 0) (𝓝 (sourceAmputatedFieldVertex q pL pR a b
        (sourceChargedFieldPart (sourceChargedSecondField q n zeta.val l r)))) := by
  simp only [charged_observed,Finset.mul_sum,←mul_assoc]
  exact tendsto_finsetSum _ (fun mu _=>(sourceChargedSecondField_generated q n zeta l r mu nonrealL nonrealR).mul_const _)

/-- The fixed original Fourier packet and both independent material legs consume this source limit at each physical frequency. -/
theorem sourceChargedSecondField_original_packet (q : PhysicalResponsePoint)
    (frequency : FullQuantum.FullSpace.Position) (zeta : sourceCausalDomain (FullQuantum.FullSpace.physicalMomentum frequency))
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*(PreparationVacuumStaticSpatialSource.sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency
        (sourceChargedFieldPart (sourceJointCausalField q (FullQuantum.FullSpace.physicalMomentum frequency) zeta.val l r d))))
      (𝓝[>] 0) (𝓝 (PreparationVacuumStaticSpatialSource.sourceSpatialPhase (fun j=>frequency j) position*
        sourcePacketIndependentVertex q pL pR a b frequency
          (sourceChargedFieldPart (sourceChargedSecondField q (FullQuantum.FullSpace.physicalMomentum frequency) zeta.val l r)))) := by
  have limit:=sourceChargedSecondField_observed q (FullQuantum.FullSpace.physicalMomentum frequency) zeta l r a b pL pR nonrealL nonrealR
  have weighted:=limit.const_mul (PreparationVacuumStaticSpatialSource.sourceSpatialPhase (fun j=>frequency j) position*
    (star (sourceFrequencyPacket frequency)*sourceFrequencyPacket frequency))
  simp only [sourcePacketIndependentVertex_generated]
  convert weighted using 1
  · funext d
    ring
  · congr 1
    ring

/-- The same source field equation remains the complete Jacobi equation with the original null-current constraint. -/
theorem sourceChargedSecondField_original_equation (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (d : sourceCausalScale n zeta) :
    originalJacobi (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥsourceJointCausalField q n zeta.val l r d.val=
      returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val)-
      originalRowLift (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
        (nullProjection*ᵥ(originalReadback (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
          returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val))) :=
  sourceJointCausalField_whole q n zeta l r d

end LowEnergy.PreparationVacuumChargedPacketGreen
