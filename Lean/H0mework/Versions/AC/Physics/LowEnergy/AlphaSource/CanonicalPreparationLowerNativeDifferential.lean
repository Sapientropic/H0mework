import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationVacuumSymbol

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerLeaves
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open GaussHistoryHilbert GaussCoreDifferential GaussLiveMomentum GaussDensityCore
open GaussNativeEnergy GaussNativePotential GaussNativeForm GaussScalarTransport
open PreparationVacuumFactor CanonicalPreparationCore CanonicalPreparationMomentum
open scoped BigOperators ContDiff

abbrev Profile := SourceCoordinateSlice → ℂ

def fieldD (v : Ambient) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  fderiv ℝ f z (direction v z)

def divergence (v : Ambient) (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : FrameIndex, fderiv ℝ (fun w => (coefficient v i w : ℂ)) z (frame i)

def densityDrift (D z : SourceCoordinateSlice) : ℂ :=
  (complexDensity 0 z)⁻¹*fderiv ℝ (complexDensity 0) z D

def fieldT (v : Ambient) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -fieldD v f z-(divergence v z+densityDrift (direction v z) z)*f z

def constantD (D : SourceCoordinateSlice) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  fderiv ℝ f z D

def constantT (D : SourceCoordinateSlice) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -constantD D f z-densityDrift D z*f z

private def evaluation (z : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evaluation_apply (z : SourceCoordinateSlice) (f : ScalarTest) : evaluation z f=f z := rfl

theorem derivative_coefficient (v : Ambient) (i : FrameIndex) (D : SourceCoordinateSlice)
    (f : ScalarTest) (z : physicalChart) :
    GaussDensityCore.derivative D (multiplyCoefficient v i f) z.val=
      (coefficient v i z.val : ℂ)*fderiv ℝ f z.val D+
        fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val D*f z.val := by
  have hc:=((coefficient_smooth v i z).differentiableAt (by simp)).hasFDerivAt
  have hf:=(f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have product : fderiv ℝ (fun w => (coefficient v i w : ℂ)*f w) z.val=
      (coefficient v i z.val : ℂ) • fderiv ℝ f z.val+
        f z.val • fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val := by
    simpa using! (hc.mul hf).fderiv
  rw [GaussDensityCore.derivative_apply]
  change fderiv ℝ (fun w => (coefficient v i w : ℂ)*f w) z.val D=_
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem source_frame_read (v : Ambient) (L : SourceCoordinateSlice →L[ℝ] ℂ)
    (z : SourceCoordinateSlice) :
    (∑ i : FrameIndex, (coefficient v i z : ℂ)*L (frame i))=L (direction v z) := by
  calc
    _=∑ i : FrameIndex,L (coefficient v i z • frame i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,RCLike.real_smul_eq_coe_mul]
      rfl
    _=L (∑ i : FrameIndex,coefficient v i z • frame i) := (map_sum L _ _).symm
    _=L (direction v z) := congrArg L (frame.sum_repr (direction v z))

theorem original_fieldTranspose_readback (v : Ambient) (f : ScalarTest) (z : physicalChart) :
    fieldTranspose 0 v f z.val=fieldT v f z.val := by
  have expanded : fieldTranspose 0 v f z.val=
      ∑ i : FrameIndex, (-(coefficient v i z.val : ℂ)*fderiv ℝ f z.val (frame i)-
        (fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val (frame i)+
          (complexDensity 0 z.val)⁻¹*(coefficient v i z.val : ℂ)*
            fderiv ℝ (complexDensity 0) z.val (frame i))*f z.val) := by
    change evaluation z.val ((∑ i : FrameIndex,
      (weightedTranspose 0 (frame i)).comp (multiplyCoefficient v i)) f)=_
    rw [LinearMap.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change weightedTranspose 0 (frame i) (multiplyCoefficient v i f) z.val=_
    rw [weightedTranspose_expand,derivative_coefficient]
    change -((coefficient v i z.val : ℂ)*fderiv ℝ f z.val (frame i)+
      fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val (frame i)*f z.val)-
      (complexDensity 0 z.val)⁻¹*fderiv ℝ (complexDensity 0) z.val (frame i)*
        ((coefficient v i z.val : ℂ)*f z.val)=_
    ring
  rw [expanded]
  have grouped : (∑ i : FrameIndex, (-(coefficient v i z.val : ℂ)*fderiv ℝ f z.val (frame i)-
        (fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val (frame i)+
          (complexDensity 0 z.val)⁻¹*(coefficient v i z.val : ℂ)*
            fderiv ℝ (complexDensity 0) z.val (frame i))*f z.val))=
      -(∑ i : FrameIndex,(coefficient v i z.val : ℂ)*fderiv ℝ f z.val (frame i))-
      ((∑ i : FrameIndex,fderiv ℝ (fun w => (coefficient v i w : ℂ)) z.val (frame i))+
        (complexDensity 0 z.val)⁻¹*∑ i : FrameIndex,(coefficient v i z.val : ℂ)*
          fderiv ℝ (complexDensity 0) z.val (frame i))*f z.val := by
    simp only [neg_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
    congr 1
    rw [←Finset.sum_mul,Finset.sum_add_distrib]
    simp only [mul_assoc]
    rw [←Finset.mul_sum]
  rw [grouped,source_frame_read,source_frame_read]
  rfl

theorem original_constantTranspose_readback (D : SourceCoordinateSlice) (f : ScalarTest)
    (z : physicalChart) : weightedTranspose 0 D f z.val=constantT D f z.val := by
  rw [weightedTranspose_expand,GaussDensityCore.derivative_apply]
  rfl

def originalLocalVacuumAction (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  (1/2 : ℂ)*(∑ a : ScalarIndex,fieldT (scalarDirection a)
    (fun w => (scalarWeight w : ℂ)*fieldD (scalarDirection a) f w) z)+
  (1/2 : ℂ)*(∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,fieldT (gaugeDirection i a)
    (fun w => (gaugeWeight w i j : ℂ)*fieldD (gaugeDirection j a) f w) z)+
  (∑ i : Fin 6,∑ j : Fin 6,constantT (GaussCoframeCore.coframeDirection i)
    (fun w => (GaussCoframeKinetic.coefficient i j w : ℂ)*
      constantD (GaussCoframeCore.coframeDirection j) f w) z)+
  ((potential z+GaussCoframeForm.volumePotential z : ℝ) : ℂ)*f z

theorem original_sandwich_readback (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) (z : physicalChart) :
    scalarSandwich v w c smooth f z.val=
      fieldT v (fun x => (c x : ℂ)*fieldD w f x) z.val := by
  rw [scalarSandwich,LinearMap.comp_apply,LinearMap.comp_apply,original_fieldTranspose_readback]
  have profile : (⇑(realCoefficient c smooth (fieldDerivative w f)) : Profile)=
      fun x => (c x : ℂ)*fieldD w f x := by
    funext x
    change (c x : ℂ)*fieldDerivative w f x=_
    rw [fieldDerivative_apply]
    rfl
  rw [profile]

theorem original_coframeTerm_readback (i j : Fin 6) (f : ScalarTest) (z : physicalChart) :
    coframeTerm 0 i j f z.val=
      constantT (GaussCoframeCore.coframeDirection i)
        (fun w => (GaussCoframeKinetic.coefficient i j w : ℂ)*
          constantD (GaussCoframeCore.coframeDirection j) f w) z.val := by
  rw [coframeTerm,LinearMap.comp_apply,LinearMap.comp_apply,original_constantTranspose_readback]
  have profile : (⇑(coframeCoefficient i j
      (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f)) : Profile)=
      fun w => (GaussCoframeKinetic.coefficient i j w : ℂ)*
        constantD (GaussCoframeCore.coframeDirection j) f w := by
    funext w
    change (GaussCoframeKinetic.coefficient i j w : ℂ)*
      GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f w=_
    rw [GaussDensityCore.derivative_apply]
    rfl
  rw [profile]

theorem originalLocalVacuumAction_readback (f : ScalarTest) (z : physicalChart) :
    scalarVacuumAction f z.val=originalLocalVacuumAction f z.val := by
  change evaluation z.val (scalarVacuumAction f)=_
  simp only [scalarVacuumAction,nativeVacuum,scalarKineticVacuum,gaugeKineticVacuum,coframeKinetic,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,map_add,map_smul,map_sum]
  simp only [evaluation_apply,original_sandwich_readback,original_coframeTerm_readback,smul_eq_mul]
  change (1/2 : ℂ)*(∑ a : ScalarIndex,fieldT (scalarDirection a)
    (fun w => (scalarWeight w : ℂ)*fieldD (scalarDirection a) f w) z.val)+
    (1/2 : ℂ)*(∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,fieldT (gaugeDirection i a)
      (fun w => (gaugeWeight w i j : ℂ)*fieldD (gaugeDirection j a) f w) z.val)+
    (potential z.val : ℂ)*f z.val+
    (∑ i : Fin 6,∑ j : Fin 6,constantT (GaussCoframeCore.coframeDirection i)
      (fun w => (GaussCoframeKinetic.coefficient i j w : ℂ)*
        constantD (GaussCoframeCore.coframeDirection j) f w) z.val)+
    (GaussCoframeForm.volumePotential z.val : ℂ)*f z.val=_
  unfold originalLocalVacuumAction
  push_cast
  ring

end LowEnergy.PreparationVacuumLowerLeaves
