import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerTensorFlux

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensor
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussLiveMomentum GaussCoreDifferential
open GaussScalarTransport GaussDensityCore PreparationScalarCoordinates CanonicalPreparationMomentum
open PreparationVacuumLowerLeaves PreparationActualFactor PreparationVacuumDensityTrace PreparationVacuumFactor
open scoped BigOperators ContDiff

def sourcePairFlux (a : SourcePair) (f : Profile) (z : SourceCoordinateSlice) (i : Fin 100) : ℂ :=
  (sourceCoefficient a z : ℂ)*(rawCovector i (sourceLeft a z) : ℂ)*
    fderiv ℝ f z (sourceRight a z)

theorem sourcePairFlux_smooth (a : SourcePair) (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => sourcePairFlux a f w i) z.val := by
  have coefficient:=Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (sourceCoefficient_smooth a z)
  have left:=Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((rawCovector i).contDiff.contDiffAt.comp z.val (sourceLeft_smooth a z))
  have derivative : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
  exact (coefficient.mul left).mul (derivative.contDiffAt.clm_apply (sourceRight_smooth a z))

private theorem rawDiv_sum {ι : Type*} [Fintype ι]
    (G : ι → SourceCoordinateSlice → Fin 100 → ℂ) (z : SourceCoordinateSlice)
    (smooth : ∀ a i,DifferentiableAt ℝ (fun w => G a w i) z) :
    rawWeightedDivergence (fun w i => ∑ a : ι,G a w i) z=
      ∑ a : ι,rawWeightedDivergence (G a) z := by
  unfold rawWeightedDivergence
  have derivative (i : Fin 100) :
      fderiv ℝ (fun w => ∑ a : ι,G a w i) z=∑ a : ι,fderiv ℝ (fun w => G a w i) z :=
    fderiv_fun_sum (fun a _ => smooth a i)
  simp only [derivative,sum_apply,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  congr 1
  exact Finset.sum_comm

private theorem rawDiv_constMul (c : ℂ) (G : SourceCoordinateSlice → Fin 100 → ℂ)
    (z : SourceCoordinateSlice) (smooth : ∀ i,DifferentiableAt ℝ (fun w => G w i) z) :
    rawWeightedDivergence (fun w i => c*G w i) z=c*rawWeightedDivergence G z := by
  unfold rawWeightedDivergence
  have derivative (i : Fin 100) : fderiv ℝ (fun w => c*G w i) z=
      c • fderiv ℝ (fun w => G w i) z := (smooth i).hasFDerivAt.const_mul c |>.fderiv
  simp only [derivative,smul_apply,smul_eq_mul]
  rw [mul_neg,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem rawFieldFlux_smooth (v : Ambient) (f : ScalarTest) (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => rawFieldFlux v f w i) z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((rawCovector i).contDiff.contDiffAt.comp z.val (direction_smooth v z))).mul f.contDiff.contDiffAt

def constantFlux (D : SourceCoordinateSlice) (f : Profile)
    (z : SourceCoordinateSlice) (i : Fin 100) : ℂ := (rawCovector i D : ℂ)*f z

theorem original_constantTranspose_rawFlux (D : SourceCoordinateSlice) (f : ScalarTest) (z : physicalChart) :
    weightedTranspose 0 D f z.val=rawWeightedDivergence (constantFlux D f) z.val := by
  have derivative (i : Fin 100) :
      fderiv ℝ (fun w => constantFlux D f w i) z.val=
        (rawCovector i D : ℂ) • fderiv ℝ f z.val :=
    ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.const_mul
      (rawCovector i D : ℂ)).fderiv
  have density : (∑ i : Fin 100,densityDrift (rawDirection i) z.val*constantFlux D f z.val i)=
      densityDrift D z.val*f z.val := by
    unfold densityDrift constantFlux
    have group : (∑ i : Fin 100,(complexDensity 0 z.val)⁻¹*
        fderiv ℝ (complexDensity 0) z.val (rawDirection i)*((rawCovector i D : ℂ)*f z.val))=
      (complexDensity 0 z.val)⁻¹*(∑ i : Fin 100,(rawCovector i D : ℂ)*
        fderiv ℝ (complexDensity 0) z.val (rawDirection i))*f z.val := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [group,original_raw_read]
  rw [original_constantTranspose_readback]
  unfold constantT constantD rawWeightedDivergence
  simp only [derivative,smul_apply,smul_eq_mul,Finset.sum_add_distrib]
  rw [original_raw_read,density]
  ring

def sourcePairAction (a : SourcePair) : ScalarTest →ₗ[ℂ] ScalarTest :=
  match a with
  | Sum.inl i => (1/2 : ℂ) • scalarSandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth
  | Sum.inr (Sum.inl (a,i,j)) => (1/2 : ℂ) • scalarSandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
  | Sum.inr (Sum.inr (i,j)) => coframeTerm 0 i j

theorem originalKinetic_pool : scalarKineticVacuum+gaugeKineticVacuum+coframeKinetic 0=
    ∑ a : SourcePair,sourcePairAction a := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourcePairAction,
    ←Finset.smul_sum,scalarKineticVacuum,gaugeKineticVacuum,coframeKinetic]
  abel

theorem originalPairAction_raw (a : SourcePair) (f : ScalarTest) (z : physicalChart) :
    sourcePairAction a f z.val=rawWeightedDivergence (sourcePairFlux a f) z.val := by
  rcases a with a|⟨a,i,j⟩|⟨i,j⟩
  · let h:=realCoefficient scalarWeight scalarWeight_smooth (fieldDerivative (scalarDirection a) f)
    have profile : sourcePairFlux (Sum.inl a) f=
        (fun w i => (1/2 : ℂ)*rawFieldFlux (scalarDirection a) h w i) := by
      funext w i
      change ((scalarWeight w/2 : ℝ) : ℂ)*(rawCovector i (direction (scalarDirection a) w) : ℂ)*
        fderiv ℝ f w (direction (scalarDirection a) w)=
        (1/2 : ℂ)*((rawCovector i (direction (scalarDirection a) w) : ℂ)*
          ((scalarWeight w : ℂ)*fieldDerivative (scalarDirection a) f w))
      rw [fieldDerivative_apply]
      push_cast
      ring
    rw [profile,rawDiv_constMul (1/2) _ _
      (fun i => (rawFieldFlux_smooth _ h i z).differentiableAt (by simp))]
    change (1/2 : ℂ)*fieldTranspose 0 (scalarDirection a) h z.val=_
    rw [original_fieldTranspose_rawFlux]
  · let h:=realCoefficient (fun w => gaugeWeight w i j) (gaugeWeight_smooth i j)
      (fieldDerivative (gaugeDirection j a) f)
    have profile : sourcePairFlux (Sum.inr (Sum.inl (a,i,j))) f=
        (fun w k => (1/2 : ℂ)*rawFieldFlux (gaugeDirection i a) h w k) := by
      funext w k
      change ((gaugeWeight w i j/2 : ℝ) : ℂ)*(rawCovector k (direction (gaugeDirection i a) w) : ℂ)*
        fderiv ℝ f w (direction (gaugeDirection j a) w)=
        (1/2 : ℂ)*((rawCovector k (direction (gaugeDirection i a) w) : ℂ)*
          ((gaugeWeight w i j : ℂ)*fieldDerivative (gaugeDirection j a) f w))
      rw [fieldDerivative_apply]
      push_cast
      ring
    rw [profile,rawDiv_constMul (1/2) _ _
      (fun k => (rawFieldFlux_smooth _ h k z).differentiableAt (by simp))]
    change (1/2 : ℂ)*fieldTranspose 0 (gaugeDirection i a) h z.val=_
    rw [original_fieldTranspose_rawFlux]
  · let h:=coframeCoefficient i j (GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f)
    have profile : sourcePairFlux (Sum.inr (Sum.inr (i,j))) f=
        constantFlux (GaussCoframeCore.coframeDirection i) h := by
      funext w k
      change (GaussCoframeKinetic.coefficient i j w : ℂ)*
        (rawCovector k (GaussCoframeCore.coframeDirection i) : ℂ)*
        fderiv ℝ f w (GaussCoframeCore.coframeDirection j)=
        (rawCovector k (GaussCoframeCore.coframeDirection i) : ℂ)*
          ((GaussCoframeKinetic.coefficient i j w : ℂ)*
            GaussDensityCore.derivative (GaussCoframeCore.coframeDirection j) f w)
      rw [GaussDensityCore.derivative_apply]
      ring
    rw [profile]
    exact original_constantTranspose_rawFlux _ h z

private def evaluation (z : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem originalVacuum_tensorAction (f : ScalarTest) (z : physicalChart) :
    scalarVacuumAction f z.val=rawWeightedDivergence (tensorFlux f) z.val+
      ((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ)*f z.val := by
  have pool:=congrArg (fun A : ScalarTest →ₗ[ℂ] ScalarTest => evaluation z.val (A f)) originalKinetic_pool
  simp only [LinearMap.add_apply,LinearMap.sum_apply,map_add,map_sum] at pool
  change scalarKineticVacuum f z.val+gaugeKineticVacuum f z.val+coframeKinetic 0 f z.val=
    ∑ a : SourcePair,sourcePairAction a f z.val at pool
  rw [show tensorFlux (f : Profile)=sourceFlux f by
    funext w i
    exact (originalFlux_tensor f w i).symm]
  have division : rawWeightedDivergence (sourceFlux f) z.val=
      ∑ a : SourcePair,rawWeightedDivergence (sourcePairFlux a f) z.val :=
    rawDiv_sum (fun a => sourcePairFlux a f) z.val
      (fun a i => (sourcePairFlux_smooth a f i z).differentiableAt (by simp))
  rw [division]
  simp only [←originalPairAction_raw]
  rw [←pool]
  change scalarKineticVacuum f z.val+gaugeKineticVacuum f z.val+(potential z.val : ℂ)*f z.val+
    coframeKinetic 0 f z.val+(GaussCoframeForm.volumePotential z.val : ℂ)*f z.val=_
  push_cast
  ring

end LowEnergy.PreparationVacuumLowerTensor
