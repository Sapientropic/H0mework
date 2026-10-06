import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerHalfSymbol

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore PreparationVacuumFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor
open scoped BigOperators ContDiff Topology

def D (i : Fin 100) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  fderiv ℝ f z (rawDirection i)

def sourceFourTermWeyl (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -(1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,
    (P i k z*D i (D k f) z+D i (fun w => P i k w*D k f w) z+
      D k (fun w => P i k w*D i f w) z+D i (D k (fun w => P i k w*f w)) z)

theorem D_smooth (i : Fin 100) {f : Profile} {z : SourceCoordinateSlice}
    (smooth : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (D i f) z :=
  (smooth.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem D_product (i : Fin 100) {a b : Profile} {z : SourceCoordinateSlice}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    D i (fun w => a w*b w) z=a z*D i b z+D i a z*b z := by
  unfold D
  have product : fderiv ℝ (fun w => a w*b w) z=
      a z • fderiv ℝ b z+b z • fderiv ℝ a z := by
    simpa only using! (ha.hasFDerivAt.mul hb.hasFDerivAt).fderiv
  rw [product]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem D_add (i : Fin 100) {a b : Profile} {z : SourceCoordinateSlice}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    D i (fun w => a w+b w) z=D i a z+D i b z := by
  have derivative : fderiv ℝ (fun w => a w+b w) z=fderiv ℝ a z+fderiv ℝ b z := by
    simpa only using! (ha.hasFDerivAt.add hb.hasFDerivAt).fderiv
  unfold D
  rw [derivative]
  rfl

private theorem secondProduct (i k : Fin 100) (f : ScalarTest) (z : physicalChart) :
    D i (D k (fun w => P i k w*f w)) z.val=
      P i k z.val*D i (D k f) z.val+D i (P i k) z.val*D k f z.val+
      D k (P i k) z.val*D i f z.val+D i (D k (P i k)) z.val*f z.val := by
  have localProduct : D k (fun w => P i k w*f w)=ᶠ[𝓝 z.val]
      (fun w => P i k w*D k f w+D k (P i k) w*f w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact D_product k ((P_smooth i k ⟨w,hw⟩).differentiableAt (by simp))
      ((f.contDiff.differentiable (by simp)).differentiableAt)
  have hp := (P_smooth i k z).differentiableAt (by simp)
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt (x:=z.val)
  have hdp := (D_smooth k (P_smooth i k z)).differentiableAt (by simp)
  have hdf := (D_smooth k (f.contDiff.contDiffAt (x:=z.val))).differentiableAt (by simp)
  have equality := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection i))
    localProduct.fderiv_eq
  change D i (D k (fun w => P i k w*f w)) z.val=
    D i (fun w => P i k w*D k f w+D k (P i k) w*f w) z.val at equality
  rw [equality,D_add i (a:=fun w => P i k w*D k f w)
    (b:=fun w => D k (P i k) w*f w) (hp.mul hdf) (hdp.mul hf),
    D_product i hp hdf,D_product i hdp hf]
  ring

theorem sourceFourTermWeyl_normalForm (f : ScalarTest) (z : physicalChart) :
    sourceFourTermWeyl f z.val=sourceWeylPrincipalAction f z.val := by
  have crossSecond : (∑ i : Fin 100,∑ k : Fin 100,P i k z.val*D k (D i f) z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,P i k z.val*D i (D k f) z.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    unfold P
    rw [sourceTensor_symmetric k i]
  have crossFirst : (∑ i : Fin 100,∑ k : Fin 100,D k (P i k) z.val*D i f z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,D i (P i k) z.val*D k f z.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have symmetry : P k i=P i k := by
      funext w
      exact congrArg (fun r : ℝ => (r : ℂ)) (sourceTensor_symmetric k i w)
    rw [symmetry]
  have term (i k : Fin 100) :
      P i k z.val*D i (D k f) z.val+D i (fun w => P i k w*D k f w) z.val+
        D k (fun w => P i k w*D i f w) z.val+D i (D k (fun w => P i k w*f w)) z.val=
      3*(P i k z.val*D i (D k f) z.val)+P i k z.val*D k (D i f) z.val+
        2*(D i (P i k) z.val*D k f z.val)+2*(D k (P i k) z.val*D i f z.val)+
        D i (D k (P i k)) z.val*f z.val := by
    rw [D_product i ((P_smooth i k z).differentiableAt (by simp))
      ((D_smooth k f.contDiff.contDiffAt).differentiableAt (by simp)),
      D_product k ((P_smooth i k z).differentiableAt (by simp))
      ((D_smooth i f.contDiff.contDiffAt).differentiableAt (by simp)),secondProduct]
    ring
  unfold sourceFourTermWeyl
  simp only [term,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  have crossFactored : (∑ i : Fin 100,(∑ k : Fin 100,D k (P i k) z.val)*D i f z.val)=
      ∑ i : Fin 100,∑ k : Fin 100,D i (P i k) z.val*D k f z.val := by
    simpa only [Finset.sum_mul] using crossFirst
  rw [crossSecond,crossFactored]
  have principal : tensorPrincipalAction f z.val=
      -∑ i : Fin 100,∑ k : Fin 100,(P i k z.val*D i (D k f) z.val+
        D i (P i k) z.val*D k f z.val) := rfl
  have correction : tensorWeylCorrection z.val=
      (1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,D i (D k (P i k)) z.val := rfl
  rw [sourceWeylPrincipalAction,principal,correction]
  simp only [Finset.sum_add_distrib]
  ring

theorem originalHalfVacuum_fourTermWeyl (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      sourceFourTermWeyl f z.val+sourceWeylZero z.val*f z.val := by
  rw [sourceFourTermWeyl_normalForm]
  exact originalHalfVacuum_WeylZero f z

end LowEnergy.PreparationVacuumWeylOrdering
