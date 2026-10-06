import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylTemporalTensor

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumDensityTrace
open PreparationVacuumEnergyTail PreparationVacuumFactor
open scoped BigOperators ContDiff Topology

def DR (i : Fin 100) (f : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) : ℝ :=
  fderiv ℝ f z (rawDirection i)

theorem DR_smooth (i : Fin 100) {f : SourceCoordinateSlice → ℝ} {z : SourceCoordinateSlice}
    (smooth : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (DR i f) z :=
  (smooth.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem D_ofReal (i : Fin 100) {f : SourceCoordinateSlice → ℝ} {z : SourceCoordinateSlice}
    (smooth : DifferentiableAt ℝ f z) :
    D i (fun w => (f w : ℂ)) z=(DR i f z : ℂ) := by
  have derivative : fderiv ℝ (fun w => (f w : ℂ)) z=
      Complex.ofRealCLM.comp (fderiv ℝ f z) := by
    simpa only using! (Complex.ofRealCLM.hasFDerivAt.comp z smooth.hasFDerivAt).fderiv
  unfold D DR
  rw [derivative]
  rfl

theorem D_leafP_real (j : Fin 13) (i k r : Fin 100) (z : physicalChart) :
    D r (leafP j i k) z.val=(DR r (rawPrincipalCoefficient j i k) z.val : ℂ) :=
  D_ofReal r ((rawPrincipalCoefficient_smooth j i k z).differentiableAt (by simp))

theorem DD_leafP_real (j : Fin 13) (i k r s : Fin 100) (z : physicalChart) :
    D r (D s (leafP j i k)) z.val=(DR r (DR s (rawPrincipalCoefficient j i k)) z.val : ℂ) := by
  have equal : D s (leafP j i k)=ᶠ[𝓝 z.val]
      (fun w => (DR s (rawPrincipalCoefficient j i k) w : ℂ)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact D_leafP_real j i k s ⟨w,hw⟩
  have read := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq
  change D r (D s (leafP j i k)) z.val=D r (fun w => (DR s (rawPrincipalCoefficient j i k) w : ℂ)) z.val at read
  rw [read]
  exact D_ofReal r ((DR_smooth s (rawPrincipalCoefficient_smooth j i k z)).differentiableAt (by simp))

theorem rawHalfLog_smooth (i : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (rawHalfLog i) z.val := by
  have half := realSourceHalf_smooth z
  have nonzero : realSourceHalf z.val≠0 := (Real.sqrt_pos.mpr (density_pos 0 z)).ne'
  exact (half.inv nonzero).mul ((half.fderiv_right (by simp)).clm_apply contDiffAt_const)

theorem ell_real (i : Fin 100) (z : physicalChart) : ell i z.val=(rawHalfLog i z.val : ℂ) :=
  sourceHalf_rawLog i z

theorem D_ell_real (i r : Fin 100) (z : physicalChart) :
    D r (ell i) z.val=(DR r (rawHalfLog i) z.val : ℂ) := by
  have equal : ell i=ᶠ[𝓝 z.val] (fun w => (rawHalfLog i w : ℂ)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact ell_real i ⟨w,hw⟩
  have read := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq
  change D r (ell i) z.val=D r (fun w => (rawHalfLog i w : ℂ)) z.val at read
  rw [read]
  exact D_ofReal r ((rawHalfLog_smooth i z).differentiableAt (by simp))

def leafHalf (j : Fin 13) (z : SourceCoordinateSlice) : ℂ :=
  ∑ i : Fin 100,∑ k : Fin 100,
    (D i (leafP j i k) z*ell k z+leafP j i k z*(D i (ell k) z+ell i z*ell k z))

def leafQuarter (j : Fin 13) (z : SourceCoordinateSlice) : ℂ :=
  (1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,D i (D k (leafP j i k)) z

theorem leafHalf_original (j : Fin 13) (z : physicalChart) :
    leafHalf j z.val=(nativeHalfCorrection j z.val : ℂ) := by
  unfold leafHalf nativeHalfCorrection
  simp only [D_leafP_real,ell_real,D_ell_real,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  unfold leafP DR
  push_cast
  ring

theorem leafQuarter_original (j : Fin 13) (z : physicalChart) :
    leafQuarter j z.val=(nativeWeylCorrection j z.val : ℂ) := by
  unfold leafQuarter nativeWeylCorrection
  simp only [DD_leafP_real,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat,Complex.ofReal_sum]
  rfl

private theorem reorder (a : Fin 100 → Fin 100 → Fin 13 → ℂ) :
    (∑ i : Fin 100,∑ k : Fin 100,∑ j : Fin 13,a i k j)=
      ∑ j : Fin 13,∑ i : Fin 100,∑ k : Fin 100,a i k j := by
  calc
    _=∑ i : Fin 100,∑ j : Fin 13,∑ k : Fin 100,a i k j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _=_ := by rw [Finset.sum_comm]

theorem sourceHalfPotential_extraction (z : physicalChart) :
    tensorHalfPotential z.val=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*leafHalf j z.val := by
  have term (i k : Fin 100) : D i (P i k) z.val*ell k z.val+
      P i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
        (D i (leafP j i k) z.val*ell k z.val+
          leafP j i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)) := by
    rw [sourceP_D_timeTensor,D_timeTensor,sourceP_timeTensor]
    unfold timeTensor
    simp only [Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ i : Fin 100,∑ k : Fin 100,(D i (P i k) z.val*ell k z.val+
    P i k z.val*(D i (ell k) z.val+ell i z.val*ell k z.val)))=_
  simp only [term]
  rw [reorder]
  simp only [leafHalf,Finset.mul_sum]

theorem sourceQuarter_extraction (z : physicalChart) :
    tensorWeylCorrection z.val=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*leafQuarter j z.val := by
  change (1/4 : ℂ)*(∑ i : Fin 100,∑ k : Fin 100,D i (D k (P i k)) z.val)=_
  simp only [sourceP_DD_timeTensor,DD_timeTensor]
  rw [reorder]
  simp only [leafQuarter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sourceWeylZero_originalLeaves (z : physicalChart) :
    sourceWeylZero z.val=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
        (originalZeroLeaves z.val (Fin.castSucc j) : ℂ) := by
  have classical := original_zeroShiftClassical z
  rw [scalar_potential_source z,magnetic_potential_source z] at classical
  unfold sourceWeylZero
  rw [sourceHalfPotential_extraction,sourceQuarter_extraction]
  have potential : ((potential z.val+GaussCoframeForm.volumePotential z.val : ℝ) : ℂ)=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
        (originalClassicalLeaves z.val j : ℂ) := by
    have read:=congrArg (fun r : ℝ => (r : ℂ)) classical
    simp only [potential,Complex.ofReal_sum,Complex.ofReal_mul] at read ⊢
    exact read.symm
  rw [potential]
  simp only [leafHalf_original,leafQuarter_original,originalZeroLeaves,Fin.snoc_castSucc,
    Complex.ofReal_add,mul_add,Finset.sum_add_distrib]
  ring

theorem originalHalfVacuum_originalZeroLeaves (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      sourceFourTermWeyl f z.val+
        (∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
          (originalZeroLeaves z.val (Fin.castSucc j) : ℂ))*f z.val := by
  rw [originalHalfVacuum_fourTermWeyl,sourceWeylZero_originalLeaves]

theorem originalZeroLeaves_Y_vacuum (z : SourceCoordinateSlice) :
    originalZeroLeaves z (Fin.last 13)=0 := by
  simp only [originalZeroLeaves,Fin.snoc_last]

end LowEnergy.PreparationVacuumWeylOrdering
