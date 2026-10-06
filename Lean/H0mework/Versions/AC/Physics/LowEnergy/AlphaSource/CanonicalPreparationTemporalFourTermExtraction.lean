import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylZeroReplay

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumDensityTrace
open PreparationVacuumEnergyTail PreparationVacuumFactor PreparationVacuumWeylOrdering
open scoped BigOperators ContDiff Topology

def leafFourTermWeyl (j : Fin 13) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -(1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,
    (leafP j i k z*D i (D k f) z+D i (fun w => leafP j i k w*D k f w) z+
      D k (fun w => leafP j i k w*D i f w) z+D i (D k (fun w => leafP j i k w*f w)) z)

def timeFourTermWeyl (n : ℝ) (b : Fin 3 → ℝ) (f : Profile) (z : SourceCoordinateSlice) : ℂ :=
  -(1/4 : ℂ)*∑ i : Fin 100,∑ k : Fin 100,
    (timeTensor n b i k z*D i (D k f) z+D i (fun w => timeTensor n b i k w*D k f w) z+
      D k (fun w => timeTensor n b i k w*D i f w) z+
        D i (D k (fun w => timeTensor n b i k w*f w)) z)

private theorem D_weighted (r : Fin 100) (weights : Fin 13 → ℂ) (a : Fin 13 → Profile)
    (z : SourceCoordinateSlice) (smooth : ∀ j, DifferentiableAt ℝ (a j) z) :
    D r (fun w => ∑ j : Fin 13,weights j*a j w) z=
      ∑ j : Fin 13,weights j*D r (a j) z := by
  change fderiv ℝ (fun w => ∑ j : Fin 13,weights j*a j w) z (rawDirection r)=_
  rw [fderiv_fun_sum (fun j _ => (smooth j).const_mul (weights j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_const_mul (smooth j)]
  rfl

theorem D_timeProduct (n : ℝ) (b : Fin 3 → ℝ) (i k r : Fin 100) (g : Profile)
    (z : physicalChart) (smooth : ContDiffAt ℝ ∞ g z.val) :
    D r (fun w => timeTensor n b i k w*g w) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        D r (fun w => leafP j i k w*g w) z.val := by
  have equal : (fun w => timeTensor n b i k w*g w)=
      (fun w => ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*(leafP j i k w*g w)) := by
    funext w
    simp only [timeTensor,Finset.sum_mul,mul_assoc]
  rw [equal]
  exact D_weighted r _ _ z.val (fun j => ((leafP_smooth j i k z).mul smooth).differentiableAt (by simp))

theorem DD_timeProduct (n : ℝ) (b : Fin 3 → ℝ) (i k r s : Fin 100) (f : ScalarTest)
    (z : physicalChart) :
    D r (D s (fun w => timeTensor n b i k w*f w)) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        D r (D s (fun w => leafP j i k w*f w)) z.val := by
  have equal : D s (fun w => timeTensor n b i k w*f w)=ᶠ[𝓝 z.val]
      (fun w => ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        D s (fun u => leafP j i k u*f u) w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact D_timeProduct n b i k s f ⟨w,hw⟩ f.contDiff.contDiffAt
  have read := congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq
  change D r (D s (fun w => timeTensor n b i k w*f w)) z.val=
    D r (fun w => ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
      D s (fun u => leafP j i k u*f u) w) z.val at read
  rw [read]
  exact D_weighted r _ _ z.val (fun j =>
    (D_smooth s ((leafP_smooth j i k z).mul f.contDiff.contDiffAt)).differentiableAt (by simp))

theorem timeFourTermWeyl_extraction (n : ℝ) (b : Fin 3 → ℝ) (f : ScalarTest)
    (z : physicalChart) : timeFourTermWeyl n b f z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*leafFourTermWeyl j f z.val := by
  have term (i k : Fin 100) :
      timeTensor n b i k z.val*D i (D k f) z.val+
        D i (fun w => timeTensor n b i k w*D k f w) z.val+
        D k (fun w => timeTensor n b i k w*D i f w) z.val+
        D i (D k (fun w => timeTensor n b i k w*f w)) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*
        (leafP j i k z.val*D i (D k f) z.val+D i (fun w => leafP j i k w*D k f w) z.val+
          D k (fun w => leafP j i k w*D i f w) z.val+D i (D k (fun w => leafP j i k w*f w)) z.val) := by
    rw [D_timeProduct n b i k i (D k f) z (D_smooth k f.contDiff.contDiffAt),
      D_timeProduct n b i k k (D i f) z (D_smooth i f.contDiff.contDiffAt),DD_timeProduct]
    simp only [timeTensor,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold timeFourTermWeyl
  simp only [term]
  have reindex (a : Fin 100 → Fin 100 → Fin 13 → ℂ) :
      (∑ i : Fin 100,∑ k : Fin 100,∑ j : Fin 13,a i k j)=
        ∑ j : Fin 13,∑ i : Fin 100,∑ k : Fin 100,a i k j := by
    calc
      _=∑ i : Fin 100,∑ j : Fin 13,∑ k : Fin 100,a i k j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _=_ := by rw [Finset.sum_comm]
  rw [reindex]
  simp only [leafFourTermWeyl,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem sourceProduct_D (i k r : Fin 100) (g : Profile) (z : physicalChart) :
    D r (fun w => P i k w*g w) z.val=
      D r (fun w => timeTensor (sourceTime 0) 0 i k w*g w) z.val := by
  have equal : (fun w => P i k w*g w)=ᶠ[𝓝 z.val]
      (fun w => timeTensor (sourceTime 0) 0 i k w*g w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    rw [sourceP_timeTensor i k ⟨w,hw⟩]
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq

theorem sourceFourTermWeyl_timeExtraction (f : ScalarTest) (z : physicalChart) :
    sourceFourTermWeyl f z.val=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*leafFourTermWeyl j f z.val := by
  have second (i k : Fin 100) : D i (D k (fun w => P i k w*f w)) z.val=
      D i (D k (fun w => timeTensor (sourceTime 0) 0 i k w*f w)) z.val := by
    have equal : D k (fun w => P i k w*f w)=ᶠ[𝓝 z.val]
        D k (fun w => timeTensor (sourceTime 0) 0 i k w*f w) := by
      filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
      exact sourceProduct_D i k k f ⟨w,hw⟩
    exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection i)) equal.fderiv_eq
  have read : sourceFourTermWeyl f z.val=timeFourTermWeyl (sourceTime 0) 0 f z.val := by
    unfold sourceFourTermWeyl timeFourTermWeyl
    simp only [sourceP_timeTensor,sourceProduct_D,second]
  rw [read,timeFourTermWeyl_extraction]

theorem originalHalfVacuum_operatorExtraction (f : ScalarTest) (z : physicalChart) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      ∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
        (leafFourTermWeyl j f z.val+(originalZeroLeaves z.val (Fin.castSucc j) : ℂ)*f z.val) := by
  rw [originalHalfVacuum_originalZeroLeaves,sourceFourTermWeyl_timeExtraction]
  simp only [Finset.sum_mul,mul_add,Finset.sum_add_distrib,mul_assoc]

end LowEnergy.PreparationVacuumTemporalOrdering
