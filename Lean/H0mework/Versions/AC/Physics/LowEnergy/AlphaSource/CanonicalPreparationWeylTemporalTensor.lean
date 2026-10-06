import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylOrdering

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOrdering
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential GaussNativeForm GaussDensityCore
open PreparationScalarCoordinates CanonicalPreparationCore PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensor PreparationVacuumDensityTrace
open PreparationVacuumEnergyTail
open scoped BigOperators ContDiff Topology

def leafP (j : Fin 13) (i k : Fin 100) (z : SourceCoordinateSlice) : ℂ :=
  rawPrincipalCoefficient j i k z

def timeTensor (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100) (z : SourceCoordinateSlice) : ℂ :=
  ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*leafP j i k z

theorem originalPrincipalLeaf_smooth (j : Fin 13) (p : Cotangent) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => originalPrincipalLeaves w p j) z.val := by
  have pull : ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => (w,p)) z.val :=
    contDiffAt_id.prodMk contDiffAt_const
  have a : ContDiffAt ℝ ∞ (fun w => A w p) z.val :=
    ContDiffAt.comp (g:=fun q : SourceCoordinateSlice × Cotangent => A q.1 q.2)
      (f:=fun w : SourceCoordinateSlice => (w,p)) z.val (A_smooth (z.val,p) z.property) pull
  have ss (i k : Fin 3) : ContDiffAt ℝ ∞ (fun w => S w p i k) z.val :=
    ContDiffAt.comp (g:=fun q : SourceCoordinateSlice × Cotangent => S q.1 q.2 i k)
      (f:=fun w : SourceCoordinateSlice => (w,p)) z.val (S_smooth (z.val,p) z.property i k) pull
  fin_cases j <;> first | exact a | exact ss _ _ | exact contDiffAt_const

theorem rawPrincipalCoefficient_smooth (j : Fin 13) (i k : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (rawPrincipalCoefficient j i k) z.val :=
  ((originalPrincipalLeaf_smooth j (rawCovector i+rawCovector k) z).sub
    (originalPrincipalLeaf_smooth j (rawCovector i) z) |>.sub
      (originalPrincipalLeaf_smooth j (rawCovector k) z)).div_const 2

theorem leafP_smooth (j : Fin 13) (i k : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (leafP j i k) z.val :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (rawPrincipalCoefficient_smooth j i k z)

theorem timeTensor_smooth (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100) (z : physicalChart) :
    ContDiffAt ℝ ∞ (timeTensor n b i k) z.val := by
  unfold timeTensor
  exact ContDiffAt.sum (fun j _ => contDiffAt_const.mul (leafP_smooth j i k z))

theorem originalTimeTensor_polarization (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100)
    (z : SourceCoordinateSlice) (timeNonzero : n≠0) (timelike : n^2-∑ r : Fin 3,b r^2≠0) :
    timeTensor n b i k z=
      (((timelikePrincipal z (rawCovector i+rawCovector k) n b-
        timelikePrincipal z (rawCovector i) n b-timelikePrincipal z (rawCovector k) n b)/2 : ℝ) : ℂ) := by
  have replay (p : Cotangent) := originalPrincipalTemporalReplay_native n b z p timeNonzero timelike
  unfold originalPrincipalTemporalReplay at replay
  rw [←replay (rawCovector i+rawCovector k),←replay (rawCovector i),←replay (rawCovector k)]
  unfold timeTensor leafP rawPrincipalCoefficient
  simp only [Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_mul]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem sourceP_timeTensor (i k : Fin 100) (z : physicalChart) :
    P i k z.val=timeTensor (sourceTime 0) 0 i k z.val := by
  calc
    _=(originalActionRawCoefficient i k z.val : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (sourceTensor_original i k z.val)
    _=(originalTemporalRawCoefficient i k z.val : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (originalActionRawCoefficient_readback i k z)
    _=_ := by simp only [originalTemporalRawCoefficient,timeTensor,leafP,
      Complex.ofReal_sum,Complex.ofReal_mul]

theorem D_timeTensor (n : ℝ) (b : Fin 3 → ℝ) (i k r : Fin 100) (z : physicalChart) :
    D r (timeTensor n b i k) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*D r (leafP j i k) z.val := by
  have smooth (j : Fin 13) : DifferentiableAt ℝ
      (fun w => (originalTemporalWeights n b j : ℂ)*leafP j i k w) z.val :=
    (contDiffAt_const.mul (leafP_smooth j i k z)).differentiableAt (by simp)
  unfold timeTensor D
  rw [fderiv_fun_sum (fun j _ => smooth j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have derivative : fderiv ℝ (fun w => (originalTemporalWeights n b j : ℂ)*leafP j i k w) z.val=
      (originalTemporalWeights n b j : ℂ) • fderiv ℝ (leafP j i k) z.val := by
    simpa only using! ((leafP_smooth j i k z).differentiableAt (by simp)).hasFDerivAt.const_mul
      (originalTemporalWeights n b j : ℂ) |>.fderiv
  rw [derivative]
  rfl

theorem DD_timeTensor (n : ℝ) (b : Fin 3 → ℝ) (i k r s : Fin 100) (z : physicalChart) :
    D r (D s (timeTensor n b i k)) z.val=
      ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*D r (D s (leafP j i k)) z.val := by
  have equal : D s (timeTensor n b i k)=ᶠ[𝓝 z.val]
      (fun w => ∑ j : Fin 13,(originalTemporalWeights n b j : ℂ)*D s (leafP j i k) w) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact D_timeTensor n b i k s ⟨w,hw⟩
  have smooth (j : Fin 13) : DifferentiableAt ℝ
      (fun w => (originalTemporalWeights n b j : ℂ)*D s (leafP j i k) w) z.val :=
    (contDiffAt_const.mul (D_smooth s (leafP_smooth j i k z))).differentiableAt (by simp)
  change fderiv ℝ (D s (timeTensor n b i k)) z.val (rawDirection r)=_
  rw [equal.fderiv_eq,fderiv_fun_sum (fun j _ => smooth j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have derivative : fderiv ℝ (fun w => (originalTemporalWeights n b j : ℂ)*D s (leafP j i k) w) z.val=
      (originalTemporalWeights n b j : ℂ) • fderiv ℝ (D s (leafP j i k)) z.val := by
    simpa only using! ((D_smooth s (leafP_smooth j i k z)).differentiableAt (by simp)).hasFDerivAt.const_mul
      (originalTemporalWeights n b j : ℂ) |>.fderiv
  rw [derivative]
  rfl

theorem sourceP_D_timeTensor (i k r : Fin 100) (z : physicalChart) :
    D r (P i k) z.val=D r (timeTensor (sourceTime 0) 0 i k) z.val := by
  have equal : P i k=ᶠ[𝓝 z.val] timeTensor (sourceTime 0) 0 i k := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact sourceP_timeTensor i k ⟨w,hw⟩
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq

theorem sourceP_DD_timeTensor (i k r s : Fin 100) (z : physicalChart) :
    D r (D s (P i k)) z.val=D r (D s (timeTensor (sourceTime 0) 0 i k)) z.val := by
  have equal : D s (P i k)=ᶠ[𝓝 z.val] D s (timeTensor (sourceTime 0) 0 i k) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact sourceP_D_timeTensor i k s ⟨w,hw⟩
  exact congrArg (fun L : SourceCoordinateSlice →L[ℝ] ℂ => L (rawDirection r)) equal.fderiv_eq

end LowEnergy.PreparationVacuumWeylOrdering
