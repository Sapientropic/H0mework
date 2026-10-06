import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerAssemblyTensor

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerAssembly
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy GaussCoreDifferential
open PreparationScalarCoordinates PreparationVacuumLowerLeaves PreparationVacuumLowerTensorBudget
open PreparationVacuumLowerCorrections PreparationVacuumRationalW PreparationVacuumWeylOrdering
open PreparationVacuumEnergyTail PreparationVacuumMoyalSymmetry
open scoped BigOperators ContDiff Topology Matrix

def half {a : ℕ} (D : Fin a → Configuration) (L : Fin a → Configuration → ℝ)
    (F : Configuration → Fin a → Fin a → ℝ) (z : Configuration) : ℝ :=
  ∑ i,∑ k,(F z i k*(L i z*L k z+fderiv ℝ (L k) z (D i))+
    fderiv ℝ (fun w => F w i k) z (D i)*L k z)

def quarter {a : ℕ} (D : Fin a → Configuration)
    (F : Configuration → Fin a → Fin a → ℝ) (z : Configuration) : ℝ :=
  (1/4 : ℝ)*∑ i,∑ k,fderiv ℝ (fun w => fderiv ℝ (fun t => F t i k) w (D k)) z (D i)

theorem finite_D {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → Configuration → ℝ)
    (z D : Configuration) (smooth : ∀ j,ContDiffAt ℝ ∞ (F j) z) :
    fderiv ℝ (fun w => ∑ j,c j*F j w) z D=∑ j,c j*fderiv ℝ (F j) z D := by
  rw [fderiv_fun_sum (fun j _ => (contDiffAt_const.mul (smooth j)).differentiableAt (by simp))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have derivative : fderiv ℝ (fun w => c j*F j w) z=c j • fderiv ℝ (F j) z :=
    ((smooth j).differentiableAt (by simp)).hasFDerivAt.const_mul (c j) |>.fderiv
  rw [derivative]
  rfl

theorem finite_DD {ι : Type} [Fintype ι] (c : ι → ℝ) (F : ι → Configuration → ℝ)
    (z : physicalChart) (D E : Configuration) (smooth : ∀ j,∀ w : physicalChart,ContDiffAt ℝ ∞ (F j) w.val) :
    fderiv ℝ (fun w => fderiv ℝ (fun t => ∑ j,c j*F j t) w E) z.val D=
      ∑ j,c j*fderiv ℝ (fun w => fderiv ℝ (F j) w E) z.val D := by
  have same : (fun w => fderiv ℝ (fun t => ∑ j,c j*F j t) w E)=ᶠ[𝓝 z.val]
      (fun w => ∑ j,c j*fderiv ℝ (F j) w E) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact finite_D c F w E (fun j => smooth j ⟨w,hw⟩)
  rw [same.fderiv_eq]
  exact finite_D c (fun j w => fderiv ℝ (F j) w E) z.val D
    (fun j => ((smooth j z).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

private theorem sum_rotate {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    (∑ i,∑ k,∑ j,f i k j)=∑ j,∑ i,∑ k,f i k j := by
  calc
    _ = ∑ i,∑ j,∑ k,f i k j := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem half_sum {a : ℕ} {ι : Type} [Fintype ι] (D : Fin a → Configuration)
    (L : Fin a → Configuration → ℝ) (c : ι → ℝ) (F : ι → Configuration → Fin a → Fin a → ℝ)
    (smooth : ∀ j i k,∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w => F j w i k) z.val)
    (z : physicalChart) :
    half D L (fun w i k => ∑ j,c j*F j w i k) z.val=∑ j,c j*half D L (F j) z.val := by
  have derivative (i k : Fin a) := finite_D c (fun j w => F j w i k) z.val (D i) (fun j => smooth j i k z)
  unfold half
  simp only [derivative,Finset.sum_mul,←Finset.sum_add_distrib]
  have term (i k : Fin a) (j : ι) :
      c j*F j z.val i k*(L i z.val*L k z.val+fderiv ℝ (L k) z.val (D i))+
        c j*fderiv ℝ (fun w => F j w i k) z.val (D i)*L k z.val=
      c j*(F j z.val i k*(L i z.val*L k z.val+fderiv ℝ (L k) z.val (D i))+
        fderiv ℝ (fun w => F j w i k) z.val (D i)*L k z.val) := by ring
  simp_rw [term]
  rw [sum_rotate]
  simp only [Finset.mul_sum]

theorem quarter_sum {a : ℕ} {ι : Type} [Fintype ι] (D : Fin a → Configuration)
    (c : ι → ℝ) (F : ι → Configuration → Fin a → Fin a → ℝ)
    (smooth : ∀ j i k,∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w => F j w i k) z.val)
    (z : physicalChart) :
    quarter D (fun w i k => ∑ j,c j*F j w i k) z.val=∑ j,c j*quarter D (F j) z.val := by
  unfold quarter
  simp only [finite_DD c (fun j w => F j w _ _) z _ _ (fun j w => smooth j _ _ w)]
  rw [sum_rotate]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem half_congr {a : ℕ} (D : Fin a → Configuration) (L : Fin a → Configuration → ℝ)
    (F G : Configuration → Fin a → Fin a → ℝ)
    (same : ∀ z : physicalChart,∀ i k,F z.val i k=G z.val i k) (z : physicalChart) :
    half D L F z.val=half D L G z.val := by
  have derivative (i k : Fin a) : fderiv ℝ (fun w => F w i k) z.val=fderiv ℝ (fun w => G w i k) z.val := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact same ⟨w,hw⟩ i k
  simp only [half,same z,derivative]

theorem quarter_congr {a : ℕ} (D : Fin a → Configuration) (F G : Configuration → Fin a → Fin a → ℝ)
    (same : ∀ z : physicalChart,∀ i k,F z.val i k=G z.val i k) (z : physicalChart) :
    quarter D F z.val=quarter D G z.val := by
  have derivative (i k : Fin a) :
      (fun w => fderiv ℝ (fun t => F t i k) w (D k))=ᶠ[𝓝 z.val]
      (fun w => fderiv ℝ (fun t => G t i k) w (D k)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    have first : (fun t => F t i k)=ᶠ[𝓝 w](fun t => G t i k) := by
      filter_upwards [physicalChart.isOpen.mem_nhds hw] with t ht
      exact same ⟨t,ht⟩ i k
    rw [first.fderiv_eq]
  unfold quarter
  simp only [(derivative _ _).fderiv_eq]

def blockTensor (n : ℝ) (F : NativeTensor) (z : Configuration) (i k : Fin 100) : ℝ :=
  Fin.addCases (fun a : Fin 6 => Fin.addCases (fun c : Fin 6 => n*K a c z)
      (fun _ : Fin 94 => 0) k)
    (fun a : Fin 94 => Fin.addCases (fun _ : Fin 6 => 0) (fun c : Fin 94 => F z a c) k) i

theorem block_left (n : ℝ) (F : NativeTensor) (i k : Fin 6) :
    (fun z => blockTensor n F z (Fin.castAdd 94 i) (Fin.castAdd 94 k))=fun z => n*K i k z := by
  funext z; simp [blockTensor]
theorem block_cross (n : ℝ) (F : NativeTensor) (i : Fin 6) (k : Fin 94) :
    (fun z => blockTensor n F z (Fin.castAdd 94 i) (Fin.natAdd 6 k))=fun _ => 0 := by
  funext z; simp [blockTensor]
theorem block_cross' (n : ℝ) (F : NativeTensor) (i : Fin 94) (k : Fin 6) :
    (fun z => blockTensor n F z (Fin.natAdd 6 i) (Fin.castAdd 94 k))=fun _ => 0 := by
  funext z; simp [blockTensor]
theorem block_right (n : ℝ) (F : NativeTensor) (i k : Fin 94) :
    (fun z => blockTensor n F z (Fin.natAdd 6 i) (Fin.natAdd 6 k))=fun z => F z i k := by
  funext z; simp [blockTensor]

theorem half_block (n : ℝ) (F : NativeTensor) (z : Configuration) :
    half rawDirection rawHalfLog (blockTensor n F) z=coframeHalf100 n z+nativeHalf F z := by
  unfold half coframeHalf100 nativeHalf
  simp only [Fin.sum_univ_add (a:=6) (b:=94),block_left,block_cross,block_cross',block_right,
    tensor_left,tensor_cross,tensor_right,fderiv_const_apply,zero_apply,
    zero_mul,add_zero,Finset.sum_const_zero]
  simp only [blockTensor,Fin.addCases_left,Fin.addCases_right,zero_mul,add_zero,zero_add,Finset.sum_const_zero]

theorem quarter_block (n : ℝ) (F : NativeTensor) (z : Configuration) :
    quarter rawDirection (blockTensor n F) z=coframeQuarter100 n z+nativeQuarter F z := by
  unfold quarter coframeQuarter100 nativeQuarter
  simp only [Fin.sum_univ_add (a:=6) (b:=94),block_left,block_cross,block_cross',block_right,
    tensor_left,tensor_cross,tensor_right,fderiv_const_apply,zero_apply,
    Finset.sum_const_zero,add_zero,zero_add,mul_add]

def weightedRho (n : ℝ) (b : Fin 3 → ℝ) : NativeTensor := fun z i k =>
  ∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) z

theorem weighted_tensor_block (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (z : physicalChart) (i k : Fin 100) :
    (∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j i k z.val)=
      blockTensor n (weightedRho n b) z.val i k := by
  rw [weighted_raw_tensor n b time]
  induction i using Fin.addCases (m:=6) (n:=94) with
  | left i => simp [wholeTensor,blockTensor]
  | right i =>
    induction k using Fin.addCases (m:=6) (n:=94) with
    | left k => simp [wholeTensor,blockTensor]
    | right k =>
      have read := weighted_raw_tensor n b time (Fin.natAdd 6 i) (Fin.natAdd 6 k) z
      simpa only [wholeTensor,blockTensor,Fin.addCases_right,weightedRho] using read.symm

theorem whole_half_split (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*nativeHalfCorrection j z.val)=
      coframeHalf100 n z.val+∑ j : Fin 13,originalTemporalWeights n b j*originalRhoHalfLeaf j z.val := by
  have linear := half_sum (a:=100) rawDirection rawHalfLog (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j i k w)
    (fun j i k w => rawPrincipalCoefficient_smooth j i k w) z
  have congruent := half_congr (a:=100) rawDirection rawHalfLog
    (fun w i k => ∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j i k w)
    (blockTensor n (weightedRho n b)) (weighted_tensor_block n b time) z
  have reduced := half_block n (weightedRho n b) z.val
  have rho := half_sum (a:=94) (fun i => rawDirection (Fin.natAdd 6 i))
    (fun i => rawHalfLog (Fin.natAdd 6 i)) (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) w)
    (fun j i k w => rawPrincipalCoefficient_smooth j _ _ w) z
  have rhoRead : nativeHalf (weightedRho n b) z.val=
      ∑ j : Fin 13,originalTemporalWeights n b j*originalRhoHalfLeaf j z.val := by
    simpa only [half,nativeHalf,originalRhoHalfLeaf,weightedRho] using rho
  have output := linear.symm.trans (congruent.trans (reduced.trans (congrArg (fun r : ℝ => coframeHalf100 n z.val+r) rhoRead)))
  simpa only [half,nativeHalfCorrection] using output

theorem whole_quarter_split (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*nativeWeylCorrection j z.val)=
      coframeQuarter100 n z.val+∑ j : Fin 13,originalTemporalWeights n b j*originalRhoQuarterLeaf j z.val := by
  have linear := quarter_sum (a:=100) rawDirection (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j i k w)
    (fun j i k w => rawPrincipalCoefficient_smooth j i k w) z
  have congruent := quarter_congr (a:=100) rawDirection
    (fun w i k => ∑ j : Fin 13,originalTemporalWeights n b j*rawPrincipalCoefficient j i k w)
    (blockTensor n (weightedRho n b)) (weighted_tensor_block n b time) z
  have reduced := quarter_block n (weightedRho n b) z.val
  have rho := quarter_sum (a:=94) (fun i => rawDirection (Fin.natAdd 6 i)) (originalTemporalWeights n b)
    (fun j w i k => rawPrincipalCoefficient j (Fin.natAdd 6 i) (Fin.natAdd 6 k) w)
    (fun j i k w => rawPrincipalCoefficient_smooth j _ _ w) z
  have rhoRead : nativeQuarter (weightedRho n b) z.val=
      ∑ j : Fin 13,originalTemporalWeights n b j*originalRhoQuarterLeaf j z.val := by
    simpa only [quarter,nativeQuarter,originalRhoQuarterLeaf,weightedRho] using rho
  have output := linear.symm.trans (congruent.trans (reduced.trans (congrArg (fun r : ℝ => coframeQuarter100 n z.val+r) rhoRead)))
  simpa only [quarter,nativeWeylCorrection] using output

theorem whole_correction_split (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (z : physicalChart) :
    (∑ j : Fin 13,originalTemporalWeights n b j*(nativeHalfCorrection j z.val+nativeWeylCorrection j z.val))=
      n*(5/(4*volume z.val))+
        ∑ j : Fin 13,originalTemporalWeights n b j*(originalRhoHalfLeaf j z.val+originalRhoQuarterLeaf j z.val) := by
  simp only [mul_add,Finset.sum_add_distrib]
  rw [whole_half_split n b time,whole_quarter_split n b time,coframeHalf100_read,coframeQuarter100_read]
  rw [←coframe_cancellation z]
  ring

end LowEnergy.PreparationVacuumLowerAssembly
