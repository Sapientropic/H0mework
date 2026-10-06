import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerCoframeCancellation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerTensorBudget
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy PreparationScalarCoordinates PreparationPhaseScalar
open PreparationVacuumLowerLeaves CanonicalPreparationMomentum PreparationActualFactor
open PreparationVacuumLowerTensor PreparationVacuumTemporalOrdering
open PreparationVacuumCanonicalMoyal PreparationVacuumMoyalSymmetry
open scoped BigOperators ContDiff Topology Matrix

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

local notation "D" => GaussCoframeCore.coframeDirection

theorem rawCovector_read (i : Fin 100) (z : Configuration) : rawCovector i z=fullCoordinates z i := by
  simp [rawCovector,nativeCovector_apply]

theorem rawDirection_coframe (i : Fin 6) : rawDirection (Fin.castAdd 94 i)=D i := by
  apply fullCoordinates.injective
  rw [coframe_direction_coordinates]
  simp only [rawDirection,ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem rawCovector_coframe_left (i a : Fin 6) : rawCovector (Fin.castAdd 94 i) (D a)=if a=i then 1 else 0 := by
  rw [rawCovector_read,coframe_direction_coordinates]
  simp [coframeSlot,Pi.single_apply,Fin.ext_iff,eq_comm]

theorem rawCovector_coframe_right (i : Fin 94) (a : Fin 6) : rawCovector (Fin.natAdd 6 i) (D a)=0 := by
  rw [rawCovector_read,coframe_direction_coordinates]
  have ne : coframeSlot a≠Fin.natAdd 6 i := by
    intro h
    have eq := congrArg Fin.val h
    change a.val=6+i.val at eq
    omega
  simp [ne]

def coframeTensor (n : ℝ) (i k : Fin 100) (z : Configuration) : ℝ :=
  Fin.addCases (fun a : Fin 6 => Fin.addCases (fun c : Fin 6 => n*K a c z)
    (fun _ : Fin 94 => 0) k) (fun _ : Fin 94 => 0) i

theorem tensor_left (n : ℝ) (i k : Fin 6) :
    coframeTensor n (Fin.castAdd 94 i) (Fin.castAdd 94 k)=(fun z => n*K i k z) := by funext z; simp [coframeTensor]
theorem tensor_cross (n : ℝ) (i : Fin 6) (k : Fin 94) :
    coframeTensor n (Fin.castAdd 94 i) (Fin.natAdd 6 k)=(fun _ => 0) := by funext z; simp [coframeTensor]
theorem tensor_right (n : ℝ) (i : Fin 94) (k : Fin 100) :
    coframeTensor n (Fin.natAdd 6 i) k=(fun _ => 0) := by funext z; simp [coframeTensor]

/-- This is exactly the coframe SourcePair branch of the original Qtime tensor. -/
theorem actualTime_coframe_tensor (n : ℝ) (b : Fin 3 → ℝ) (i k : Fin 100) (z : Configuration) :
    (∑ a : Fin 6,∑ c : Fin 6,
      actualTimePairCoefficient n b (Sum.inr (Sum.inr (a,c))) z*
        rawCovector i (sourceLeft (Sum.inr (Sum.inr (a,c))) z)*
        rawCovector k (sourceRight (Sum.inr (Sum.inr (a,c))) z))=coframeTensor n i k z := by
  induction i using Fin.addCases (m:=6) (n:=94) with
  | left i =>
    induction k using Fin.addCases (m:=6) (n:=94) with
    | left k =>
      simp only [sourceLeft,sourceRight,rawCovector_coframe_left,actualTimePairCoefficient,tensor_left]
      simp only [mul_ite,mul_one,mul_zero]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rw [K_original]
      ring
    | right k => simp [sourceRight,rawCovector_coframe_right,tensor_cross]
  | right i => simp [sourceLeft,rawCovector_coframe_right,tensor_right]

theorem original_coframe_log (i : Fin 6) (z : physicalChart) :
    rawHalfLog (Fin.castAdd 94 i) z.val=L i z.val := by
  rw [PreparationVacuumDensityBudget.actual_rawHalfLog_coframe]
  have c0 : PreparationVacuumDensityBudget.coordinate 0 z.val=z.val.1 0 := rfl
  have c2 : PreparationVacuumDensityBudget.coordinate 2 z.val=z.val.1 2 := rfl
  have c5 : PreparationVacuumDensityBudget.coordinate 5 z.val=z.val.1 5 := rfl
  have h0 := z.property.1.ne'
  have h2 := z.property.2.1.ne'
  have h5 := z.property.2.2.1.ne'
  fin_cases i <;>
    norm_num [PreparationVacuumDensityBudget.coframeLog,c0,c2,c5,L,halfLogVolume,
      volumeDerivative,GaussCoframeCore.coframeDirection,EuclideanSpace.single,
      PiLp.single_apply,Fin.ext_iff,volume] <;>
    field_simp [h0,h2,h5]

theorem original_coframe_log_derivative (i k : Fin 6) (z : physicalChart) :
    fderiv ℝ (rawHalfLog (Fin.castAdd 94 k)) z.val (D i)=
      fderiv ℝ (L k) z.val (D i) := by
  have same : rawHalfLog (Fin.castAdd 94 k)=ᶠ[𝓝 z.val]L k := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact original_coframe_log k ⟨w,hw⟩
  rw [same.fderiv_eq]

private theorem scale_derivative (c : ℝ) (f : Configuration → ℝ) (z d : Configuration)
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun w => c*f w) z d=c*fderiv ℝ f z d :=
  congrArg (fun F : Configuration →L[ℝ] ℝ => F d) (hf.hasFDerivAt.const_mul c).fderiv

theorem K_scale_second (n : ℝ) (i j : Fin 6) (z : physicalChart) :
    fderiv ℝ (fun w => fderiv ℝ (fun t => n*K i j t) w (D j)) z.val (D i)=
      n*fderiv ℝ (fun w => fderiv ℝ (K i j) w (D j)) z.val (D i) := by
  have same : (fun w => fderiv ℝ (fun t => n*K i j t) w (D j))=ᶠ[𝓝 z.val]
      (fun w => n*fderiv ℝ (K i j) w (D j)) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
    exact scale_derivative n (K i j) w (D j) ((K_smooth i j ⟨w,hw⟩).differentiableAt (by simp))
  rw [same.fderiv_eq]
  exact scale_derivative n _ _ _
    ((((K_smooth i j z).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp))

def coframeHalf100 (n : ℝ) (z : Configuration) : ℝ :=
  ∑ i : Fin 100,∑ k : Fin 100,
    (coframeTensor n i k z*(rawHalfLog i z*rawHalfLog k z+fderiv ℝ (rawHalfLog k) z (rawDirection i))+
      fderiv ℝ (coframeTensor n i k) z (rawDirection i)*rawHalfLog k z)

def coframeQuarter100 (n : ℝ) (z : Configuration) : ℝ :=
  (1/4 : ℝ)*∑ i : Fin 100,∑ k : Fin 100,
    fderiv ℝ (fun w => fderiv ℝ (coframeTensor n i k) w (rawDirection k)) z (rawDirection i)

theorem coframeHalf100_read (n : ℝ) (z : physicalChart) :
    coframeHalf100 n z.val=n*coframeHalf z.val := by
  unfold coframeHalf100
  simp only [Fin.sum_univ_add (a:=6) (b:=94),tensor_left,tensor_cross,tensor_right,
    fderiv_const_apply,zero_apply,zero_mul,add_zero,Finset.sum_const_zero,
    rawDirection_coframe,original_coframe_log,original_coframe_log_derivative]
  unfold coframeHalf
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [scale_derivative n (K i k) _ _ ((K_smooth i k z).differentiableAt (by simp))]
  ring

theorem coframeQuarter100_read (n : ℝ) (z : physicalChart) :
    coframeQuarter100 n z.val=n*coframeQuarter z.val := by
  unfold coframeQuarter100
  simp only [Fin.sum_univ_add (a:=6) (b:=94),tensor_left,tensor_cross,tensor_right,
    fderiv_const_apply,zero_apply,Finset.sum_const_zero,add_zero,rawDirection_coframe,K_scale_second]
  unfold coframeQuarter
  simp only [←Finset.mul_sum]
  ring

def actualCoframeVacuumZero (n : ℝ) (z : Configuration) : ℝ :=
  coframeHalf100 n z+coframeQuarter100 n z+(n/sourceTime 0)*GaussCoframeForm.volumePotential z

theorem actualCoframeVacuumZero_formula (n : ℝ) (z : physicalChart) :
    actualCoframeVacuumZero n z.val=n*(5/(4*volume z.val)+3*volume z.val) := by
  unfold actualCoframeVacuumZero
  rw [coframeHalf100_read,coframeQuarter100_read,←mul_add,coframe_cancellation]
  unfold GaussCoframeForm.volumePotential
  field_simp [source_time_nonzero]


def vacuumArray (m : ℕ) : ℝ := (5/4 : ℝ)*PreparationVacuumCoframeBudget.inverseVolumeArray m+
  3*PreparationVacuumCoframeBudget.volumeArray m

def originalCf0VacuumArray (m : ℕ) : ℝ := 2*vacuumArray m

def originalCf0ScalarArray (m : ℕ) : ℝ :=
  2*((((3*504^2+18*504+20 : ℝ)/16))*PreparationVacuumCoframeBudget.inverseVolumeArray m+
    3*PreparationVacuumCoframeBudget.volumeArray m)

def actualCoframeZeroSymbol (n : ℝ) : Symbol := fun x => actualCoframeVacuumZero n (fullCoordinates.symm x.1)

private theorem volume_smooth_at (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    ContDiffAt ℝ ∞ PreparationVacuumCoframeBudget.sourceVolume x := by
  have smooth := PreparationVacuumCoframeBudget.entryValue_smooth
    PreparationVacuumCoframeBudget.sourceVolumeEntry PreparationVacuumCoframeBudget.sourceVolume_poles
  have same : PreparationVacuumCoframeBudget.entryValue PreparationVacuumCoframeBudget.sourceVolumeEntry=
      PreparationVacuumCoframeBudget.sourceVolume := funext PreparationVacuumCoframeBudget.sourceVolume_readback
  rw [same] at smooth
  exact (smooth x (PreparationVacuumCoframeBudget.sourceBox_guards x box).1).contDiffAt
    (PreparationVacuumCoframeBudget.coframeDomain_open.mem_nhds (PreparationVacuumCoframeBudget.sourceBox_guards x box).1)

private theorem inverseVolume_smooth_at (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    ContDiffAt ℝ ∞ PreparationVacuumCoframeBudget.sourceVolumeInverse x := by
  have smooth := PreparationVacuumCoframeBudget.entryValue_smooth
    PreparationVacuumCoframeBudget.sourceInverseVolumeEntry PreparationVacuumCoframeBudget.sourceInverseVolume_poles
  have same : PreparationVacuumCoframeBudget.entryValue PreparationVacuumCoframeBudget.sourceInverseVolumeEntry=
      PreparationVacuumCoframeBudget.sourceVolumeInverse := funext PreparationVacuumCoframeBudget.sourceInverseVolume_readback
  rw [same] at smooth
  exact (smooth x (PreparationVacuumCoframeBudget.sourceBox_guards x box).1).contDiffAt
    (PreparationVacuumCoframeBudget.coframeDomain_open.mem_nhds (PreparationVacuumCoframeBudget.sourceBox_guards x box).1)

private theorem cjet_scale (c : ℝ) (f : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (smooth : ContDiffAt ℝ ∞ f x) : jet m (fun y => c*f y) w x=c*jet m f w x :=
  PreparationVacuumCoframeBudget.jet_scale c f m w x smooth

private theorem cjet_add (f g : Symbol) (m : ℕ) (w : Word m) (x : Phase)
    (fs : ContDiffAt ℝ ∞ f x) (gs : ContDiffAt ℝ ∞ g x) :
    jet m (fun y => f y+g y) w x=jet m f w x+jet m g w x :=
  PreparationVacuumCoframeBudget.jet_add f g m w x fs gs

theorem actual_coframe_zero_jet (n : ℝ) (m : ℕ) (w : Word m) (x : Phase)
    (box : PreparationVacuumCoframeBudget.sourceBox x) :
    jet m (actualCoframeZeroSymbol n) w x=n*((5/4 : ℝ)*
      jet m PreparationVacuumCoframeBudget.sourceVolumeInverse w x+
      3*jet m PreparationVacuumCoframeBudget.sourceVolume w x) := by
  have physical : x∈originalPhysicalPhase := (phaseChart x.1 box).property
  have same : actualCoframeZeroSymbol n=ᶠ[𝓝 x](fun y => n*((5/4 : ℝ)*
      PreparationVacuumCoframeBudget.sourceVolumeInverse y+3*PreparationVacuumCoframeBudget.sourceVolume y)) := by
    filter_upwards [originalPhysicalPhase_open.mem_nhds physical] with y hy
    change actualCoframeVacuumZero n (fullCoordinates.symm y.1)=_
    have formula : actualCoframeVacuumZero n (fullCoordinates.symm y.1)=
        n*(5/(4*volume (fullCoordinates.symm y.1))+3*volume (fullCoordinates.symm y.1)) :=
      actualCoframeVacuumZero_formula n ⟨_,hy⟩
    rw [formula]
    unfold PreparationVacuumCoframeBudget.sourceVolumeInverse PreparationVacuumCoframeBudget.sourceVolume
    ring
  have fs := inverseVolume_smooth_at x box
  have gs := volume_smooth_at x box
  have first : ContDiffAt ℝ ∞ (fun y => (5/4 : ℝ)*PreparationVacuumCoframeBudget.sourceVolumeInverse y) x :=
    contDiffAt_const.mul fs
  have second : ContDiffAt ℝ ∞ (fun y => 3*PreparationVacuumCoframeBudget.sourceVolume y) x :=
    contDiffAt_const.mul gs
  have read : jet m (actualCoframeZeroSymbol n) w x=jet m (fun y => n*((5/4 : ℝ)*
      PreparationVacuumCoframeBudget.sourceVolumeInverse y+3*PreparationVacuumCoframeBudget.sourceVolume y)) w x :=
    PreparationVacuumCoframeBudget.jet_germ same m w
  rw [read,cjet_scale _ _ _ _ _ (first.add second),cjet_add _ _ _ _ _ first second,
    cjet_scale _ _ _ _ _ fs,cjet_scale _ _ _ _ _ gs]

theorem actual_coframe_zero_budget (n : ℝ) (m : ℕ) (w : Word m) (x : Phase)
    (box : PreparationVacuumCoframeBudget.sourceBox x) :
    |jet m (actualCoframeZeroSymbol n) w x| ≤ |n| *vacuumArray m := by
  rw [actual_coframe_zero_jet n m w x box,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg n)
  calc
    _ ≤ |(5/4 : ℝ)*jet m PreparationVacuumCoframeBudget.sourceVolumeInverse w x| +
        |3*jet m PreparationVacuumCoframeBudget.sourceVolume w x| := abs_add_le _ _
    _ = (5/4 : ℝ)*|jet m PreparationVacuumCoframeBudget.sourceVolumeInverse w x| +
        3*|jet m PreparationVacuumCoframeBudget.sourceVolume w x| := by rw [abs_mul,abs_mul]; norm_num
    _ ≤ vacuumArray m := add_le_add
      (mul_le_mul_of_nonneg_left (PreparationVacuumCoframeBudget.actual_inverseVolume_budget m w x box) (by norm_num))
      (mul_le_mul_of_nonneg_left (PreparationVacuumCoframeBudget.actual_volume_budget m w x box) (by norm_num))

theorem actual_coframe_p_zero (n : ℝ) (m : ℕ) (w : Word m) (x : Phase)
    (box : PreparationVacuumCoframeBudget.sourceBox x) (k : Fin m) (momentum : (w k).2=true) :
    jet m (actualCoframeZeroSymbol n) w x=0 := by
  have vi : jet m PreparationVacuumCoframeBudget.sourceVolumeInverse w x=0 :=
    PreparationVacuumCoframeBudget.actual_inverseVolume_p_zero m w x box k momentum
  have v : jet m PreparationVacuumCoframeBudget.sourceVolume w x=0 :=
    PreparationVacuumCoframeBudget.actual_volume_p_zero m w x box k momentum
  rw [actual_coframe_zero_jet n m w x box,vi,v]
  ring

theorem original_cf0_vacuum_budget (n : ℝ) (timeBound : |n| ≤ 2)
    (m : ℕ) (w : Word m) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    |jet m (actualCoframeZeroSymbol n) w x| ≤ originalCf0VacuumArray m :=
  (actual_coframe_zero_budget n m w x box).trans
    (mul_le_mul_of_nonneg_right timeBound (by unfold vacuumArray; positivity))

theorem original_cf0_scalar_admission (m : ℕ) : originalCf0VacuumArray m ≤ originalCf0ScalarArray m := by
  unfold originalCf0VacuumArray originalCf0ScalarArray vacuumArray
  have positive : (0 : ℝ) ≤ PreparationVacuumCoframeBudget.inverseVolumeArray m := Nat.cast_nonneg _
  nlinarith


theorem original_time_interval_bound (n : ℝ) (lower : sourceTime 0 ≤ n) (upper : n ≤ 2*sourceTime 0) : |n| ≤ 2 := by
  have positive : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have square : (sourceTime 0)^2=54/125 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_sq
  have small : sourceTime 0 ≤ 1 := by nlinarith
  rw [abs_of_nonneg (le_trans positive.le lower)]
  linarith

theorem original_Qtime_cf0_budget (n : ℝ) (b : Fin 3 → ℝ)
    (lower : sourceTime 0 ≤ n) (upper : n ≤ 2*sourceTime 0)
    (m : ℕ) (w : Word m) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    |jet m (actualCoframeZeroSymbol (PreparationVacuumEnergyTail.originalTemporalWeights n b 0)) w x|
      ≤ originalCf0ScalarArray m :=
  (original_cf0_vacuum_budget n (original_time_interval_bound n lower upper) m w x box).trans
    (original_cf0_scalar_admission m)

end LowEnergy.PreparationVacuumLowerTensorBudget
