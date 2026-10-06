import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerAssemblyCorrections
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerClassicalFamilies
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoefficientFormula
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationUniformEnergyFeed
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTimeCorrectionLeaves

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLowerAssembly
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussNativeEnergy PreparationScalarCoordinates PreparationActualFactor
open PreparationVacuumLowerLeaves PreparationVacuumLowerTensorBudget PreparationVacuumLowerCorrections
open PreparationVacuumTimeReader PreparationVacuumRationalW PreparationVacuumCanonicalMoyal
open PreparationVacuumEnergyTail PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol
open PreparationVacuumEngineSmooth PreparationVacuumEngineBudget PreparationVacuumCentralBudget
open PreparationVacuumCoframeBudget PreparationVacuumCoefficientBudget
open PreparationVacuumLowerClassical
open scoped BigOperators ContDiff Topology

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

def coframeCorrection (j : Fin 13) (z : Configuration) : ℝ := if j=0 then 5/(4*volume z) else 0

theorem weighted_coframe_correction (n : ℝ) (b : Fin 3 → ℝ) (z : Configuration) :
    (∑ j : Fin 13,originalTemporalWeights n b j*coframeCorrection j z)=n*(5/(4*volume z)) := by
  simp only [coframeCorrection,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rfl

theorem correction_leaf_formula (j : Fin 13) (z : physicalChart) :
    nativeHalfCorrection j z.val+nativeWeylCorrection j z.val=
      coframeCorrection j z.val+(originalRhoHalfLeaf j z.val+originalRhoQuarterLeaf j z.val) := by
  let f : Fin 13 → ℝ := fun k => nativeHalfCorrection k z.val+nativeWeylCorrection k z.val
  let g : Fin 13 → ℝ := fun k => coframeCorrection k z.val+
    (originalRhoHalfLeaf k z.val+originalRhoQuarterLeaf k z.val)
  have samples : sampleValues f=sampleValues g := by
    funext t
    have source := whole_correction_split N (pointShift t) (actual_point_box t) z
    change (∑ k : Fin 13,originalTemporalWeights N (pointShift t) k*f k)=_
    dsimp [sampleValues,actualWeights,g]
    simp only [mul_add,Finset.sum_add_distrib] at source ⊢
    rw [weighted_coframe_correction]
    simpa only [f,mul_add,Finset.sum_add_distrib] using source
  change f j=g j
  rw [←read_original_coefficients f j,←read_original_coefficients g j,samples]

def coframeCorrectionSymbol (j : Fin 13) : Symbol := fun x =>
  if j=0 then (5/4 : ℝ)*sourceVolumeInverse x else 0

def coframeCorrectionArray (j : Fin 13) (m : ℕ) : ℝ :=
  if j=0 then (5/4 : ℝ)*inverseVolumeArray m else 0

theorem coframe_correction_read (j : Fin 13) (x : Phase) :
    coframeCorrection j (fullCoordinates.symm x.1)=coframeCorrectionSymbol j x := by
  unfold coframeCorrection coframeCorrectionSymbol sourceVolumeInverse
  split_ifs <;> ring

theorem inverse_volume_smooth : SmoothSymbol sourceVolumeInverse := by
  intro x hx
  have native := volume_smooth.contDiffAt.comp x (nativePhase_smooth.contDiffAt.fst)
  exact (native.inv (volume_pos ⟨_,hx.1.1⟩).ne').contDiffWithinAt

theorem coframe_correction_smooth (j : Fin 13) : SmoothSymbol (coframeCorrectionSymbol j) := by
  unfold coframeCorrectionSymbol
  split_ifs
  · exact contDiffOn_const.mul inverse_volume_smooth
  · exact contDiffOn_const

theorem coframeCorrectionArray_nonnegative (j : Fin 13) (m : ℕ) : 0 ≤ coframeCorrectionArray j m := by
  unfold coframeCorrectionArray
  split_ifs <;> positivity

theorem coframe_correction_budget (j : Fin 13) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) : FiniteBound (coframeCorrectionSymbol j) M (coframeCorrectionArray j) x := by
  unfold coframeCorrectionSymbol coframeCorrectionArray
  by_cases h : j=0
  · have bound : FiniteBound sourceVolumeInverse M (fun m => (inverseVolumeArray m : ℝ)) x :=
      fun m _ w => actual_inverseVolume_budget m w x box
    have scaled := finite_scale (5/4 : ℝ) sourceVolumeInverse inverse_volume_smooth _ M x hx bound
    simpa only [h,if_true,abs_of_pos (by norm_num : (0 : ℝ)<5/4)] using scaled
  · intro m _ w
    simp only [h,if_false]
    simpa [constantArray] using (finite_constant 0 0 (by simp) M x m (by omega) w)

theorem reader_smooth (F : Fin 13 → Symbol) (samples : ∀ t,SmoothSymbol (sampleSymbol F t)) (j : Fin 13) :
    SmoothSymbol (F j) := by
  rw [read_original_functions F j]
  exact ContDiffOn.sum (fun t _ => contDiffOn_const.mul (samples t))

def nativeCorrectionSymbol (j : Fin 13) : Symbol := fun x =>
  nativeHalfCorrection j (fullCoordinates.symm x.1)+nativeWeylCorrection j (fullCoordinates.symm x.1)

def correctionArray (j : Fin 13) (m : ℕ) : ℝ :=
  coframeCorrectionArray j m+(originalHalfLeafArray j m+originalQuarterLeafArray j m)

theorem correctionArray_nonnegative (j : Fin 13) (m : ℕ) : 0 ≤ correctionArray j m := by
  exact add_nonneg (coframeCorrectionArray_nonnegative j m)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (original_density_nonnegative m))
      (mul_nonneg (Nat.cast_nonneg _) (original_weyl_nonnegative m)))

theorem native_correction_smooth (j : Fin 13) : SmoothSymbol (nativeCorrectionSymbol j) := by
  intro x hx
  exact (((nativeHalfCorrection_smooth j ⟨_,hx.1.1⟩).add
    (nativeWeylCorrection_smooth j ⟨_,hx.1.1⟩)).comp x
      (nativePhase_smooth.contDiffAt.fst)).contDiffWithinAt

theorem actual_correction_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) (j : Fin 13) : FiniteBound (nativeCorrectionSymbol j) M (correctionArray j) x := by
  have coefficients := generatedCoefficientInputs x hx box (M+2)
  have halfBudget := actual_half_leaf_budget M x hx box coefficients j
  have quarterBudget := actual_quarter_leaf_budget M x hx box coefficients j
  have halfSmooth := reader_smooth actualHalfLeaves half_sample_smooth j
  have quarterSmooth := reader_smooth actualQuarterLeaves quarter_sample_smooth j
  have rhoBudget := finite_add _ _ halfSmooth quarterSmooth _ _ M x hx halfBudget quarterBudget
  have whole := finite_add _ _ (coframe_correction_smooth j) (halfSmooth.add quarterSmooth) _ _ M x hx
    (coframe_correction_budget j M x hx box) rhoBudget
  have same : nativeCorrectionSymbol j=ᶠ[𝓝 x]
      (coframeCorrectionSymbol j+(actualHalfLeaves j+actualQuarterLeaves j)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    have formula := correction_leaf_formula j ⟨fullCoordinates.symm y.1,hy.1.1⟩
    rw [coframe_correction_read] at formula
    exact formula
  intro m hm w
  have read : PreparationVacuumCanonicalMoyal.jet m (nativeCorrectionSymbol j) w x=
      PreparationVacuumCanonicalMoyal.jet m (coframeCorrectionSymbol j+(actualHalfLeaves j+actualQuarterLeaves j)) w x :=
    PreparationVacuumCoframeBudget.jet_germ same m w
  rw [read]
  exact whole m hm w


def zeroLeafArray (j : Fin 14) : ArrayBound :=
  Fin.lastCases (fun _ => 0) (fun k m => classicalLeafArray k m+correctionArray k m) j

theorem zeroLeafArray_nonnegative (j : Fin 14) (m : ℕ) : 0 ≤ zeroLeafArray j m := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [zeroLeafArray,Fin.lastCases_last,le_refl]
  · simpa only [zeroLeafArray,Fin.lastCases_castSucc] using
      add_nonneg (classicalLeafArray_nonnegative k m) (correctionArray_nonnegative k m)

theorem classical_leaf_smooth (j : Fin 13) :
    SmoothSymbol (fun x => originalClassicalLeaves (fullCoordinates.symm x.1) j) := by
  intro x hx
  exact ((originalClassicalLeaf_smooth j ⟨_,hx.1.1⟩).comp x
    (nativePhase_smooth.contDiffAt.fst)).contDiffWithinAt

theorem actual_zero_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) (j : Fin 14) : FiniteBound (originalLeaf 0 j) M (zeroLeafArray j) x := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have same : originalLeaf 0 (Fin.last 13)=(fun _ => (0 : ℝ)) := by
      funext y
      simp only [originalLeaf_zero,originalZeroLeaves,Fin.snoc_last]
    rw [same]
    have bound := finite_constant 0 0 (by simp) M x
    have zero : constantArray 0=(fun _ => (0 : ℝ)) := by funext m; simp [constantArray]
    rw [zero] at bound
    simpa only [zeroLeafArray,Fin.lastCases_last] using bound
  · have same : originalLeaf 0 (Fin.castSucc k)=
        (fun y => originalClassicalLeaves (fullCoordinates.symm y.1) k+nativeCorrectionSymbol k y) := by
      funext y
      rw [originalLeaf_zero,originalZeroLeaves,Fin.snoc_castSucc]
      change originalClassicalLeaves (fullCoordinates.symm y.1) k+
        nativeHalfCorrection k (fullCoordinates.symm y.1)+nativeWeylCorrection k (fullCoordinates.symm y.1)=_
      simp only [nativeCorrectionSymbol,add_assoc]
    rw [same]
    simpa only [zeroLeafArray,Fin.lastCases_castSucc,Pi.add_def] using
      (finite_add _ _ (classical_leaf_smooth k) (native_correction_smooth k) _ _ M x hx
        (actual_classical_leaf_budget M x hx box k) (actual_correction_leaf_budget M x hx box k))

def lowerLeafArray (d : Fin 2) (j : Fin 14) : ArrayBound :=
  Fin.cases (zeroLeafArray j) (fun _ => firstLeafArray j) d

theorem lowerLeafArray_nonnegative (d : Fin 2) (j : Fin 14) (m : ℕ) :
    0 ≤ lowerLeafArray d j m := by
  fin_cases d
  · exact zeroLeafArray_nonnegative j m
  · exact firstLeafArray_nonnegative j m

theorem actual_lower_leaf_budget (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) (d : Fin 2) (j : Fin 14) :
    FiniteBound (originalLeaf (Fin.castSucc d) j) M (lowerLeafArray d j) x := by
  fin_cases d
  · exact actual_zero_leaf_budget M x hx box j
  · exact actual_first_leaf_budget M x hx box annulus j

def generatedLowerInputs (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (box : sourceBox x) (annulus : (∑ i : Fin 100,(x.2 i)^2) ≤ 4) : PreparationVacuumUniformFeed.LowerInputs x M where
  array := lowerLeafArray
  nonnegative := lowerLeafArray_nonnegative
  bounds := actual_lower_leaf_budget M x hx box annulus

end LowEnergy.PreparationVacuumLowerAssembly
