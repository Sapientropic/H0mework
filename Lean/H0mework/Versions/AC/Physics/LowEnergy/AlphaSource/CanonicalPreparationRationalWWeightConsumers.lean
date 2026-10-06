import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationRationalWElectricEntries
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalActualN0

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRationalW
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open PreparationActualFactor
open GaussNativeEnergy GaussHistoryHilbert PreparationScalarCoordinates PreparationCoordinates
open PreparationVacuumLowerLeaves PreparationVacuumTemporalOrdering PreparationVacuumLowerTensor
open PreparationVacuumPrincipalBudget PreparationVacuumClockSymbol PreparationVacuumEngineSmooth
open PreparationVacuumCanonicalMoyal PreparationVacuumCentralBudget
open PreparationVacuumMoyalBudget PreparationVacuumEngineBudget
open scoped BigOperators ContDiff Topology Matrix

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol

private theorem minkowski_inverse : minkowskiInternalMetric⁻¹=minkowskiInternalMetric := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiInternalMetric,Matrix.mul_apply,Fin.sum_univ_four]

theorem original_h00 (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart) (hn : n≠0) :
    originalScalarMetric n b z.val 0 0= -(volume z.val/n) := by
  have formula : originalScalarMetric n b z.val=
      (n*volume z.val) • (generatedCoframeInverse n b z.val.1*minkowskiInternalMetric*
        (generatedCoframeInverse n b z.val.1).transpose) := by
    unfold originalScalarMetric lorentzianMetricOfCoframe
    rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,minkowski_inverse,
      originalCoframeInverse_generated n b z hn,coframe_determinant]
    simp only [originalTimeColumn,Matrix.mul_assoc,volume]
    rfl
  rw [formula]
  simp only [Matrix.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,smul_eq_mul]
  simp [generatedCoframeInverse,minkowskiInternalMetric,Fin.sum_univ_four]
  field_simp [hn]

def scalarWeight (n : ℝ) (b : Fin 3 → ℝ) : Symbol := fun x =>
  (originalScalarMetric n b (fullCoordinates.symm x.1) 0 0)⁻¹

theorem scalar_weight_formula (n : ℝ) (b : Fin 3 → ℝ) (z : physicalChart) (hn : n≠0) :
    (originalScalarMetric n b z.val 0 0)⁻¹= -n*(volume z.val)⁻¹ := by
  rw [original_h00 n b z hn]
  field_simp [hn,(volume_pos z).ne']

theorem scalar_source_coefficient (n : ℝ) (b : Fin 3 → ℝ) (a : GaussNativeForm.ScalarIndex)
    (z : physicalChart) (hn : n≠0) :
    2*actualTimePairCoefficient n b (Sum.inl a) z.val=(originalScalarMetric n b z.val 0 0)⁻¹ := by
  rw [scalar_weight_formula n b z hn]
  unfold actualTimePairCoefficient GaussNativeEnergy.scalarWeight
  field_simp [source_time_nonzero]

def scalarWArray (m : ℕ) : ℝ := 2*PreparationVacuumCoframeBudget.inverseVolumeArray m

def gaugeWArray (m : ℕ) : ℝ := 2*electricArray m

private theorem scalar_germ (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) :
    scalarWeight n b=ᶠ[𝓝 x](fun y => -n*PreparationVacuumCoframeBudget.sourceVolumeInverse y) := by
  filter_upwards [PreparationVacuumMoyalSymmetry.originalPhysicalPhase_open.mem_nhds physical] with y hy
  exact scalar_weight_formula n b ⟨_,hy⟩ hn

theorem scalar_weight_smooth (n : ℝ) (b : Fin 3 → ℝ) (hn : n≠0) : SmoothSymbol (scalarWeight n b) := by
  intro x hx
  have smooth := (inverseVolume_smooth_source x hx).contDiffAt (poleDomain_open.mem_nhds hx)
  have scaled : ContDiffAt ℝ ∞ (fun y => -n*PreparationVacuumCoframeBudget.sourceVolumeInverse y) x :=
    contDiffAt_const.mul smooth
  exact (scaled.congr_of_eventuallyEq (scalar_germ n b hn x hx.1.1)).contDiffWithinAt

theorem scalar_weight_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (m : ℕ) (w : Word m) (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) :
    |jet m (scalarWeight n b) w x| ≤ scalarWArray m := by
  have physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase := (PreparationPhaseScalar.phaseChart x.1 box).property
  have same : jet m (scalarWeight n b) w x=jet m (fun y => -n*PreparationVacuumCoframeBudget.sourceVolumeInverse y) w x :=
    PreparationVacuumCoframeBudget.jet_germ (scalar_germ n b (time_positive n b time).1.ne' x physical) m w
  have vi : ContDiffAt ℝ ∞ PreparationVacuumCoframeBudget.sourceVolumeInverse x :=
    ((volume_smooth.contDiffAt.comp x (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).inv
      (volume_pos (PreparationPhaseScalar.phaseChart x.1 box)).ne')
  have scale : jet m (fun y => -n*PreparationVacuumCoframeBudget.sourceVolumeInverse y) w x=
      -n*jet m PreparationVacuumCoframeBudget.sourceVolumeInverse w x :=
    PreparationVacuumCoframeBudget.jet_scale (-n) _ m w x vi
  rw [same,scale,abs_mul,abs_neg]
  have nb : |n| ≤ 2 := by simpa [timeCoordinate] using time_coordinate_bound n b time 0
  exact mul_le_mul nb (PreparationVacuumCoframeBudget.actual_inverseVolume_budget m w x box)
    (abs_nonneg _) (by norm_num)

def scalarW (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 70 70 := fun x =>
  Matrix.diagonal (fun _ => scalarWeight n b x)

def gaugeW (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 36 36 := fun x i j =>
  actualElectric n b (spatialRow i) (spatialRow j) x*rawGramInverse (nativeRow i) (nativeRow j)

def rawGaugeRows : (Fin 3 × Fin 12) ≃ Fin 36 where
  toFun p := combinedRow p.1 p.2
  invFun i := (spatialRow i,nativeRow i)
  left_inv p := by simp [spatial_combined,native_combined]
  right_inv := combined_rows

theorem sum_rawGaugeRows (f : Fin 36 → ℝ) : (∑ i,f i)=∑ r : Fin 3,∑ a : Fin 12,f (combinedRow r a) := by
  rw [←Equiv.sum_comp rawGaugeRows]
  exact Fintype.sum_prod_type _

theorem electric_smooth (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) (i j : Fin 3) :
    SmoothSymbol (actualElectric n b i j) := by
  intro x hx
  exact ((actualElectricInverse_smooth n b (time_positive n b time).1.ne'
    (time_positive n b time).2.ne' i j ⟨_,hx.1.1⟩).comp x
      (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem gaugeW_smooth (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) : RectSmooth (gaugeW n b) := by
  intro i j
  exact (electric_smooth n b time (spatialRow i) (spatialRow j)).mul contDiffOn_const

theorem scalarW_smooth (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b) : RectSmooth (scalarW n b) := by
  intro i j
  by_cases h : i=j
  · subst j; simpa [scalarW] using scalar_weight_smooth n b (time_positive n b time).1.ne'
  · simp only [scalarW,Matrix.diagonal_apply_ne _ h]
    exact contDiffOn_const

theorem scalarW_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (x : Phase) (box : PreparationVacuumCoframeBudget.sourceBox x) (M : ℕ) :
    MatrixBound (scalarW n b) M scalarWArray x :=
  finite_diagonal (scalarWeight n b) M scalarWArray (fun m => by unfold scalarWArray; positivity) x
    (fun m _ w => scalar_weight_budget n b time m w x box)

private theorem gaugeW_jet (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (m : ℕ) (w : Word m) (x : Phase) (hx : x∈poleDomain) (i j : Fin 36) :
    jet m (fun y => gaugeW n b y i j) w x=
      jet m (actualElectric n b (spatialRow i) (spatialRow j)) w x*rawGramInverse (nativeRow i) (nativeRow j) := by
  have smooth := (electric_smooth n b time (spatialRow i) (spatialRow j) x hx).contDiffAt (poleDomain_open.mem_nhds hx)
  have scale : jet m (fun y => rawGramInverse (nativeRow i) (nativeRow j)*
      actualElectric n b (spatialRow i) (spatialRow j) y) w x=
      rawGramInverse (nativeRow i) (nativeRow j)*jet m (actualElectric n b (spatialRow i) (spatialRow j)) w x :=
    PreparationVacuumCoframeBudget.jet_scale _ _ m w x smooth
  simpa only [gaugeW,mul_comm] using scale

theorem gaugeW_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x) (M : ℕ) :
    MatrixBound (gaugeW n b) M gaugeWArray x := by
  intro m _ w
  constructor
  · intro i
    simp only [gaugeW_jet n b time m w x hx]
    rw [sum_rawGaugeRows]
    simp only [spatial_combined,native_combined,abs_mul,←Finset.mul_sum]
    calc
      _ ≤ ∑ r : Fin 3,|jet m (actualElectric n b (spatialRow i) r) w x| *2 :=
        Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (rawGramInverse_bound.1 (nativeRow i)) (abs_nonneg _))
      _ = (∑ r : Fin 3,|jet m (actualElectric n b (spatialRow i) r) w x|)*2 := by rw [Finset.sum_mul]
      _ ≤ gaugeWArray m := by
        have row : (∑ r : Fin 3,|jet m (actualElectric n b (spatialRow i) r) w x|) ≤ (electricArray m : ℝ) :=
          actual_electric_row_budget n b time m w x box (spatialRow i)
        simpa only [gaugeWArray,mul_comm] using mul_le_mul_of_nonneg_right row (by norm_num : (0 : ℝ) ≤ 2)
  · intro j
    simp only [gaugeW_jet n b time m w x hx]
    rw [sum_rawGaugeRows]
    simp only [spatial_combined,native_combined,abs_mul,←Finset.mul_sum]
    calc
      _ ≤ ∑ r : Fin 3,|jet m (actualElectric n b r (spatialRow j)) w x| *2 :=
        Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (rawGramInverse_bound.2 (nativeRow j)) (abs_nonneg _))
      _ = (∑ r : Fin 3,|jet m (actualElectric n b r (spatialRow j)) w x|)*2 := by rw [Finset.sum_mul]
      _ ≤ gaugeWArray m := by
        have col : (∑ r : Fin 3,|jet m (actualElectric n b r (spatialRow j)) w x|) ≤ (electricArray m : ℝ) :=
          actual_electric_column_budget n b time m w x box (spatialRow j)
        simpa only [gaugeWArray,mul_comm] using mul_le_mul_of_nonneg_right col (by norm_num : (0 : ℝ) ≤ 2)



theorem actual_scalarW_quadratic (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) :
    (∑ r : Fin 70,∑ s : Fin 70,scalarW n b x r s*rawScalarMomentum r x*rawScalarMomentum s x)=
      scalarWeight n b x*PreparationActualFactor.scalarNormSquare (fullCoordinates.symm x.1) (nativeCovector x.2) := by
  rw [actual_scalarGram_raw,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [scalarW,Matrix.diagonal_apply,ite_mul]
  ring

theorem actual_gaugeW_quadratic (n : ℝ) (b : Fin 3 → ℝ) (x : Phase) :
    (∑ r : Fin 36,∑ s : Fin 36,gaugeW n b x r s*rawGaugeMomentum r x*rawGaugeMomentum s x)=
      ∑ i : Fin 3,∑ j : Fin 3,actualElectric n b i j x*
        PreparationActualFactor.electricGram (fullCoordinates.symm x.1) (nativeCovector x.2) i j := by
  have row (i : Fin 3) :
      (∑ a : Fin 12,∑ j : Fin 3,∑ c : Fin 12,actualElectric n b i j x*rawGramInverse a c*
        rawGaugeMomentum (combinedRow i a) x*rawGaugeMomentum (combinedRow j c) x)=
      ∑ j : Fin 3,actualElectric n b i j x*((electricRawMatrix x*rawGramInverse)*(electricRawMatrix x)ᵀ) i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul,electricRawMatrix]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [sum_rawGaugeRows]
  simp only [gaugeW,spatial_combined,native_combined]
  simp only [row,←actual_electricGram_raw]

def scalarP (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 94 94 := fun x =>
  (1/2 : ℝ) • (((scalarCoefficients x.1)ᵀ*scalarW n b x)*scalarCoefficients x.1)
def gaugeP (n : ℝ) (b : Fin 3 → ℝ) : RectSymbol 94 94 := fun x =>
  (1/2 : ℝ) • (((gaugeCoefficients x.1)ᵀ*gaugeW n b x)*gaugeCoefficients x.1)

def scalarPArray (m : ℕ) : ℝ := (1/2 : ℝ)*productArray (productArray scalarFactorArray scalarWArray) scalarFactorArray m
def gaugePArray (m : ℕ) : ℝ := (1/2 : ℝ)*productArray (productArray gaugeFactorArray gaugeWArray) gaugeFactorArray m

private theorem sandwich_budget {a : ℕ} (A : RectSymbol a 94) (W : RectSymbol a a)
    (asmooth : RectSmooth A) (wsmooth : RectSmooth W) (B D : ArrayBound)
    (bp : ∀ m,0 ≤ B m) (dp : ∀ m,0 ≤ D m) (M : ℕ) (x : Phase) (hx : x∈poleDomain)
    (abound : MatrixBound A M B x) (wbound : MatrixBound W M D x) :
    MatrixBound (fun y => (1/2 : ℝ) • ((A y)ᵀ*W y*A y)) M
      (fun m => (1/2 : ℝ)*productArray (productArray B D) B m) x := by
  have first := finite_matrix_product (fun y => (A y)ᵀ) W (fun i j => asmooth j i) wsmooth M B D bp dp x hx
    (finite_matrix_transpose A M B x abound) wbound
  have firstSmooth := matrix_product_smooth (fun y => (A y)ᵀ) W (fun i j => asmooth j i) wsmooth
  have second := finite_matrix_product (fun y => (A y)ᵀ*W y) A firstSmooth asmooth M (productArray B D) B
    (productArray_nonnegative B D bp dp) bp x hx first abound
  have secondSmooth := matrix_product_smooth (fun y => (A y)ᵀ*W y) A firstSmooth asmooth
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using
    finite_matrix_scale (1/2 : ℝ) _ secondSmooth M _ x hx second

theorem actual_scalarP_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (inputs : CoefficientInputs x M) : MatrixBound (scalarP n b) M scalarPArray x :=
  sandwich_budget (fun y => scalarCoefficients y.1) (scalarW n b)
    (fun a k => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ k) (scalarW_smooth n b time) scalarFactorArray scalarWArray
    scalarFactor_nonnegative (fun m => by unfold scalarWArray; positivity) M x hx inputs.scalar
    (scalarW_budget n b time x box M)

theorem actual_gaugeP_budget (n : ℝ) (b : Fin 3 → ℝ) (time : TimeBox n b)
    (M : ℕ) (x : Phase) (hx : x∈poleDomain) (box : PreparationVacuumCoframeBudget.sourceBox x)
    (inputs : CoefficientInputs x M) : MatrixBound (gaugeP n b) M gaugePArray x :=
  sandwich_budget (fun y => gaugeCoefficients y.1) (gaugeW n b)
    (fun a k => PreparationVacuumPrincipalBudget.sourceCoefficient_smooth _ k) (gaugeW_smooth n b time) gaugeFactorArray gaugeWArray
    gaugeFactor_nonnegative (fun m => by unfold gaugeWArray; positivity) M x hx inputs.gauge
    (gaugeW_budget n b time x hx box M)

theorem gaugeW_array_zero : gaugeWArray 0=37678911750 := by
  rw [gaugeWArray,electric_array_zero]
  norm_num

end LowEnergy.PreparationVacuumRationalW
