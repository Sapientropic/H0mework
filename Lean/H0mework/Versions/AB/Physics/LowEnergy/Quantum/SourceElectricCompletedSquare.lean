import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceElectricColumns

/-! Completion of the actual electric covariant columns in the original source pairing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.SourceElectricCompletedSquare
open SaturationMonoid.PhysicsCore
open StageNineGlobalIntegratedAction StageNineEnrichedProofFreeSource
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceElectricColumns
open scoped ContDiff Topology InnerProductSpace

def gaugePair (X Y : LieIndex → Fin 3 → QuantumTest) : ℂ :=
  ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3, sourcePair (X a i) (metricColumn i j (Y a j))

def completedColumn (κ : ℝ) (i : Fin 3) (a : LieIndex) : SourceElectricColumns.CoreEnd :=
  column i a-(Complex.I*(κ : ℂ)) • logColumn i a

def completedPair (κ : ℝ) (f g : QuantumTest) : ℂ :=
  gaugePair (fun a i => completedColumn κ i a f) (fun a i => completedColumn κ i a g)

private theorem pair_sum_right {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι → QuantumTest) :
    sourcePair f (∑ i, g i)=∑ i, sourcePair f (g i) := by
  simp only [sourcePair, map_sum, inner_sum]

private theorem pair_sum_left {ι : Type*} [Fintype ι] (f : ι → QuantumTest) (g : QuantumTest) :
    sourcePair (∑ i, f i) g=∑ i, sourcePair (f i) g := by
  simp only [sourcePair, map_sum, sum_inner]

private def evaluate (z : SourceCoordinateSlice) (word : Occupation) : QuantumTest →ₗ[ℂ] ℂ where
  toFun f := f z word
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem log_square_action :
    (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
      logColumn i a*(metricColumn i j*logColumn j a))=radialWeightAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change evaluate z word ((∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    logColumn i a*(metricColumn i j*logColumn j a)) f)=evaluate z word (radialWeightAction f)
  simp only [LinearMap.sum_apply, map_sum]
  change (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    (logCoefficient i a z : ℂ)*((gaugeWeight z i j : ℂ)*((logCoefficient j a z : ℂ)*f z word)))=
      (radialWeight z : ℂ)*f z word
  by_cases hz : z ∈ physicalChart
  · have hc : (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
        (logCoefficient i a z : ℂ)*((gaugeWeight z i j : ℂ)*(logCoefficient j a z : ℂ)))=
          (radialWeight z : ℂ) := by exact_mod_cast log_coefficient_square ⟨z,hz⟩
    simp_rw [←mul_assoc] at hc ⊢
    simp_rw [←Finset.sum_mul]
    rw [hc]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf]

theorem gauge_kinetic_columns (f g : QuantumTest) :
    gaugePair (fun a i => column i a f) (fun a i => column i a g)=
      2*sourcePair f (gaugeKinetic g) := by
  have he : 2*sourcePair f (gaugeKinetic g)=
      ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
        sourcePair f (sandwich (gaugeDirection i a) (gaugeDirection j a)
          (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) g) := by
    simp only [gaugeKinetic, LinearMap.smul_apply, LinearMap.sum_apply, sourcePair,
      map_smul, map_sum, inner_smul_right, inner_sum]
    ring
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (adjoint_pair (gaugeDirection i a) f (metricColumn i j (column j a g))).symm

theorem gauge_pair_left_cross (f g : QuantumTest) :
    gaugePair (fun a i => column i a f) (fun a i => logColumn i a g)=
      Complex.I*sourcePair (radialAction f) g := by
  have hs (i : Fin 3) (a : LieIndex) :
      (∑ j : Fin 3, metricColumn i j (logColumn j a g))=radialColumn i a g := by
    have h := LinearMap.congr_fun (metric_log_columns i a) g
    simpa only [LinearMap.sum_apply, Module.End.mul_apply] using h
  unfold gaugePair
  simp_rw [←pair_sum_right, hs]
  have hp (i : Fin 3) (a : LieIndex) :
      sourcePair (column i a f) (radialColumn i a g)=sourcePair (radialColumn i a (column i a f)) g :=
    multiply_pair _ _ _ _
  simp_rw [hp]
  simp_rw [←pair_sum_left]
  rw [radial_column_contraction]
  simp only [sourcePair, map_smul, inner_smul_left, map_neg, Complex.conj_I, neg_neg]

private theorem metric_column_symmetry (i j : Fin 3) : metricColumn i j=metricColumn j i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (gaugeWeight z i j : ℂ) • f z=(gaugeWeight z j i : ℂ) • f z
  rw [gaugeWeight_symmetric]

theorem gauge_pair_conjugate (X Y : LieIndex → Fin 3 → QuantumTest) :
    (starRingEnd ℂ) (gaugePair X Y)=gaugePair Y X := by
  simp only [gaugePair, map_sum, pair_conjugate]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    sourcePair (metricColumn j i (Y a i)) (X a j)=sourcePair (Y a i) (metricColumn j i (X a j)) :=
      (multiply_pair _ _ _ _).symm
    _ = _ := by rw [metric_column_symmetry j i]

theorem gauge_pair_right_cross (f g : QuantumTest) :
    gaugePair (fun a i => logColumn i a f) (fun a i => column i a g)=
      -Complex.I*sourcePair f (radialAction g) := by
  rw [←gauge_pair_conjugate, gauge_pair_left_cross]
  simp only [map_mul, Complex.conj_I, pair_conjugate]

theorem gauge_pair_log_square (f g : QuantumTest) :
    gaugePair (fun a i => logColumn i a f) (fun a i => logColumn i a g)=
      sourcePair f (radialWeightAction g) := by
  unfold gaugePair
  have hp (a : LieIndex) (i j : Fin 3) :
      sourcePair (logColumn i a f) (metricColumn i j (logColumn j a g))=
        sourcePair f (logColumn i a (metricColumn i j (logColumn j a g))) :=
    (multiply_pair _ _ _ _).symm
  simp_rw [hp]
  simp_rw [←pair_sum_right]
  have h := LinearMap.congr_fun log_square_action g
  simpa only [LinearMap.sum_apply, Module.End.mul_apply] using congrArg (sourcePair f) h

private theorem pair_expansion (X Y Z W : LieIndex → Fin 3 → QuantumTest) (c : ℂ) :
    gaugePair (fun a i => X a i-c • Y a i) (fun a i => Z a i-c • W a i)=
      gaugePair X Z-c*gaugePair X W-(starRingEnd ℂ) c*gaugePair Y Z+
        ((starRingEnd ℂ) c*c)*gaugePair Y W := by
  simp only [gaugePair, sourcePair, map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, mul_sub, Finset.sum_sub_distrib, ←Finset.mul_sum]
  ring

theorem completed_pair_identity (κ : ℝ) (f g : QuantumTest) :
    completedPair κ f g=2*sourcePair f (gaugeKinetic g)+
      ((κ : ℂ)*((κ : ℂ)-34))*sourcePair f (radialWeightAction g) := by
  change gaugePair (fun a i => column i a f-(Complex.I*(κ : ℂ)) • logColumn i a f)
    (fun a i => column i a g-(Complex.I*(κ : ℂ)) • logColumn i a g)=_
  rw [pair_expansion, gauge_kinetic_columns, gauge_pair_left_cross, gauge_pair_right_cross,
    gauge_pair_log_square]
  have h := original_radial_current f g
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (norm := ring_nf) (κ : ℂ)*h
  simp only [Complex.I_sq]
  ring

theorem electric_completed_square_pair (κ : ℝ) (f g : QuantumTest) :
    sourcePair f (gaugeKinetic g)=(1/2 : ℂ)*completedPair κ f g+
      ((κ*(34-κ)/2 : ℝ) : ℂ)*sourcePair f (radialWeightAction g) := by
  rw [completed_pair_identity]
  push_cast
  ring

def factorCoefficient (k i : Fin 3) (z : SourceCoordinateSlice) : ℝ :=
  Real.sqrt (sourceSigma*volume z/sourceTime 0)*triadInverse z.1 i k

theorem electric_scale_pos (z : physicalChart) : 0<sourceSigma*volume z.val/sourceTime 0 := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact Stage9C.Material.SpinPair.lapse_pos
  exact div_pos (mul_pos positiveSmoothUnifiedSource.legacy.sigma_pos (volume_pos z)) hn

theorem factor_coefficient_smooth (k i : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (factorCoefficient k i) z.val :=
  (((contDiffAt_const.mul volume_smooth.contDiffAt).div_const _).sqrt
    (electric_scale_pos z).ne').mul (triadInverse_smooth i k z)

theorem factor_coefficient_square (z : physicalChart) (i j : Fin 3) :
    (∑ k : Fin 3, factorCoefficient k i z.val*factorCoefficient k j z.val)=
      gaugeWeight z.val i j := by
  unfold factorCoefficient gaugeWeight inverseSpatial
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have hs := Real.sq_sqrt (electric_scale_pos z).le
  calc
    _ = (Real.sqrt (sourceSigma*volume z.val/sourceTime 0))^2*
        ∑ k : Fin 3, triadInverse z.val.1 i k*triadInverse z.val.1 j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hs]

def factorColumn (k i : Fin 3) : SourceElectricColumns.CoreEnd :=
  multiply (factorCoefficient k i) (factor_coefficient_smooth k i)

theorem factor_column_square (i j : Fin 3) :
    (∑ k : Fin 3, factorColumn k i*factorColumn k j)=metricColumn i j := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change evaluate z word ((∑ k : Fin 3, factorColumn k i*factorColumn k j) f)=
    evaluate z word (metricColumn i j f)
  simp only [LinearMap.sum_apply, map_sum]
  change (∑ k : Fin 3, (factorCoefficient k i z : ℂ)*((factorCoefficient k j z : ℂ)*f z word))=
    (gaugeWeight z i j : ℂ)*f z word
  by_cases hz : z ∈ physicalChart
  · have hc : (∑ k : Fin 3, (factorCoefficient k i z : ℂ)*(factorCoefficient k j z : ℂ))=
        (gaugeWeight z i j : ℂ) := by exact_mod_cast factor_coefficient_square ⟨z,hz⟩ i j
    simp_rw [←mul_assoc]
    rw [←Finset.sum_mul, hc]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp [hf]

theorem gauge_pair_factor (X Y : LieIndex → Fin 3 → QuantumTest) :
    gaugePair X Y=∑ a : LieIndex, ∑ k : Fin 3,
      sourcePair (∑ i : Fin 3, factorColumn k i (X a i))
        (∑ j : Fin 3, factorColumn k j (Y a j)) := by
  unfold gaugePair
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [pair_sum_left, pair_sum_right]
  have hm (i j : Fin 3) (g : QuantumTest) :
      metricColumn i j g=∑ k : Fin 3, factorColumn k i (factorColumn k j g) := by
    have h := LinearMap.congr_fun (factor_column_square i j) g
    simpa only [LinearMap.sum_apply, Module.End.mul_apply] using h.symm
  simp_rw [hm, pair_sum_right]
  have hp (i j k : Fin 3) :
      sourcePair (X a i) (factorColumn k i (factorColumn k j (Y a j)))=
        sourcePair (factorColumn k i (X a i)) (factorColumn k j (Y a j)) :=
    multiply_pair _ _ _ _
  simp_rw [hp]
  trans ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3,
    sourcePair (factorColumn k i (X a i)) (factorColumn k j (Y a j))
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

theorem gauge_pair_nonneg (X : LieIndex → Fin 3 → QuantumTest) :
    0≤(gaugePair X X).re := by
  rw [gauge_pair_factor]
  change 0≤Complex.reAddGroupHom (∑ a : LieIndex, ∑ k : Fin 3, _)
  simp only [map_sum]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro k _
  exact inner_self_nonneg

theorem completed_pair_nonneg (κ : ℝ) (f : QuantumTest) :
    0≤(completedPair κ f f).re :=
  gauge_pair_nonneg _

theorem electric_completed_square_real (κ : ℝ) (f : QuantumTest) :
    (sourcePair f (gaugeKinetic f)).re=(1/2:ℝ)*(completedPair κ f f).re+
      (κ*(34-κ)/2)*(sourcePair f (radialWeightAction f)).re := by
  have h := congrArg Complex.re (electric_completed_square_pair κ f f)
  simpa using h

theorem electric_hardy (f : QuantumTest) :
    (289/2:ℝ)*(sourcePair f (radialWeightAction f)).re≤
      (sourcePair f (gaugeKinetic f)).re := by
  have h := electric_completed_square_real 17 f
  have hp := completed_pair_nonneg 17 f
  norm_num at h
  linarith

end LowEnergy.SourceElectricCompletedSquare
