import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeJointGaussianSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NativePointReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceClockPhiNativeMatchedSource
open SourceQuantumConfigurationHilbert SourceClockPhiMatchedDiffusionSource SourceClockPhiCombinedScalePressure
open ClockPhiHeatCorrectedCovarianceSource SourceClockPhiNormalizedScalarBudget FirstCurrentPayerNext MeasureTheory ProbabilityTheory
open SourceClockPhiGaussianComplexIBP
open scoped InnerProductSpace
private abbrev γ:=gaussianReal 0 1
attribute [local irreducible] sourcePair embed

private theorem gaussian_third:(∫x:ℝ,x^3 ∂γ)=0:=by
  have h:Measure.map (fun x:ℝ=>-x) γ=γ:=by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ:=0) (v:=1))
  have hi:=integral_map (μ:=γ) (φ:=fun x:ℝ=>-x) (f:=fun x:ℝ=>x^3) (by fun_prop) (by fun_prop)
  rw [h] at hi
  have he:(fun x:ℝ=>(-x)^3)=fun x:ℝ=>-(x^3):=by funext x;ring
  rw [he,integral_neg] at hi
  linarith

private theorem gaussian_moments:
    (∫x:ℝ,x^0 ∂γ)=1 ∧ (∫x:ℝ,x^1 ∂γ)=0 ∧
    (∫x:ℝ,x^2 ∂γ)=1 ∧ (∫x:ℝ,x^3 ∂γ)=0:=by
  exact ⟨by simp,by simpa only [pow_one] using (integral_id_gaussianReal (μ:=0) (v:=1)),
    standard_gaussian_square_moment,gaussian_third⟩

private theorem affine_quadratic_moment(i:Fin 3)(b:QuadraticIndex):
    quadraticMoment (i,0) b=
      if i=0 then (if b=(0,0) ∨ b=(1,1) ∨ b=(2,2) then 1 else 0)
      else if i=1 then (if b=(0,1) ∨ b=(1,0) then 1 else 0)
      else (if b=(0,2) ∨ b=(2,0) then 1 else 0):=by
  rcases b with ⟨j,k⟩
  let d1:=fun a:Fin 3=>if a=1 then (1:ℕ) else 0
  let d2:=fun a:Fin 3=>if a=2 then (1:ℕ) else 0
  have he:quadraticMoment (i,0) (j,k)=
      (∫x:ℝ,x^(d1 i+d1 0+d1 j+d1 k) ∂γ)*
      (∫x:ℝ,x^(d2 i+d2 0+d2 j+d2 k) ∂γ):=rfl
  rw [he]
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num [d1,d2,Fin.ext_iff,gaussian_moments.1,gaussian_moments.2.1,
    gaussian_moments.2.2.1,gaussian_moments.2.2.2]

def affineGaussianColumn(v:Fin 3→QuantumTest):QuadraticIndex→QuantumTest:=
  fun a=>if a.2=0 then v a.1 else 0

def cubicSourcePair(t:ℝ)(v:Fin 3→QuantumTest)(w:QuadraticIndex→QuantumTest):ℂ:=
  sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (v 0))
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (w (0,0)+w (1,1)+w (2,2)))+
  sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (v 1))
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (w (0,1)+w (1,0)))+
  sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (v 2))
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (w (0,2)+w (2,0)))

private theorem pair_zero(f:QuantumTest):sourcePair 0 f=0:=by
  simp only [sourcePair,map_zero,inner_zero_left]
private theorem pair_zero_right(f:QuantumTest):sourcePair f 0=0:=by
  simp only [sourcePair,map_zero,inner_zero_right]
private theorem pair_add(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]

/-- The actual Gaussian moments contract an affine × quadratic source to its three original rows. -/
theorem actual_affine_quadratic_source_contraction(t:ℝ)(v:Fin 3→QuantumTest)(w:QuadraticIndex→QuantumTest):
    coframeGaussianPair t (affineGaussianColumn v) w=cubicSourcePair t v w:=by
  unfold coframeGaussianPair affineGaussianColumn
  simp only [Fintype.sum_prod_type,Fin.sum_univ_succ]
  norm_num [Fin.ext_iff,affine_quadratic_moment,map_zero,pair_zero]
  unfold cubicSourcePair
  simp only [map_add,pair_add]
  ring

/-- The same contraction retains all three source squares and removes every artificial noise cross. -/
theorem actual_affine_source_square(t:ℝ)(v:Fin 3→QuantumTest):
    coframeGaussianPair t (affineGaussianColumn v) (affineGaussianColumn v)=
      ∑i:Fin 3,sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (v i))
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (v i)):=by
  rw [actual_affine_quadratic_source_contraction]
  norm_num [cubicSourcePair,affineGaussianColumn,Fin.sum_univ_succ,Fin.ext_iff,map_zero,map_add,
    pair_add,pair_zero,pair_zero_right]
  ring

def matchedSourceRows(t:ℝ)(ht:0<t)(w:QuantumTest):Fin 3→QuantumTest:=
  ![matchedTester w,-(noiseAction t ht 1 0 (combinedGenerator w)),-(noiseAction t ht 0 1 (combinedGenerator w))]

private theorem actual_matched_source_rows(t:ℝ)(ht:0<t)(w:QuantumTest):
    matchedGaussianColumn t ht w=affineGaussianColumn (matchedSourceRows t ht w):=by
  funext a
  rcases a with ⟨i,j⟩
  change (if (i,j)=(0,0) then matchedTester w else 0)+
    (if (i,j)=(1,0) then -(noiseAction t ht 1 0 (combinedGenerator w)) else 0)+
    (if (i,j)=(2,0) then -(noiseAction t ht 0 1 (combinedGenerator w)) else 0)=
      (if j=0 then matchedSourceRows t ht w i else 0)
  fin_cases i <;> fin_cases j <;> norm_num [matchedSourceRows,Fin.ext_iff]

/-- The literal matched current needs precisely its three original source rows. -/
theorem actual_matched_coframe_cubic_price(t:ℝ)(ht:0<t)(z:ℂ)(w:QuantumTest):
    coframeGaussianPair t (matchedGaussianColumn t ht w) (coframeForcingColumn t ht z w)=
      cubicSourcePair t (matchedSourceRows t ht w) (coframeForcingColumn t ht z w) ∧
    coframeGaussianPair t (matchedGaussianColumn t ht w) (matchedGaussianColumn t ht w)=
      ∑i:Fin 3,sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (matchedSourceRows t ht w i))
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (matchedSourceRows t ht w i)):=by
  rw [actual_matched_source_rows]
  exact ⟨actual_affine_quadratic_source_contraction _ _ _,actual_affine_source_square _ _⟩

theorem actual_signed_coframe_three_row_gaussian(t:ℝ)(ht:0<t)
    (m ell:ℕ)(F:GaussUnitaryHistory.Index)(z:ℂ)(hz:z.im≠0)(g:GaussDiagonalHistory.diagonal.domain):
    let w:=normalizedState m ell F z hz g
    let price:=fun x:ℝ×ℝ=>(432/GaussNativeEnergy.sourceTime 0)*‖embed (coframeForcing t ht x z w)‖^2-
      (GaussNativeEnergy.sourceTime 0/48)*‖embed (coframeCompleted t ht x z w)‖^2
    Integrable price (γ.prod γ) ∧ (∫x,price x ∂γ.prod γ)=
      -6*(cubicSourcePair t (matchedSourceRows t ht w) (coframeForcingColumn t ht z w)).re-
      (GaussNativeEnergy.sourceTime 0/48)*(∑i:Fin 3,
        sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (matchedSourceRows t ht w i))
          (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (matchedSourceRows t ht w i))).re:=by
  intro w price
  have h:=actual_normalized_signed_coframe_gaussian t ht m ell F z hz g
  dsimp only at h
  rw [(actual_matched_coframe_cubic_price t ht z w).1,(actual_matched_coframe_cubic_price t ht z w).2] at h
  exact h

end LowEnergy.NativePointReturn
