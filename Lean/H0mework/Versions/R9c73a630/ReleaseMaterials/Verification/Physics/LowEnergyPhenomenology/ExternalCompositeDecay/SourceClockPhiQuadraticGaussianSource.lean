import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeSecondActionSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.FirstCurrentPayerNext
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
private abbrev γ := gaussianReal 0 1
abbrev QuadraticIndex := Fin 3 × Fin 3
private def firstDegree (i : Fin 3) : ℕ := if i = 1 then 1 else 0
private def secondDegree (i : Fin 3) : ℕ := if i = 2 then 1 else 0

def noiseLinear (i : Fin 3) (x : ℝ×ℝ) : ℝ := x.1^(firstDegree i)*x.2^(secondDegree i)
def noiseQuadratic (i : QuadraticIndex) (x : ℝ×ℝ) : ℝ := noiseLinear i.1 x*noiseLinear i.2 x
def quadraticSource (v : QuadraticIndex → QuantumTest) (x : ℝ×ℝ) : QuantumTest :=
  ∑ i, (noiseQuadratic i x:ℂ) • v i
private def rawMoment (k : ℕ) : ℝ := ∫ x : ℝ, x^k ∂γ
def quadraticMoment (i j : QuadraticIndex) : ℝ :=
  rawMoment (firstDegree i.1+firstDegree i.2+firstDegree j.1+firstDegree j.2)*
    rawMoment (secondDegree i.1+secondDegree i.2+secondDegree j.1+secondDegree j.2)

private theorem gaussian_power_integrable (k : ℕ) : Integrable (fun x : ℝ => x^k) γ := by
  have h := (memLp_id_gaussianReal' (μ:=0) (v:=1) (k:ENNReal) (by finiteness)).integrable_norm_pow'
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by simp only [norm_pow,id_eq,le_refl]
private theorem quadratic_product (i j : QuadraticIndex) (x : ℝ×ℝ) :
    noiseQuadratic i x*noiseQuadratic j x =
      x.1^(firstDegree i.1+firstDegree i.2+firstDegree j.1+firstDegree j.2)*
      x.2^(secondDegree i.1+secondDegree i.2+secondDegree j.1+secondDegree j.2) := by
  simp only [noiseQuadratic,noiseLinear,pow_add]
  ring
private theorem quadratic_integrable (i j : QuadraticIndex) :
    Integrable (fun x : ℝ×ℝ => (noiseQuadratic i x:ℂ)*(noiseQuadratic j x:ℂ)) (γ.prod γ) := by
  have h := (gaussian_power_integrable (firstDegree i.1+firstDegree i.2+firstDegree j.1+firstDegree j.2)).mul_prod
    (gaussian_power_integrable (secondDegree i.1+secondDegree i.2+secondDegree j.1+secondDegree j.2))
  simpa only [←Complex.ofReal_mul,quadratic_product] using! h.ofReal
private theorem quadratic_integral (i j : QuadraticIndex) :
    (∫ x : ℝ×ℝ, (noiseQuadratic i x:ℂ)*(noiseQuadratic j x:ℂ) ∂γ.prod γ) = (quadraticMoment i j:ℂ) := by
  simp only [←Complex.ofReal_mul,quadratic_product]
  rw [integral_complex_ofReal]
  congr 1
  exact integral_prod_mul (μ:=γ) (ν:=γ)
    (fun x : ℝ => x^(firstDegree i.1+firstDegree i.2+firstDegree j.1+firstDegree j.2))
    (fun x : ℝ => x^(secondDegree i.1+secondDegree i.2+secondDegree j.1+secondDegree j.2))
private theorem quadratic_pair_expansion (v w : QuadraticIndex → QuantumTest)
    (M : QuantumTest →ₗ[ℂ] QuantumTest) (x : ℝ×ℝ) :
    sourcePair (quadraticSource v x) (M (quadraticSource w x)) =
      ∑ i,∑ j,(noiseQuadratic i x:ℂ)*(noiseQuadratic j x:ℂ)*sourcePair (v i) (M (w j)) := by
  simp only [quadraticSource,map_sum,map_smul,sourcePair,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual Gaussian product law internally pays all fourth moments of a quadratic source. -/
theorem quadratic_gaussian_pair (v w : QuadraticIndex → QuantumTest)
    (M : QuantumTest →ₗ[ℂ] QuantumTest) :
    Integrable (fun x : ℝ×ℝ => sourcePair (quadraticSource v x) (M (quadraticSource w x))) (γ.prod γ) ∧
    (∫ x : ℝ×ℝ, sourcePair (quadraticSource v x) (M (quadraticSource w x)) ∂γ.prod γ) =
      ∑ i,∑ j,(quadraticMoment i j:ℂ)*sourcePair (v i) (M (w j)) := by
  have hi (i j : QuadraticIndex) := (quadratic_integrable i j).mul_const (sourcePair (v i) (M (w j)))
  have hs (i : QuadraticIndex) := integrable_finsetSum Finset.univ (fun j _ => hi i j)
  refine ⟨?_,?_⟩
  · simpa only [quadratic_pair_expansion] using integrable_finsetSum Finset.univ (fun i _ => hs i)
  · simp only [quadratic_pair_expansion]
    rw [integral_finsetSum _ (fun i _ => hs i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const,quadratic_integral]
theorem noiseLinear_values (x : ℝ×ℝ) :
    noiseLinear 0 x = 1 ∧ noiseLinear 1 x = x.1 ∧ noiseLinear 2 x = x.2 := by
  norm_num [noiseLinear,firstDegree,secondDegree,Fin.ext_iff]
end LowEnergy.FirstCurrentPayerNext
