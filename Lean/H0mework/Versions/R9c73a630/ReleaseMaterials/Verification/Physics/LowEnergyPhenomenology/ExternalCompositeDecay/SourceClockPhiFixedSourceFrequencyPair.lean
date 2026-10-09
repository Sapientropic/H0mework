import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPairedFrequencyKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.InputForceFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussDiagonalHistory
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open MeasureTheory Filter ReverseNativeFrequencyWard
private abbrev pole(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹

def fixedSourceWave {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(a:ι→ℝ)(c:ι→QuantumTest)(q:ℝ):QuantumTest:=
  ∑i,pole advanced μ (a i) q • c i
def fixedSourceDerivative {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(a:ι→ℝ)(c:ι→QuantumTest)(q:ℝ):QuantumTest:=
  ∑i,(pole advanced μ (a i) q)^2 • c i
attribute [local irreducible] sourcePair embed
private theorem finite_pair {ι:Type*}[Fintype ι](c d:ι→QuantumTest)(a b:ι→ℂ):
    sourcePair (∑i,a i • c i) (∑j,b j • d j)=∑i,∑j,(star (a i)*b j)*sourcePair (c i) (d j):=by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
private theorem frame_integrable {ι:Type*}[Fintype ι](k:ι→ι→ℝ→ℂ)(p:ι→ι→ℂ)
    (h:∀i j,Integrable (k i j)):Integrable (fun q:ℝ=>∑i,∑j,k i j q*p i j):=
  integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>(h i j).mul_const _))
private theorem frame_integral {ι:Type*}[Fintype ι](k:ι→ι→ℝ→ℂ)(p:ι→ι→ℂ)
    (h:∀i j,Integrable (k i j)):
    (∫q:ℝ,∑i,∑j,k i j q*p i j)=∑i,∑j,(∫q:ℝ,k i j q)*p i j:=by
  rw [integral_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>(h i j).mul_const _))]
  apply Finset.sum_congr rfl;intro i _
  rw [integral_finsetSum Finset.univ (fun j _=>(h i j).mul_const _)]
  exact Finset.sum_congr rfl (fun j _=>integral_mul_const _ _)

/-- All ordered interference is retained. This finite-source identity supplies an ordinary complex integral, without a separate bound on either frequency-weighted source leg. -/
theorem actual_fixed_source_frequency_pair {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c d:ι→QuantumTest):
    Integrable (fun q:ℝ=>sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceWave advanced μ a d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceWave advanced μ a d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
      (fixedSourceDerivative advanced μ a d q)) ∧
    (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceWave advanced μ a d q))=
      -(∫q:ℝ,sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceWave advanced μ a d q))-
        (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
          (fixedSourceDerivative advanced μ a d q)):=by
  let k₀(i j:ι)(q:ℝ):=star (pole advanced μ (a i) q)*pole advanced μ (a j) q
  let k₁(i j:ι):ℝ→ℂ:=forcingFrequencyKernel advanced μ (a i) (a j)
  let k₂(i j:ι):ℝ→ℂ:=inputFrequencyKernel advanced μ (a i) (a j)
  let p(i j:ι):=sourcePair (c i) (d j)
  have h₀(i j:ι):Integrable (k₀ i j):=(actual_frequency_kernel_integrable advanced μ hμ (a i) (a j)).1
  have h₁(i j:ι):Integrable (k₁ i j):=(actual_frequency_kernel_integrable advanced μ hμ (a i) (a j)).2.1
  have h₂(i j:ι):Integrable (k₂ i j):=(actual_frequency_kernel_integrable advanced μ hμ (a i) (a j)).2.2
  have e₀(q:ℝ):sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceWave advanced μ a d q)=
      ∑i,∑j,k₀ i j q*p i j:=finite_pair c d _ _
  have e₁(q:ℝ):sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceWave advanced μ a d q)=∑i,∑j,k₁ i j q*p i j:=by
    unfold fixedSourceDerivative fixedSourceWave
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact finite_pair c d _ _
  have e₂(q:ℝ):sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
      (fixedSourceDerivative advanced μ a d q)=∑i,∑j,k₂ i j q*p i j:=by
    unfold fixedSourceDerivative fixedSourceWave
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact finite_pair c d _ _
  refine ⟨(frame_integrable k₀ p h₀).congr (Eventually.of_forall (fun q=>(e₀ q).symm)),
    (frame_integrable k₁ p h₁).congr (Eventually.of_forall (fun q=>(e₁ q).symm)),
    (frame_integrable k₂ p h₂).congr (Eventually.of_forall (fun q=>(e₂ q).symm)),?_⟩
  simp_rw [e₀,e₁,e₂]
  rw [frame_integral k₀ p h₀,frame_integral k₁ p h₁,frame_integral k₂ p h₂]
  simp only [←Finset.sum_neg_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  have h:=actual_paired_frequency_integral advanced μ hμ (a i) (a j)
  change (∫q:ℝ,k₁ i j q)= -(∫q:ℝ,k₀ i j q)-(∫q:ℝ,k₂ i j q) at h
  rw [h]
  ring

def fixedSourceSecondDerivative {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(a:ι→ℝ)(c:ι→QuantumTest)(q:ℝ):QuantumTest:=
  ∑i,((2:ℂ)*(pole advanced μ (a i) q)^3) • c i

theorem actual_fixed_derivative_frequency_pair {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c d:ι→QuantumTest):
    Integrable (fun q:ℝ=>sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceDerivative advanced μ a d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceDerivative advanced μ a d q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
      (fixedSourceSecondDerivative advanced μ a d q)) ∧
    (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceDerivative advanced μ a d q))=
      -(∫q:ℝ,sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceDerivative advanced μ a d q))-
        (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
          (fixedSourceSecondDerivative advanced μ a d q)):=by
  let k₀(i j:ι)(q:ℝ):=star (pole advanced μ (a i) q)*(pole advanced μ (a j) q)^2
  let k₁(i j:ι):ℝ→ℂ:=forcingDerivativeKernel advanced μ (a i) (a j)
  let k₂(i j:ι):ℝ→ℂ:=inputDerivativeKernel advanced μ (a i) (a j)
  let p(i j:ι):=sourcePair (c i) (d j)
  have h₀(i j:ι):Integrable (k₀ i j):=(actual_derivative_kernel_integrable advanced μ hμ (a i) (a j)).1
  have h₁(i j:ι):Integrable (k₁ i j):=(actual_derivative_kernel_integrable advanced μ hμ (a i) (a j)).2.1
  have h₂(i j:ι):Integrable (k₂ i j):=(actual_derivative_kernel_integrable advanced μ hμ (a i) (a j)).2.2
  have e₀(q:ℝ):sourcePair (fixedSourceWave advanced μ a c q) (fixedSourceDerivative advanced μ a d q)=
      ∑i,∑j,k₀ i j q*p i j:=finite_pair c d _ _
  have e₁(q:ℝ):sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a c q)
      (fixedSourceDerivative advanced μ a d q)=∑i,∑j,k₁ i j q*p i j:=by
    unfold fixedSourceDerivative
    rw [Finset.smul_sum]
    simp only [smul_smul]
    rw [finite_pair]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    dsimp only [k₁,p,forcingDerivativeKernel,forcingFrequencyKernel]
    ring
  have e₂(q:ℝ):sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a c q)
      (fixedSourceSecondDerivative advanced μ a d q)=∑i,∑j,k₂ i j q*p i j:=by
    unfold fixedSourceSecondDerivative fixedSourceWave
    rw [Finset.smul_sum]
    simp only [smul_smul]
    rw [finite_pair]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    dsimp only [k₂,p,inputDerivativeKernel,inputFrequencyKernel]
    ring
  refine ⟨(frame_integrable k₀ p h₀).congr (Eventually.of_forall (fun q=>(e₀ q).symm)),
    (frame_integrable k₁ p h₁).congr (Eventually.of_forall (fun q=>(e₁ q).symm)),
    (frame_integrable k₂ p h₂).congr (Eventually.of_forall (fun q=>(e₂ q).symm)),?_⟩
  simp_rw [e₀,e₁,e₂]
  rw [frame_integral k₀ p h₀,frame_integral k₁ p h₁,frame_integral k₂ p h₂]
  simp only [←Finset.sum_neg_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  have h:=actual_paired_derivative_integral advanced μ hμ (a i) (a j)
  change (∫q:ℝ,k₁ i j q)= -(∫q:ℝ,k₀ i j q)-(∫q:ℝ,k₂ i j q) at h
  rw [h]
  ring

private theorem power_pair_integrable {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c d:ι→QuantumTest)(r s:ℕ):
    Integrable (fun q:ℝ=>sourcePair (∑i,(pole advanced μ (a i) q)^(r+1) • c i)
      (∑j,(pole advanced μ (a j) q)^(s+1) • d j)):=by
  have h:=frame_integrable (fun i j q=>star ((pole advanced μ (a i) q)^(r+1))*(pole advanced μ (a j) q)^(s+1))
    (fun i j=>sourcePair (c i) (d j)) (fun i j=>actual_pole_power_pair_integrable advanced μ hμ (a i) (a j) r s)
  exact h.congr (Eventually.of_forall (fun q=>(finite_pair c d _ _).symm))

theorem actual_fixed_jet_pair_integrable {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c₀ c₁ d₀ d₁:ι→QuantumTest):
    Integrable (fun q:ℝ=>sourcePair
      (fixedSourceWave advanced μ a c₀ q+fixedSourceDerivative advanced μ a c₁ q)
      (fixedSourceWave advanced μ a d₀ q+fixedSourceDerivative advanced μ a d₁ q)):=by
  have h00:=power_pair_integrable advanced μ hμ a c₀ d₀ 0 0
  have h01:=power_pair_integrable advanced μ hμ a c₀ d₁ 0 1
  have h10:=power_pair_integrable advanced μ hμ a c₁ d₀ 1 0
  have h11:=power_pair_integrable advanced μ hμ a c₁ d₁ 1 1
  simp only [zero_add,one_add_one_eq_two,pow_one] at h00 h01 h10 h11
  apply ((h00.add h01).add (h10.add h11)).congr
  apply Eventually.of_forall;intro q
  simp only [Pi.add_apply,fixedSourceWave,fixedSourceDerivative,sourcePair,map_add,inner_add_left,inner_add_right]
  ring

theorem actual_fixed_wave_derivative {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c:ι→QuantumTest)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (fixedSourceWave advanced μ a c r))
      (embed (fixedSourceDerivative advanced μ a c q)) q:=by
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset ι)) (fun i _=>
    (actual_physical_pole_derivative advanced μ hμ (a i) q).smul_const (embed (c i)))
  simpa only [fixedSourceWave,fixedSourceDerivative,map_sum,map_smul] using! h

theorem actual_fixed_derivative_derivative {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(c:ι→QuantumTest)(q:ℝ):
    HasDerivAt (fun r:ℝ=>embed (fixedSourceDerivative advanced μ a c r))
      (embed (fixedSourceSecondDerivative advanced μ a c q)) q:=by
  have he(i:ι):HasDerivAt (fun r:ℝ=>(pole advanced μ (a i) r)^2)
      ((2:ℂ)*(pole advanced μ (a i) q)^3) q:=by
    convert! (actual_physical_pole_derivative advanced μ hμ (a i) q).pow 2 using 1
    ring
  have h:=HasDerivAt.fun_sum (u:=(Finset.univ:Finset ι)) (fun i _=> (he i).smul_const (embed (c i)))
  simpa only [fixedSourceDerivative,fixedSourceSecondDerivative,map_sum,map_smul] using! h

/-- The mixed single/double-pole response keeps its actual derivative in the signed paired transport. -/
theorem actual_fixed_jet_frequency_pair {ι:Type*}[Fintype ι](advanced:Bool)(μ:ℝ)(hμ:0<μ)
    (a:ι→ℝ)(f c d:ι→QuantumTest):
    let v:=fun q=>fixedSourceWave advanced μ a c q+fixedSourceDerivative advanced μ a d q
    let vprime:=fun q=>fixedSourceDerivative advanced μ a c q+fixedSourceSecondDerivative advanced μ a d q
    Integrable (fun q:ℝ=>sourcePair (fixedSourceWave advanced μ a f q) (v q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a f q) (v q)) ∧
    Integrable (fun q:ℝ=>sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a f q) (vprime q)) ∧
    (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceDerivative advanced μ a f q) (v q))=
      -(∫q:ℝ,sourcePair (fixedSourceWave advanced μ a f q) (v q))-
      (∫q:ℝ,sourcePair (actualFrequency advanced μ q • fixedSourceWave advanced μ a f q) (vprime q)):=by
  dsimp only
  have hc:=actual_fixed_source_frequency_pair advanced μ hμ a f c
  have hd:=actual_fixed_derivative_frequency_pair advanced μ hμ a f d
  have add_right(u v w:QuantumTest):sourcePair u (v+w)=sourcePair u v+sourcePair u w:=by
    simp only [sourcePair,map_add,inner_add_right]
  simp only [add_right]
  refine ⟨hc.1.add hd.1,hc.2.1.add hd.2.1,hc.2.2.1.add hd.2.2.1,?_⟩
  rw [integral_add hc.2.1 hd.2.1,integral_add hc.1 hd.1,integral_add hc.2.2.1 hd.2.2.1,
    hc.2.2.2,hd.2.2.2]
  ring
end LowEnergy.InputForceFrequencyPayment
