import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceMatterContactCoframe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceSelfAdjointTimeBalance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption
open SourceScalarPairedTransport SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair compressionCore coreTime

private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def timeSum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*c i j
private def gapCoefficient (F : Index) (J T : End) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  (Complex.I/2)*((channelValue F i : ℂ)-(channelValue F j : ℂ))*coefficient F g T (J*T) i j

private theorem time_factor (μ a b t : ℝ) :
    Complex.exp (-gap μ a b*(t : ℂ))=(Real.exp (-2*μ*t) : ℂ)*star (phase a t)*phase b t := by
  simp only [gap,phase,Complex.star_def,←Complex.exp_conj,Complex.ofReal_exp]
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  push_cast
  ring

private theorem pair_sum (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑ i,c i • channelTest F g i)) (B (∑ j,c j • channelTest F g j))=
      ∑ i,∑ j,star (c i)*c j*coefficient F g A B i j := by
  simp only [coefficient,sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_time (F : Index) (μ : ℝ) (g : diagonal.domain) (A B : End) (t : ℝ) :
    timeSum F μ (coefficient F g A B) t=(Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t)) := by
  unfold timeSum
  simp_rw [time_factor]
  rw [coreTime,pair_sum]
  simp only [Finset.mul_sum,phase]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem decay_integrable (μ a b : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-gap μ a b*(t : ℂ))) (Set.Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp [gap]
  linarith

private theorem decay_integral (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ t : ℝ in Set.Ioi 0,Complex.exp (-gap μ a b*(t : ℂ)))=(gap μ a b)⁻¹ := by
  have hn : (-gap μ a b).re<0 := by simp [gap];linarith
  rw [integral_exp_mul_complex_Ioi hn 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,div_neg,neg_div,neg_neg,one_div]

private theorem sum_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    IntegrableOn (timeSum F μ c) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))

private theorem sum_integral (F : Index) (μ : ℝ) (hμ : 0 < μ) (c : Channel F → Channel F → ℂ) :
    (∫ t : ℝ in Set.Ioi 0,timeSum F μ c t)=
      ∑ i,∑ j,(gap μ (channelValue F i) (channelValue F j))⁻¹*c i j := by
  unfold timeSum
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (decay_integrable μ (channelValue F i) (channelValue F j) hμ).mul_const _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,decay_integral μ _ _ hμ]


private def currentPairJ (F : Index) (J T : End) (p q : QuantumTest) : ℂ :=
  (Complex.I/2)*(sourcePair (T (compressionCore F p)) (J (T q))-
    sourcePair (J (T p)) (T (compressionCore F q)))

private theorem channel_gap (F : Index) (J T : End)
    (hJ : ∀ f g,sourcePair f (J g)=sourcePair (J f) g)
    (g : diagonal.domain) (u v : Channel F) :
    currentPairJ F J T (channelTest F g u) (channelTest F g v)=
      gapCoefficient F J T g u v := by
  rw [currentPairJ,actual_channel_eigen,actual_channel_eigen,map_smul,map_smul]
  have hp (c : ℝ) (a b : QuantumTest) : sourcePair ((c : ℂ) • a) b=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_left,Complex.conj_ofReal]
  have hq (c : ℝ) (a b : QuantumTest) : sourcePair a ((c : ℂ) • b)=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hp,hq,←hJ (T (channelTest F g u)) (T (channelTest F g v))]
  simp only [gapCoefficient,coefficient,Module.End.mul_apply]
  ring

private theorem diagonal_current (F : Index) (J T : End) (q : QuantumTest) :
    currentPairJ F J T q q=(-((sourcePair (T (compressionCore F q)) (J (T q))).im) : ℂ) := by
  rw [currentPairJ,(GaussNativeForm.pair_conjugate (T (compressionCore F q)) (J (T q))).symm]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

private theorem current_sum (F : Index) (J T : End) (hJ : ∀ f g,sourcePair f (J g)=sourcePair (J f) g) (g : diagonal.domain) (a : Channel F → ℂ) :
    currentPairJ F J T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*gapCoefficient F J T g i j := by
  have he : currentPairJ F J T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*currentPairJ F J T (channelTest F g i) (channelTest F g j) := by
    simp only [currentPairJ,map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,
      inner_smul_right,starRingEnd_apply,Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_comm (f := fun x i => a x * (star (a i) *
      inner ℂ (embed (J (T (channelTest F g i)))) (embed (T (compressionCore F (channelTest F g x))))))]
    simp only [←Finset.sum_sub_distrib,mul_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [channel_gap F J T hJ,gapCoefficient,coefficient,Module.End.mul_apply] using he

private theorem current_time (F : Index) (μ : ℝ) (J T : End)
    (hJ : ∀ f g,sourcePair f (J g)=sourcePair (J f) g)
    (g : diagonal.domain) (t : ℝ) :
    timeSum F μ (gapCoefficient F J T g) t=(Real.exp (-2*μ*t) : ℂ)*
      (-((sourcePair (T (compressionCore F (coreTime F g t))) (J (T (coreTime F g t)))).im) : ℂ) := by
  rw [←diagonal_current,coreTime,current_sum F J T hJ]
  unfold timeSum
  simp_rw [time_factor]
  simp only [Finset.mul_sum,phase]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem core_zero (F : Index) (g : diagonal.domain) : coreTime F g 0=coreEquiv.symm g := by
  apply embed_injective
  rw [actual_core_time,SourceFiniteUnitary.time_zero]
  simpa only [one_apply_eq_self] using! (congrArg Subtype.val (coreEquiv.apply_symm_apply g)).symm

private theorem initial_sum (F : Index) (J T : End) (g : diagonal.domain) :
    ∑ i,∑ j,coefficient F g T (J*T) i j=
      sourcePair (T (coreEquiv.symm g)) (J (T (coreEquiv.symm g))) := by
  have he := pair_time F 1 g T (J*T) 0
  simpa only [timeSum,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
    Real.exp_zero,Complex.ofReal_one,core_zero,Module.End.mul_apply] using he

attribute [local irreducible] coefficient gapCoefficient

private theorem finite_balance {ι : Type*} [Fintype ι] (μ : ℝ) (hμ : 0 < μ)
    (v : ι → ℝ) (c : ι → ι → ℂ) :
    (2*μ : ℂ)*(∑ i,∑ j,(gap μ (v i) (v j))⁻¹*c i j)=
      (∑ i,∑ j,c i j)+2*(∑ i,∑ j,(gap μ (v i) (v j))⁻¹*
        ((Complex.I/2)*((v i : ℂ)-(v j : ℂ))*c i j)) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := gap_ne μ (v i) (v j) hμ
  field_simp
  simp only [gap]
  ring

private theorem algebra_balance (F : Index) (J : End) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    (2*μ : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (J*T)) t)=
      sourcePair (T (coreEquiv.symm g)) (J (T (coreEquiv.symm g)))+
        2*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F J T g) t) := by
  rw [sum_integral F μ hμ,sum_integral F μ hμ,←initial_sum F J T g]
  simpa only [gapCoefficient] using finite_balance μ hμ (channelValue F) (coefficient F g T (J*T))


/-- Every core insertion is time integrable on the same complete finite-channel trajectory. -/
theorem actual_pair_time_integrable (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) (A B : End) :
    IntegrableOn (fun t : ℝ => (Real.exp (-2*μ*t) : ℂ)*
      sourcePair (A (coreTime F g t)) (B (coreTime F g t))) (Set.Ioi 0) :=
  (sum_integrable F μ hμ (coefficient F g A B)).congr
    (Eventually.of_forall (pair_time F μ g A B))

/-- Exact source time balance for a generated formally self-adjoint core current. -/
theorem actual_self_adjoint_time_balance (F : Index) (J : End)
    (hJ : ∀ f g,sourcePair f (J g)=sourcePair (J f) g)
    (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*
      Complex.im (sourcePair (T (compressionCore F (coreTime F g t))) (J (T (coreTime F g t))))) (Set.Ioi 0) ∧
    2*μ*(∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
      Complex.re (sourcePair (T (coreTime F g t)) (J (T (coreTime F g t)))))=
      Complex.re (sourcePair (T (coreEquiv.symm g)) (J (T (coreEquiv.symm g))))-
        2*(∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
          Complex.im (sourcePair (T (compressionCore F (coreTime F g t))) (J (T (coreTime F g t))))) := by
  have ht := sum_integrable F μ hμ (coefficient F g T (J*T))
  have hc := sum_integrable F μ hμ (gapCoefficient F J T g)
  have he (t : ℝ) : (timeSum F μ (coefficient F g T (J*T)) t).re=
      Real.exp (-2*μ*t)*Complex.re (sourcePair (T (coreTime F g t)) (J (T (coreTime F g t)))) := by
    rw [pair_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  have hj (t : ℝ) : (timeSum F μ (gapCoefficient F J T g) t).re=
      -(Real.exp (-2*μ*t)*Complex.im (sourcePair (T (compressionCore F (coreTime F g t))) (J (T (coreTime F g t))))) := by
    rw [current_time F μ J T hJ]
    simp only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mul_neg]
  have hi : IntegrableOn (fun t : ℝ => -(Real.exp (-2*μ*t)*
      Complex.im (sourcePair (T (compressionCore F (coreTime F g t))) (J (T (coreTime F g t))))))
      (Set.Ioi 0) := hc.re.congr (Eventually.of_forall hj)
  refine ⟨?_,?_⟩
  · have h := hi.neg
    convert h using 1
    funext t
    exact (neg_neg _).symm
  have hb := congrArg Complex.re (algebra_balance F J μ hμ T g)
  have htr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (J*T)) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (coefficient F g T (J*T)) t).re := (integral_re ht).symm
  have hcr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F J T g) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (gapCoefficient F J T g) t).re := (integral_re hc).symm
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,mul_zero,add_zero,sub_zero,Complex.add_re,htr,hcr,he,hj,integral_neg] at hb
  linear_combination hb

end LowEnergy.SourceSelfAdjointTimeBalance
