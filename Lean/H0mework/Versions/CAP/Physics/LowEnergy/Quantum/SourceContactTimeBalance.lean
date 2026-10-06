import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceMatterContactNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceContactTimeBalance
open SourceMatterContactNative SourceMatterContactCoframe GaussNativeForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceBulkTwoTime SourceBulkParseval SourceInverseNoetherChannelGap SourceInverseNoetherEnergy
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarOscillatorAbsorption
open SourceScalarPairedTransport SourceMovingJetFlux SourceEscapeCurrent GaussNativeEnergy SourceQuantumScalarChart
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private def gramForm (f : QuantumTest) : ℝ :=
  ∑ a : LieIndex,∑ k : Fin 3,‖embed (coframeColumn k a f)‖^2
private theorem gram_energy (f : QuantumTest) : (sourcePair f (gramAction f)).re=gramForm f :=
  original_contact_gram_energy f

def reducedCurrent : End := (GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*gramAction-
  gramAction*(GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)

def contactCurrent (F : Index) (T : End) (q : QuantumTest) : ℝ :=
  (sourcePair (raisedDefect F T q) (gramAction (T q))).im-
    (sourcePair (T q) (reducedCurrent (T q))).im/2

private theorem current_form (q : QuantumTest) :
    (sourcePair q (reducedCurrent q)).im=2*(sourcePair (diagonalAction q) (gramAction q)).im := by
  have h := original_contact_hamiltonian_current
  have he : reducedCurrent=diagonalAction*gramAction-gramAction*diagonalAction := h.symm
  rw [he]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_im]
  change (sourcePair q (diagonalAction (gramAction q))).im-(sourcePair q (gramAction (diagonalAction q))).im=_
  rw [diagonalAction_pair q (gramAction q),original_contact_gram_pair q (diagonalAction q),
    ←GaussNativeForm.pair_conjugate (diagonalAction q) (gramAction q),Complex.conj_im]
  simp only [sourcePair]
  ring

/-- The original full compression defect is retained after the native sectors leave the Gram current. -/
theorem original_contact_compression (F : Index) (T : End) (q : QuantumTest) :
    contactCurrent F T q= -(sourcePair (T (compressionCore F q)) (gramAction (T q))).im := by
  have hd : raisedDefect F T q=diagonalAction (T q)-T (compressionCore F q) := by
    simp only [raisedDefect,defectAction,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
    abel
  rw [contactCurrent,current_form,hd]
  simp only [sourcePair,map_sub,inner_sub_left,Complex.sub_im]
  ring

private def contactPair (F : Index) (T : End) (p q : QuantumTest) : ℂ :=
  (Complex.I/2)*(sourcePair (T (compressionCore F p)) (gramAction (T q))-
    sourcePair (gramAction (T p)) (T (compressionCore F q)))

private theorem diagonal_contact (F : Index) (T : End) (q : QuantumTest) :
    contactPair F T q q=(contactCurrent F T q : ℂ) := by
  have hc (p q : QuantumTest) : sourcePair q p=star (sourcePair p q) := (GaussNativeForm.pair_conjugate p q).symm
  rw [contactPair,hc (T (compressionCore F q)) (gramAction (T q)),original_contact_compression]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  ring

private theorem channel_contact (F : Index) (T : End) (g : diagonal.domain) (u v : Channel F) :
    contactPair F T (channelTest F g u) (channelTest F g v)=
      (Complex.I/2)*((channelValue F u : ℂ)-(channelValue F v : ℂ))*
        sourcePair (T (channelTest F g u)) (gramAction (T (channelTest F g v))) := by
  rw [contactPair,actual_channel_eigen,actual_channel_eigen,map_smul,map_smul]
  have hp (c : ℝ) (a b : QuantumTest) : sourcePair ((c : ℂ) • a) b=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_left,Complex.conj_ofReal]
  have hq (c : ℝ) (a b : QuantumTest) : sourcePair a ((c : ℂ) • b)=(c : ℂ)*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hp,hq,←original_contact_gram_pair]
  ring

attribute [local irreducible] sourcePair gramAction compressionCore contactCurrent gramForm coreTime

private def coefficient (F : Index) (g : diagonal.domain) (A B : End) (i j : Channel F) : ℂ :=
  sourcePair (A (channelTest F g i)) (B (channelTest F g j))
private def timeSum (F : Index) (μ : ℝ) (c : Channel F → Channel F → ℂ) (t : ℝ) : ℂ :=
  ∑ i,∑ j,Complex.exp (-gap μ (channelValue F i) (channelValue F j)*(t : ℂ))*c i j
private def gapCoefficient (F : Index) (T : End) (g : diagonal.domain) (i j : Channel F) : ℂ :=
  (Complex.I/2)*((channelValue F i : ℂ)-(channelValue F j : ℂ))*coefficient F g T (gramAction*T) i j

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

private theorem current_sum (F : Index) (T : End) (g : diagonal.domain) (a : Channel F → ℂ) :
    contactPair F T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*gapCoefficient F T g i j := by
  have he : contactPair F T (∑ i,a i • channelTest F g i) (∑ j,a j • channelTest F g j)=
      ∑ i,∑ j,star (a i)*a j*contactPair F T (channelTest F g i) (channelTest F g j) := by
    simp only [contactPair,map_sum,map_smul,sourcePair,sum_inner,inner_sum,inner_smul_left,
      inner_smul_right,starRingEnd_apply,Finset.mul_sum]
    rw [Finset.sum_comm,Finset.sum_comm (f := fun x i => a x * (star (a i) *
      inner ℂ (embed (gramAction (T (channelTest F g i)))) (embed (T (compressionCore F (channelTest F g x))))))]
    simp only [←Finset.sum_sub_distrib,mul_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [channel_contact,gapCoefficient,coefficient,Module.End.mul_apply] using he

private theorem current_time (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) (t : ℝ) :
    timeSum F μ (gapCoefficient F T g) t=(Real.exp (-2*μ*t) : ℂ)*
      (contactCurrent F T (coreTime F g t) : ℂ) := by
  rw [←diagonal_contact,coreTime,current_sum]
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

private theorem initial_sum (F : Index) (T : End) (g : diagonal.domain) :
    ∑ i,∑ j,coefficient F g T (gramAction*T) i j=
      sourcePair (T (coreEquiv.symm g)) (gramAction (T (coreEquiv.symm g))) := by
  have he := pair_time F 1 g T (gramAction*T) 0
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

private theorem algebra_balance (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    (2*μ : ℂ)*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (gramAction*T)) t)=
      sourcePair (T (coreEquiv.symm g)) (gramAction (T (coreEquiv.symm g)))+
        2*(∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F T g) t) := by
  rw [sum_integral F μ hμ,sum_integral F μ hμ,←initial_sum F T g]
  simpa only [gapCoefficient] using finite_balance μ hμ (channelValue F) (coefficient F g T (gramAction*T))

/-- Exact original contact-moment time balance; only coframe, matter and the full compression defect can drive its growth. -/
theorem actual_contact_time_balance (F : Index) (μ : ℝ) (hμ : 0 < μ) (T : End) (g : diagonal.domain) :
    IntegrableOn (fun t : ℝ => Real.exp (-2*μ*t)*contactCurrent F T (coreTime F g t)) (Set.Ioi 0) ∧
    2*μ*coframeTime F μ T g=(sourcePair (T (coreEquiv.symm g)) (gramAction (T (coreEquiv.symm g)))).re+
      2*(∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*contactCurrent F T (coreTime F g t)) := by
  have ht := sum_integrable F μ hμ (coefficient F g T (gramAction*T))
  have hc := sum_integrable F μ hμ (gapCoefficient F T g)
  have he (t : ℝ) : (timeSum F μ (coefficient F g T (gramAction*T)) t).re=
      Real.exp (-2*μ*t)*gramForm (T (coreTime F g t)) := by
    rw [pair_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact congrArg (fun r : ℝ => Real.exp (-2*μ*t)*r) (gram_energy _)
  have hj (t : ℝ) : (timeSum F μ (gapCoefficient F T g) t).re=
      Real.exp (-2*μ*t)*contactCurrent F T (coreTime F g t) := by
    rw [current_time,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨hc.re.congr (Eventually.of_forall hj),?_⟩
  have hb := congrArg Complex.re (algebra_balance F μ hμ T g)
  have htr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (coefficient F g T (gramAction*T)) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (coefficient F g T (gramAction*T)) t).re := (integral_re ht).symm
  have hcr : (∫ t : ℝ in Set.Ioi 0,timeSum F μ (gapCoefficient F T g) t).re=
      ∫ t : ℝ in Set.Ioi 0,(timeSum F μ (gapCoefficient F T g) t).re := (integral_re hc).symm
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,mul_zero,add_zero,sub_zero,Complex.add_re,htr,hcr,he,hj,gram_energy] at hb
  rw [gram_energy]
  simpa only [coframeTime,gramForm] using hb


end LowEnergy.SourceContactTimeBalance
