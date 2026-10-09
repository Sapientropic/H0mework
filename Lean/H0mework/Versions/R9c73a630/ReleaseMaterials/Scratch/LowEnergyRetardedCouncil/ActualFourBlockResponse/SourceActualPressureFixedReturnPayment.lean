import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureMomentPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualPressureFixedReturnPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceNativeCutoffContact SourceResolventBandLimit
open ActualMixedCovarianceTail ActualMixedWindowGram ActualVectorJointCost ActualScalarPhaseJet
open ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment ActualCompensatedQuadraticWardMoment
open ActualBalancedPressureMomentPayment ActualBalancedLocalizationContactReturn ActualBalancedPressureWardPayment
open ActualShiftedQuadraticWardPayment SourceInverseFullResponse SourceScalarPositiveBulkWard
open SourceJointResidualEnergy SourceRetardedGraph SourceInverseNoetherChannelGap
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair coreCovariance resolventCore compressionCore diagonalAction
  pressureFullJet pressureOperator phaseSecond phaseGenerator
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K

elab "paid_fixed_pressure%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureMomentPayment 0) "LowEnergy") "ActualBalancedPressureMomentPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):(causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

private def covWord:List End → ℕ → ℕ → Index → (z:ℂ) → z.im≠0 → QuantumTest → QuantumTest → ℂ
  | [],m,ell,F,z,hz,f,h=>sourcePair f (coreCovariance m ell F z hz h)
  | G::word,m,ell,F,z,hz,f,h=>-covWord word m ell F z hz (G f) h-covWord word m ell F z hz f (G h)

private theorem cov_pair_window(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair f (coreCovariance m ell F z hz h)=(paid_phase_moment% windowPair) m ell F z f h := by
  rw [actual_core_covariance_pair]
  rfl

private theorem cov_word_continuous(word:List End)(advanced:Bool)(μ:ℝ)(hμ:0 < μ)
    (m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>covWord word m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) f h) := by
  induction word generalizing f h with
  | nil=>
    simp_rw [covWord,cov_pair_window]
    exact ((paid_phase_moment% window_continuous) advanced μ hμ m ell F f).inner (𝕜:=ℂ)
      ((paid_phase_moment% window_continuous) advanced μ hμ m ell F h)
  | cons G word ih=>exact (ih (G f) h).neg.sub (ih f (G h))

private theorem cov_word_tail(word:List End)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖covWord word m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal ε := by
  induction word generalizing f h with
  | nil=>
    simp only [covWord,cov_pair_window]
    exact (paid_phase_moment% window_pair_tail) μ hμ f h
  | cons G word ih=>
    intro ε hε
    obtain ⟨N1,h1⟩:=ih (G f) h (ε/2) (by positivity)
    obtain ⟨N2,h2⟩:=ih f (G h) (ε/2) (by positivity)
    refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
    filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF1 hF2
    intro advanced
    let p(a b:QuantumTest)(w:ℝ):ℂ:=covWord word m ell F (causalFrequency advanced μ w)
      (nonreal advanced μ hμ w) a b
    have hp(a b:QuantumTest):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p a b w‖):=
      ENNReal.measurable_ofReal.comp (cov_word_continuous word advanced μ hμ m ell F a b).norm.measurable
    have hn(a b:ℂ):‖-a-b‖ ≤ ‖a‖+‖b‖ := by
      simpa only [norm_neg] using norm_sub_le (-a) b
    change (∫⁻w:ℝ,ENNReal.ofReal ‖-p (G f) h w-p f (G h) w‖) ≤ _
    apply (lintegral_mono (μ:=volume) (fun w=>ENNReal.ofReal_le_ofReal (hn _ _))).trans
    simp_rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    rw [lintegral_add_left (hp _ _)]
    apply (add_le_add (hF1 advanced) (hF2 advanced)).trans_eq
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

private theorem matrix_nil(P:PairMatrix):(paid_pressure_moment% wordMatrix) [] P=P := rfl
private theorem matrix_cons(G:End)(word:List End)(P:PairMatrix):
    (paid_pressure_moment% wordMatrix) (G::word) P=
      pairDelta G ((paid_pressure_moment% wordMatrix) word P) := rfl
private theorem matrix_append(word rest:List End)(P:PairMatrix):
    (paid_pressure_moment% wordMatrix) (word++rest) P=
      (paid_pressure_moment% wordMatrix) word ((paid_pressure_moment% wordMatrix) rest P) := by
  induction word with
  | nil=>rfl
  | cons G word ih=>rw [List.cons_append,matrix_cons,matrix_cons,ih]

private theorem matrix_cov_source(word:List End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (f h:QuantumTest)(A B:End):
    (paid_pressure_moment% wordMatrix) word (responseRead f h (coreCovariance m ell F z hz)) A B=
      covWord word m ell F z hz (A f) (B h) := by
  induction word generalizing A B with
  | nil=>rfl
  | cons G word ih=>
    rw [matrix_cons]
    change -(paid_pressure_moment% wordMatrix) word (responseRead f h (coreCovariance m ell F z hz)) (G*A) B-
      (paid_pressure_moment% wordMatrix) word (responseRead f h (coreCovariance m ell F z hz)) A (G*B)=_
    rw [ih,ih]
    rfl

private theorem response_phase(f h:QuantumTest)(X:End):
    responseRead f h (phaseSecond X)=
      (paid_pressure_moment% wordMatrix) [phaseGenerator,phaseGenerator] (responseRead f h X) := by
  have hp(Y:End):responseRead f h (phaseJet Y)=pairDelta phaseGenerator (responseRead f h Y) := by
    unfold phaseJet
    exact (paid_shifted_response% response_delta) phaseGenerator (paid_quadratic_phase% phase_skew) f h Y
  simp only [phaseSecond,LinearMap.comp_apply,matrix_cons,matrix_nil,hp]

private def fullWord(i:Fin 8):List End :=
  (paid_fixed_pressure% pressureWord) i++[phaseGenerator,phaseGenerator]
private def fixedJetPair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  sourcePair f (pressureFullJet (coreCovariance m ell F z hz) h)

/-- These are the same source A/G/Phi words, followed by both actual phase
jets. No additional Phi shift or commuting of ordered words is used. -/
theorem actual_fixed_pressure_pair_words(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    fixedJetPair m ell F z hz f h=∑i:Fin 8,(paid_fixed_pressure% pressureCoefficient) i*
      covWord (fullWord i) m ell F z hz f h := by
  have hp:responseRead f h (pressureFullJet (coreCovariance m ell F z hz))=
      pressureMomentMatrix ((paid_pressure_moment% wordMatrix) [phaseGenerator,phaseGenerator]
        (responseRead f h (coreCovariance m ell F z hz))) := by
    simp only [pressureFullJet,LinearMap.comp_apply,(paid_fixed_pressure% response_pressure),response_phase]
  rw [(paid_fixed_pressure% pressure_matrix_words)] at hp
  have he:=congrArg (fun P:PairMatrix=>P 1 1) hp
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,←matrix_append,
    matrix_cov_source,Module.End.one_apply] at he
  unfold fixedJetPair fullWord
  exact he

private theorem fixed_pair_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖fixedJetPair m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C:ℝ:=∑i:Fin 8,‖(paid_fixed_pressure% pressureCoefficient) i‖
  have hC:0 ≤ C:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let d:ℝ:=ε/(C+1)
  have hd:0 < d := by dsimp only [d];positivity
  choose N hN using (fun i:Fin 8=>cov_word_tail (fullWord i) μ hμ f h d hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hF:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 8,∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖covWord (fullWord i) m ell F (causalFrequency advanced μ w)
        (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal d := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hF] with F hF
  intro advanced
  let p(i:Fin 8)(w:ℝ):ℂ:=covWord (fullWord i) m ell F (causalFrequency advanced μ w)
    (nonreal advanced μ hμ w) f h
  have hm(i:Fin 8):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p i w‖):=
    ENNReal.measurable_ofReal.comp (cov_word_continuous (fullWord i) advanced μ hμ m ell F f h).norm.measurable
  simp_rw [actual_fixed_pressure_pair_words]
  apply (lintegral_mono (μ:=volume) (fun w=>ENNReal.ofReal_le_ofReal (norm_sum_le Finset.univ _))).trans
  simp_rw [norm_mul]
  have ho(w:ℝ):ENNReal.ofReal (∑i:Fin 8,‖(paid_fixed_pressure% pressureCoefficient) i‖*‖p i w‖)=
      ∑i:Fin 8,ENNReal.ofReal ‖(paid_fixed_pressure% pressureCoefficient) i‖*ENNReal.ofReal ‖p i w‖ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
  change (∫⁻w:ℝ,ENNReal.ofReal (∑i:Fin 8,‖(paid_fixed_pressure% pressureCoefficient) i‖*‖p i w‖)) ≤ _
  simp_rw [ho]
  rw [lintegral_finsetSum _ (fun i _=>(hm i).const_mul _)]
  simp_rw [lintegral_const_mul _ (hm _)]
  have hb:∑i:Fin 8,ENNReal.ofReal ‖(paid_fixed_pressure% pressureCoefficient) i‖*
      (∫⁻w:ℝ,ENNReal.ofReal ‖p i w‖) ≤
      ∑i:Fin 8,ENNReal.ofReal ‖(paid_fixed_pressure% pressureCoefficient) i‖*ENNReal.ofReal d := by
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact hF i advanced
  apply hb.trans
  simp_rw [←ENNReal.ofReal_mul (norm_nonneg _)]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) hd.le),←Finset.sum_mul]
  apply ENNReal.ofReal_le_ofReal
  change C*d ≤ ε
  dsimp only [d]
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0 < C+1)).mpr
  linarith only [hε]

/-- The fixed square orbit is generated on one ordinary source-filter event;
no CF/H0 replacement is silently assumed. -/
theorem actual_fixed_source_square_event(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),(compressionCore F*compressionCore F) g=
      (diagonalAction*diagonalAction) g := by
  filter_upwards [(paid_phase_moment% fixed_compression) g,
    (paid_phase_moment% fixed_compression) (diagonalAction g)] with F h0 h1
  simp only [Module.End.mul_apply,h0,h1]

/-- Direct correction consumer: the real moving CF square input is paid by
actual fixed source jets, with a common N before F and both causes. -/
theorem actual_pressure_fixed_return_tail(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖sourcePair g
          (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
            (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=fixed_pair_tail μ hμ g ((diagonalAction*diagonalAction) g) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_fixed_source_square_event g] with F hF hSq
  intro advanced
  rw [hSq]
  exact hF advanced

private theorem complex_price(v:ℝ→ℂ)(hv:Continuous v)(b:ℝ)(hb:0 ≤ b)
    (hp:(∫⁻w:ℝ,ENNReal.ofReal ‖v w‖) ≤ ENNReal.ofReal b):
    Integrable v ∧ (∫w:ℝ,‖v w‖) ≤ b := by
  have hf:HasFiniteIntegral v := by
    rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt hp ENNReal.ofReal_lt_top
  have hi:Integrable v:=⟨hv.aestronglyMeasurable,hf⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi.norm (Eventually.of_forall (fun _=>norm_nonneg _))
  rw [←he] at hp
  exact ⟨hi,(ENNReal.ofReal_le_ofReal_iff hb).mp hp⟩

private theorem fixed_pair_continuous(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>fixedJetPair m ell F (causalFrequency advanced μ w)
      (nonreal advanced μ hμ w) f h) := by
  simp_rw [actual_fixed_pressure_pair_words]
  exact continuous_finsetSum Finset.univ (fun i _=>continuous_const.mul
    (cov_word_continuous (fullWord i) advanced μ hμ m ell F f h))

/-- The actual correction slot has an ordinary complex norm-L1 price,
paid after its own same-F fixed-square source event. -/
theorem actual_pressure_fixed_return_price(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>sourcePair g
          (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
            (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))) ∧
        (∫w:ℝ,‖sourcePair g (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))‖) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_pressure_fixed_return_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_fixed_source_square_event g] with F hF hSq
  intro advanced
  have hv:Continuous (fun w:ℝ=>sourcePair g
      (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
        (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))) := by
    rw [hSq]
    exact fixed_pair_continuous advanced μ hμ m ell F g ((diagonalAction*diagonalAction) g)
  exact complex_price _ hv ε hε.le (hF advanced)

/-- Same actual corrected invoice, with only the now-paid fixed-square debit
cleared. All moving Own, ordered cross, CF, radial and contact responsibilities remain. -/
def fixedReturnClearedInvoice(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  correctedSourceNativeInvoice advanced μ hμ m ell F g w+
    (1/12:ℝ)*(sourcePair g (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
      (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))).re

private theorem source_mu_positive:0 < sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large

/-- Direct original-mu signed consumer: the fixed jet debit is cleared
inside the whole native/Own lower bound, with no target-current budget. -/
theorem actual_source_fixed_return_native_lower(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w) g).re) ≥
          (∫w:ℝ,fixedReturnClearedInvoice advanced sourceMu source_mu_positive m ell F g w)-ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=actual_source_native_pressure_integral_payment g (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_pressure_fixed_return_price sourceMu source_mu_positive g (6*ε) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF1 hF2
  intro advanced
  obtain ⟨hc,hcprice⟩:=hF1 advanced
  obtain ⟨hi,hiprice⟩:=hF2 advanced
  have hr:=hi.re.const_mul (1/12:ℝ)
  have he:(∫w:ℝ,fixedReturnClearedInvoice advanced sourceMu source_mu_positive m ell F g w)=
      (∫w:ℝ,correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g w)+
      (1/12:ℝ)*(∫w:ℝ,(sourcePair g (pressureFullJet (coreCovariance m ell F
        (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w))
        ((compressionCore F*compressionCore F) g))).re) := by
    unfold fixedReturnClearedInvoice
    have hh:=integral_add hc hr
    simp only [RCLike.re_to_complex] at hh
    rw [hh,integral_const_mul]
  have hb:|(∫w:ℝ,(sourcePair g (pressureFullJet (coreCovariance m ell F
      (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w))
      ((compressionCore F*compressionCore F) g))).re)| ≤ 6*ε := by
    have heI:(∫w:ℝ,sourcePair g (pressureFullJet (coreCovariance m ell F
        (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w))
        ((compressionCore F*compressionCore F) g))).re=
        ∫w:ℝ,(sourcePair g (pressureFullJet (coreCovariance m ell F
          (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w))
          ((compressionCore F*compressionCore F) g))).re := by
      simpa only [RCLike.re_to_complex] using (integral_re hi).symm
    rw [←heI]
    exact (Complex.abs_re_le_norm _).trans ((norm_integral_le_integral_norm _).trans hiprice)
  rw [he]
  have hlo:=(abs_le.mp hcprice).1
  have hhi:=(abs_le.mp hb).2
  linarith only [hlo,hhi]

end LowEnergy.ActualPressureFixedReturnPayment
