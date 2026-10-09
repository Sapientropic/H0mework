import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPressureContactReturnPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualPressureProductCrossPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet SourceClockPhiSecondBulk
open SourceCoframeVolumeCurrent ActualScalarPhaseJet ActualScalarPhaseFrequencyReturn
open ActualBalancedPressureMomentPayment ActualMixedWindowGram ActualCompensatedWardOperatorReturn
open ActualShiftedQuadraticWardPayment ActualPressureFixedReturnPayment ActualPressureContactReturnPayment
open SourceResolventBandLimit SourceNativeCutoffContact SourceInverseFullResponse
open ActualMixedCovarianceTail ActualVectorJointCost ActualScalarPhaseQuadraticMoment SourceScalarPositiveBulkWard
open ActualBalancedPressureWardPayment SourceRetardedGraph
open SourceClockYukawaCubicCurrent SourceJointResidualEnergy SourceScalarPairedTransport
open Lean Meta Elab Term Filter MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
private abbrev End:=QuantumTest →ₗ[ℂ]QuantumTest
attribute [local irreducible] sourcePair compressionCore diagonalAction phaseSquareOwn pressureFullJet
  deltaPhi deltaGauge scaleDerivative secondJet phaseJet phaseSecond coreCovariance resolventCore phaseGenerator
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K

elab "paid_invoice_fixed%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail 0) "LowEnergy")
      "ActualMixedWardMomentTail") "fixed_compression")

private def fixedReturn(A:Index→End)(B:End):Prop:=
  ∀f:QuantumTest,∀ᶠF in (sourceFilter:Filter Index),A F f=B f
private theorem constant_return(B:End):fixedReturn (fun _=>B) B:=
  fun _=>Eventually.of_forall (fun _=>rfl)
private theorem add_return{A C:Index→End}{B D:End}
    (hA:fixedReturn A B)(hC:fixedReturn C D):
    fixedReturn (fun F=>A F+C F) (B+D):=by
  intro f
  filter_upwards [hA f,hC f] with F ha hc
  simp only [LinearMap.add_apply,ha,hc]
private theorem sub_return{A C:Index→End}{B D:End}
    (hA:fixedReturn A B)(hC:fixedReturn C D):
    fixedReturn (fun F=>A F-C F) (B-D):=by
  intro f
  filter_upwards [hA f,hC f] with F ha hc
  simp only [LinearMap.sub_apply,ha,hc]
private theorem smul_return(c:ℂ){A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>c • A F) (c • B):=by
  intro f
  filter_upwards [hA f] with F ha
  simp only [LinearMap.smul_apply,ha]
private theorem mul_return{A C:Index→End}{B D:End}
    (hA:fixedReturn A B)(hC:fixedReturn C D):
    fixedReturn (fun F=>A F*C F) (B*D):=by
  intro f
  filter_upwards [hC f,hA (D f)] with F hc ha
  simp only [Module.End.mul_apply,hc,ha]
private theorem comm_return(X:End){A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>X*A F-A F*X) (X*B-B*X):=
  sub_return (mul_return (constant_return X) hA) (mul_return hA (constant_return X))
private theorem phi_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>deltaPhi (A F)) (deltaPhi B):=by
  simpa only [←SourceScalarAffineScaleTransport.generator_commutator] using
    comm_return SourceScalarAffineScaleTransport.generator hA
private theorem gauge_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>deltaGauge (A F)) (deltaGauge B):=by
  simpa only [←SourceGaugeScaleTransport.generator_commutator] using
    comm_return SourceGaugeScaleTransport.generator hA
private theorem coframe_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>scaleDerivative (A F)) (scaleDerivative B):=by
  simpa only [scaleDerivative,LinearMap.coe_mk,AddHom.coe_mk] using
    smul_return (3*Complex.I/2) (comm_return dilation hA)
private theorem phase_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>phaseJet (A F)) (phaseJet B):=by
  simpa only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk] using
    comm_return phaseGenerator hA
private theorem phase_second_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>phaseSecond (A F)) (phaseSecond B):=by
  simpa only [phaseSecond,LinearMap.comp_apply] using phase_return (phase_return hA)
private theorem second_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>secondJet (A F)) (secondJet B):=by
  have h:=sub_return (phi_return hA) (gauge_return hA)
  have hh:=sub_return h (gauge_return h)
  simpa only [secondJet,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply] using hh
private theorem projection_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>nonmagneticProjection (A F)) (nonmagneticProjection B):=by
  have h:=add_return (gauge_return hA) (smul_return 2 hA)
  have hh:=sub_return hA (smul_return (1/24) (gauge_return h))
  simpa only [nonmagneticProjection,LinearMap.sub_apply,LinearMap.add_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.id_apply] using hh
private theorem pressure_return{A:Index→End}{B:End}(hA:fixedReturn A B):
    fixedReturn (fun F=>pressureFullJet (A F)) (pressureFullJet B):=by
  have h:=projection_return (second_return (phase_second_return hA))
  have hh:=sub_return (sub_return (smul_return 3 (phi_return h))
    (smul_return 12 (gauge_return h))) (smul_return 6 (coframe_return h))
  simpa only [pressureFullJet,pressureOperator,pressureDerivation,LinearMap.comp_apply,
    LinearMap.sub_apply,LinearMap.smul_apply] using hh

/-- A fixed original source input closes the entire ordered OwnSquare jet;
no moving retarded input is substituted into this return. -/
theorem actual_pressure_own_fixed_source_zero(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),pressureFullJet (phaseSquareOwn F) g=0:=by
  have hCF:fixedReturn compressionCore diagonalAction:=paid_invoice_fixed%
  have hSq:=mul_return hCF hCF
  have hOwn:=sub_return (constant_return (diagonalAction*diagonalAction)) hSq
  have hJ:=pressure_return hOwn g
  filter_upwards [hJ] with F hF
  rw [sub_self,pressureFullJet.map_zero] at hF
  simpa only [phaseSquareOwn,LinearMap.zero_apply] using hF

/-- The actual covariance correction's whole OwnSquare word vanishes on
one cofinal source frame before every cutoff and non-real frequency. -/
theorem actual_covariance_own_correction_zero(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      sourcePair g ((coreCovariance m ell F z hz*pressureFullJet (phaseSquareOwn F)) g)=0:=by
  filter_upwards [actual_pressure_own_fixed_source_zero g] with F hF
  intro m ell z hz
  simp only [Module.End.mul_apply,hF,map_zero,sourcePair,inner_zero_right]

elab "paid_cross_fixed%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPressureFixedReturnPayment 0) "LowEnergy") "ActualPressureFixedReturnPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
private theorem nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):(causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

private def squareCovWord:List End → ℕ → ℕ → Index → (z:ℂ) → z.im≠0 → QuantumTest → QuantumTest → ℂ
  | [],m,ell,F,z,hz,f,h=>sourcePair f (coreCovariance m ell F z hz ((compressionCore F*compressionCore F) h))
  | G::word,m,ell,F,z,hz,f,h=>-squareCovWord word m ell F z hz (G f) h-squareCovWord word m ell F z hz f (G h)
private theorem square_word_continuous(word:List End)(advanced:Bool)(μ:ℝ)(hμ:0 < μ)
    (m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>squareCovWord word m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) f h) := by
  induction word generalizing f h with
  | nil=>exact (paid_cross_fixed% cov_word_continuous) [] advanced μ hμ m ell F f ((compressionCore F*compressionCore F) h)
  | cons G word ih=>exact (ih (G f) h).neg.sub (ih f (G h))
private theorem square_word_tail(word:List End)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖squareCovWord word m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal ε := by
  induction word generalizing f h with
  | nil=>
    intro ε hε
    obtain ⟨N,hN⟩:=(paid_cross_fixed% cov_word_tail) [] μ hμ f ((diagonalAction*diagonalAction) h) ε hε
    refine ⟨N,fun m hm ell hml=>?_⟩
    filter_upwards [hN m hm ell hml,actual_fixed_source_square_event h] with F hF hSq
    intro advanced
    simp only [squareCovWord,hSq]
    exact hF advanced
  | cons G word ih=>
    intro ε hε
    obtain ⟨N1,h1⟩:=ih (G f) h (ε/2) (by positivity)
    obtain ⟨N2,h2⟩:=ih f (G h) (ε/2) (by positivity)
    refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
    filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF1 hF2
    intro advanced
    let p(a b:QuantumTest)(w:ℝ):ℂ:=squareCovWord word m ell F (causalFrequency advanced μ w)
      (nonreal advanced μ hμ w) a b
    have hp(a b:QuantumTest):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p a b w‖):=
      ENNReal.measurable_ofReal.comp (square_word_continuous word advanced μ hμ m ell F a b).norm.measurable
    have hn(a b:ℂ):‖-a-b‖ ≤ ‖a‖+‖b‖ := by simpa only [norm_neg] using norm_sub_le (-a) b
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
    (paid_pressure_moment% wordMatrix) (G::word) P=pairDelta G ((paid_pressure_moment% wordMatrix) word P) := rfl
private theorem matrix_square_source(word:List End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (f h:QuantumTest)(A B:End):
    (paid_pressure_moment% wordMatrix) word (responseRead f h
      (coreCovariance m ell F z hz*(compressionCore F*compressionCore F))) A B=
      squareCovWord word m ell F z hz (A f) (B h) := by
  induction word generalizing A B with
  | nil=>rfl
  | cons G word ih=>
    rw [matrix_cons]
    change -(paid_pressure_moment% wordMatrix) word (responseRead f h
      (coreCovariance m ell F z hz*(compressionCore F*compressionCore F))) (G*A) B-
      (paid_pressure_moment% wordMatrix) word (responseRead f h
        (coreCovariance m ell F z hz*(compressionCore F*compressionCore F))) A (G*B)=_
    rw [ih,ih]
    rfl
private def fullWord(i:Fin 8):List End :=(paid_fixed_pressure% pressureWord) i++[phaseGenerator,phaseGenerator]
private def squareJetPair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  sourcePair f (pressureFullJet (coreCovariance m ell F z hz*(compressionCore F*compressionCore F)) h)
private theorem square_jet_words(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    squareJetPair m ell F z hz f h=∑i:Fin 8,(paid_fixed_pressure% pressureCoefficient) i*
      squareCovWord (fullWord i) m ell F z hz f h := by
  have hp:responseRead f h (pressureFullJet (coreCovariance m ell F z hz*(compressionCore F*compressionCore F)))=
      pressureMomentMatrix ((paid_pressure_moment% wordMatrix) [phaseGenerator,phaseGenerator]
        (responseRead f h (coreCovariance m ell F z hz*(compressionCore F*compressionCore F)))) := by
    simp only [pressureFullJet,LinearMap.comp_apply,(paid_fixed_pressure% response_pressure),(paid_cross_fixed% response_phase)]
  rw [(paid_fixed_pressure% pressure_matrix_words)] at hp
  have he:=congrArg (fun P:PairMatrix=>P 1 1) hp
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,←(paid_cross_fixed% matrix_append),
    matrix_square_source,Module.End.one_apply] at he
  unfold squareJetPair fullWord
  exact he
private theorem square_jet_continuous(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>squareJetPair m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) f h) := by
  simp_rw [square_jet_words]
  exact continuous_finsetSum Finset.univ (fun i _=>continuous_const.mul
    (square_word_continuous (fullWord i) advanced μ hμ m ell F f h))

private theorem square_jet_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖squareJetPair m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C:ℝ:=∑i:Fin 8,‖(paid_fixed_pressure% pressureCoefficient) i‖
  have hC:0 ≤ C:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let d:ℝ:=ε/(C+1)
  have hd:0 < d := by dsimp only [d];positivity
  choose N hN using (fun i:Fin 8=>square_word_tail (fullWord i) μ hμ f h d hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hF:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 8,∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖squareCovWord (fullWord i) m ell F (causalFrequency advanced μ w)
        (nonreal advanced μ hμ w) f h‖) ≤ ENNReal.ofReal d := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hF] with F hF
  intro advanced
  let p(i:Fin 8)(w:ℝ):ℂ:=squareCovWord (fullWord i) m ell F (causalFrequency advanced μ w)
    (nonreal advanced μ hμ w) f h
  have hm(i:Fin 8):Measurable (fun w:ℝ=>ENNReal.ofReal ‖p i w‖):=
    ENNReal.measurable_ofReal.comp (square_word_continuous (fullWord i) advanced μ hμ m ell F f h).norm.measurable
  simp_rw [square_jet_words]
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


/-- The entire ordered pressure jet of the raw CF square returns only
on a fixed original source input. -/
theorem actual_pressure_square_fixed_source_return(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),pressureFullJet (compressionCore F*compressionCore F) g=
      balancedPressureJet ActualSecondPressureMagneticPayment.nonmagneticSecondField g := by
  have hCF:fixedReturn compressionCore diagonalAction:=paid_invoice_fixed%
  have hSq:=pressure_return (mul_return hCF hCF) g
  filter_upwards [hSq] with F hF
  rw [actual_pressure_source_field] at hF
  exact hF

private theorem square_jet_price(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>squareJetPair m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) f h) ∧
        (∫w:ℝ,‖squareJetPair m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) f h‖) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=square_jet_tail μ hμ f h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  exact (paid_cross_fixed% complex_price) _ (square_jet_continuous advanced μ hμ m ell F f h) ε hε.le (hF advanced)

private theorem covariance_square_jet_price(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>sourcePair g (coreCovariance m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) (pressureFullJet (compressionCore F*compressionCore F) g))) ∧
        (∫w:ℝ,‖sourcePair g (coreCovariance m ell F (causalFrequency advanced μ w)
          (nonreal advanced μ hμ w) (pressureFullJet (compressionCore F*compressionCore F) g))‖) ≤ ε := by
  intro ε hε
  let Q:=balancedPressureJet ActualSecondPressureMagneticPayment.nonmagneticSecondField
  obtain ⟨N,hN⟩:=(paid_cross_fixed% cov_word_tail) [] μ hμ g (Q g) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_pressure_square_fixed_source_return g] with F hF hSq
  intro advanced
  rw [hSq]
  exact (paid_cross_fixed% complex_price) _
    ((paid_cross_fixed% cov_word_continuous) [] advanced μ hμ m ell F g (Q g)) ε hε.le (hF advanced)

private theorem cross_pair_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourcePair g (pressureProductCross (coreCovariance m ell F z hz) (compressionCore F*compressionCore F) g)=
      squareJetPair m ell F z hz g g-
      sourcePair g (pressureFullJet (coreCovariance m ell F z hz) ((compressionCore F*compressionCore F) g))-
      sourcePair g (coreCovariance m ell F z hz (pressureFullJet (compressionCore F*compressionCore F) g)) := by
  unfold pressureProductCross squareJetPair
  simp only [LinearMap.sub_apply,Module.End.mul_apply,(paid_phase_frequency% pair_sub_right)]

/-- Three actual ordered source slots share one N, one source frame and
both causes. The whole product cross receives a complex absolute L1 price. -/
theorem actual_pressure_product_cross_price(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>sourcePair g (pressureProductCross
          (coreCovariance m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w))
          (compressionCore F*compressionCore F) g)) ∧
        (∫w:ℝ,‖sourcePair g (pressureProductCross
          (coreCovariance m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w))
          (compressionCore F*compressionCore F) g)‖) ≤ ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=square_jet_price μ hμ g g (ε/3) (by positivity)
  obtain ⟨N2,h2⟩:=actual_pressure_fixed_return_price μ hμ g (ε/3) (by positivity)
  obtain ⟨N3,h3⟩:=covariance_square_jet_price μ hμ g (ε/3) (by positivity)
  refine ⟨max (max N1 N2) N3,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hF1 hF2 hF3
  intro advanced
  obtain ⟨ha,pa⟩:=hF1 advanced
  obtain ⟨hb,pb⟩:=hF2 advanced
  obtain ⟨hd,pd⟩:=hF3 advanced
  let a(w:ℝ):ℂ:=squareJetPair m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) g g
  let b(w:ℝ):ℂ:=sourcePair g (pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w)
    (nonreal advanced μ hμ w)) ((compressionCore F*compressionCore F) g))
  let d(w:ℝ):ℂ:=sourcePair g (coreCovariance m ell F (causalFrequency advanced μ w)
    (nonreal advanced μ hμ w) (pressureFullJet (compressionCore F*compressionCore F) g))
  let v(w:ℝ):ℂ:=sourcePair g (pressureProductCross (coreCovariance m ell F (causalFrequency advanced μ w)
    (nonreal advanced μ hμ w)) (compressionCore F*compressionCore F) g)
  have he(w:ℝ):v w=a w-b w-d w:=cross_pair_source m ell F _ _ g
  have hi:Integrable v := ((ha.sub hb).sub hd).congr (Eventually.of_forall (fun w=>(he w).symm))
  refine ⟨hi,?_⟩
  have hn(w:ℝ):‖v w‖ ≤ ‖a w‖+‖b w‖+‖d w‖ := by
    rw [he]
    have h1:=norm_sub_le (a w) (b w)
    have h2:=norm_sub_le (a w-b w) (d w)
    linarith only [h1,h2]
  have hm:=integral_mono hi.norm ((ha.norm.add hb.norm).add hd.norm) hn
  have hA:=integral_add ha.norm hb.norm
  have hB:=integral_add (ha.norm.add hb.norm) hd.norm
  simp only [Pi.add_apply] at hA hB
  simp only [Pi.add_apply] at hm
  rw [hB,hA] at hm
  linarith only [hm,pa,pb,pd]

/-- The invoice now contains only the two genuine moving currents;
OwnSquare and all ordered cross words have been paid from fixed source jets. -/
def movingCurrentInvoice(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  retardedPressureSource m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) g+
    (1/12:ℝ)*(sourcePair g ((-pressureRadialCurrent m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w)+
      pressureCFCurrent m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w)) g)).re-
    (phaseCoefficient*sourceTime 0*
      ‖SourceQuantumScalarChart.vacuum‖^2/4)*‖embed (thetaAction m ell (resolventCore F
        (causalFrequency advanced μ w) (nonreal advanced μ hμ w) g))‖^2

private theorem moving_invoice_source(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,∀w:ℝ,
      movingCurrentInvoice advanced μ hμ m ell F g w=contactClearedInvoice advanced μ hμ m ell F g w+
        (1/12:ℝ)*(sourcePair g (pressureProductCross
          (coreCovariance m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w))
          (compressionCore F*compressionCore F) g)).re := by
  filter_upwards [actual_covariance_own_correction_zero g] with F hF advanced μ hμ m ell w
  rw [actual_contact_cleared_invoice_source]
  have hh:=hF m ell (causalFrequency advanced μ w) (nonreal advanced μ hμ w)
  unfold remainingPressureCorrection movingCurrentInvoice
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right),
    Complex.add_re,Complex.sub_re,hh,Complex.zero_re]
  ring

private theorem source_mu_positive:0 < sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large

/-- The original-mu native lower bound clears whole Own and product cross
without a moving Own-zero claim or a caller frequency budget. -/
theorem actual_source_moving_current_native_lower(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (movingCurrentInvoice advanced sourceMu source_mu_positive m ell F g) ∧
        (∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w) g).re) ≥
          (∫w:ℝ,movingCurrentInvoice advanced sourceMu source_mu_positive m ell F g w)-ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=actual_source_contact_cleared_native_lower g (ε/2) (by positivity)
  obtain ⟨N2,h2⟩:=actual_pressure_product_cross_price sourceMu source_mu_positive g (6*ε) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,moving_invoice_source g] with F hF1 hF2 hF3
  intro advanced
  obtain ⟨hc,hLower⟩:=hF1 advanced
  obtain ⟨hi,hPrice⟩:=hF2 advanced
  let v(w:ℝ):ℂ:=sourcePair g (pressureProductCross
    (coreCovariance m ell F (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w))
    (compressionCore F*compressionCore F) g)
  have hr:=hi.re.const_mul (1/12:ℝ)
  have hEq: movingCurrentInvoice advanced sourceMu source_mu_positive m ell F g=
      fun w:ℝ=>contactClearedInvoice advanced sourceMu source_mu_positive m ell F g w+(1/12:ℝ)*(v w).re :=
    funext (hF3 advanced sourceMu source_mu_positive m ell)
  have hm:Integrable (movingCurrentInvoice advanced sourceMu source_mu_positive m ell F g) := by
    rw [hEq]
    exact (hc.add hr).congr (Eventually.of_forall (fun _=>rfl))
  have hInt:(∫w:ℝ,movingCurrentInvoice advanced sourceMu source_mu_positive m ell F g w)=
      (∫w:ℝ,contactClearedInvoice advanced sourceMu source_mu_positive m ell F g w)+
        (1/12:ℝ)*(∫w:ℝ,(v w).re) := by
    rw [hEq]
    have hh:=integral_add hc hr
    simp only [RCLike.re_to_complex] at hh
    rw [hh,integral_const_mul]
  have hRe:(∫w:ℝ,(v w).re)=(∫w:ℝ,v w).re := by
    simpa only [RCLike.re_to_complex] using integral_re hi
  have hBound:=Complex.abs_re_le_norm (∫w:ℝ,v w)
  have hNorm:=norm_integral_le_integral_norm (μ:=volume) v
  rw [hInt,hRe]
  refine ⟨hm,?_⟩
  have hUpper:(∫w:ℝ,v w).re ≤ 6*ε := le_trans (le_abs_self _) (le_trans hBound (le_trans hNorm hPrice))
  linarith only [hLower,hUpper]

end LowEnergy.ActualPressureProductCrossPayment
