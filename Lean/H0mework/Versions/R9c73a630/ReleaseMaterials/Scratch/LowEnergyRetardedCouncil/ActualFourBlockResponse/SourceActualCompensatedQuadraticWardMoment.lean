import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseQuadraticMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseWardIntertwiner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCompensatedQuadraticWardMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceClockYukawaCubicCurrent
open SourceNativeCutoffContact SourcePhysicalKineticSquare SourceResolventBandLimit
open ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment ActualScalarPhaseJet
open ActualPhaseWardIntertwiner SourceRetardedGraph FullYSourceResolventGraphSplice
open SourceJointResidualEnergy SourceScalarVirialBulk ActualVectorJointCost
open ActualMixedCovarianceTail ActualMixedWindowGram MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix
private abbrev End := QuantumTest  →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussDiagonalHistory.diagonalAction resolventCore compressionCore
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K
  phaseGenerator phaseJet phaseSecond sourcePair inverseVolumeAction thetaAction
  coreWindow phasePair phaseCoefficient sourceTime vacuumJetCoefficient compensatedQuadratic sourceCharge escapePole

private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- Complex polarization retains the original star-escape charge on both
fixed source legs. The charge is chosen before F and either causal sign. -/
def pairMoment(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g h:QuantumTest)(w:ℝ):ℂ :=
  let z:=causalFrequency advanced μ w
  z^2*phasePair m ell F z (causal_nonreal advanced μ hμ w) g h+
    (-2*(phaseCoefficient:ℂ))*sourcePair (thetaAction m ell g)
      (inverseVolumeAction (thetaAction m ell h))*star (escapePole advanced μ w)

theorem actual_pair_moment_diagonal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g:QuantumTest)(w:ℝ):
    pairMoment advanced μ hμ m ell F g g w=
      compensatedQuadratic advanced μ hμ m ell F g w := by
  unfold pairMoment compensatedQuadratic sourceCharge
  rfl

private theorem core_pair_polarization(A B:End)(g h:QuantumTest):
    sourcePair (A g) (B h)=
      (sourcePair (A (g+h)) (B (g+h))-sourcePair (A (g-h)) (B (g-h))-
        Complex.I*sourcePair (A (g+Complex.I • h)) (B (g+Complex.I • h))+
        Complex.I*sourcePair (A (g-Complex.I • h)) (B (g-Complex.I • h)))/4 := by
  simp only [sourcePair,map_add,map_sub,map_smul,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private def fourPairForm(X W S T V:End)(a b d:ℂ)(g h:QuantumTest):ℂ:=
  a*((2:ℂ)*sourcePair (X g) (X h)+sourcePair (W g) (S h)+sourcePair (S g) (W h))+
    b*sourcePair (T g) (V h)*d

private theorem four_form_polarization(X W S T V:End)(a b d:ℂ)(g h:QuantumTest):
    fourPairForm X W S T V a b d g h=
      (fourPairForm X W S T V a b d (g+h) (g+h)-fourPairForm X W S T V a b d (g-h) (g-h)-
        Complex.I*fourPairForm X W S T V a b d (g+Complex.I • h) (g+Complex.I • h)+
        Complex.I*fourPairForm X W S T V a b d (g-Complex.I • h) (g-Complex.I • h))/4 := by
  have h1:=core_pair_polarization X X g h
  have h2:=core_pair_polarization W S g h
  have h3:=core_pair_polarization S W g h
  have h4:=core_pair_polarization T V g h
  unfold fourPairForm
  linear_combination (norm:=ring) (2*a)*h1+a*h2+a*h3+b*d*h4

/-- No Hermitian-real assumption is used: z squared and the compensation
stay in the same complex polarized carrier. -/
theorem actual_pair_moment_polarization(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g h:QuantumTest)(w:ℝ):
    pairMoment advanced μ hμ m ell F g h w=
      (compensatedQuadratic advanced μ hμ m ell F (g+h) w-
        compensatedQuadratic advanced μ hμ m ell F (g-h) w-
        Complex.I*compensatedQuadratic advanced μ hμ m ell F (g+Complex.I • h) w+
        Complex.I*compensatedQuadratic advanced μ hμ m ell F (g-Complex.I • h) w)/4 := by
  let z:=causalFrequency advanced μ w
  let hz:=causal_nonreal advanced μ hμ w
  let R:=resolventCore F z hz
  let T:=thetaAction m ell
  have hp:=four_form_polarization (T*phaseJet R) (coreWindow m ell F z hz)
    (T*phaseSecond R) T (inverseVolumeAction*T) (z^2) (-2*(phaseCoefficient:ℂ))
    (star (escapePole advanced μ w)) g h
  simpa only [fourPairForm,Module.End.mul_apply,pairMoment,compensatedQuadratic,sourceCharge,phasePair] using hp

private theorem four_norm(a b c d:ℂ):
    ‖(a-b-Complex.I*c+Complex.I*d)/4‖ ≤ (‖a‖+‖b‖+‖c‖+‖d‖)/4 := by
  have h1:=norm_sub_le a b
  have h2:=norm_sub_le (a-b) (Complex.I*c)
  have h3:=norm_add_le (a-b-Complex.I*c) (Complex.I*d)
  simp only [norm_mul,Complex.norm_I,one_mul] at h2 h3
  simp only [norm_div,Complex.norm_ofNat]
  nlinarith only [h1,h2,h3]

/-- All four original diagonal producers share one event for both causes;
the conclusion bounds the norm of the whole integral, not its absolute L1 tail. -/
theorem actual_pair_moment_tail(μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (pairMoment advanced μ hμ m ell F g h) ∧
        ‖∫w:ℝ,pairMoment advanced μ hμ m ell F g h w‖ ≤ ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=actual_complex_compensated_quadratic_moment_tail μ hμ (g+h) ε hε
  obtain ⟨N2,h2⟩:=actual_complex_compensated_quadratic_moment_tail μ hμ (g-h) ε hε
  obtain ⟨N3,h3⟩:=actual_complex_compensated_quadratic_moment_tail μ hμ (g+Complex.I • h) ε hε
  obtain ⟨N4,h4⟩:=actual_complex_compensated_quadratic_moment_tail μ hμ (g-Complex.I • h) ε hε
  refine ⟨max (max N1 N2) (max N3 N4),fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,
    h3 m (by omega) ell hml,h4 m (by omega) ell hml] with F hF1 hF2 hF3 hF4
  intro advanced
  obtain ⟨hi1,hp1⟩:=hF1 advanced
  obtain ⟨hi2,hp2⟩:=hF2 advanced
  obtain ⟨hi3,hp3⟩:=hF3 advanced
  obtain ⟨hi4,hp4⟩:=hF4 advanced
  have he:pairMoment advanced μ hμ m ell F g h=
      fun w:ℝ=>(compensatedQuadratic advanced μ hμ m ell F (g+h) w-
        compensatedQuadratic advanced μ hμ m ell F (g-h) w-
        Complex.I*compensatedQuadratic advanced μ hμ m ell F (g+Complex.I • h) w+
        Complex.I*compensatedQuadratic advanced μ hμ m ell F (g-Complex.I • h) w)/4 :=
    funext (fun w=>actual_pair_moment_polarization advanced μ hμ m ell F g h w)
  rw [he]
  refine ⟨(((hi1.sub hi2).sub (hi3.const_mul Complex.I)).add
    (hi4.const_mul Complex.I)).div_const 4,?_⟩
  have ha1:=integral_sub hi1 hi2
  have ha2:=integral_sub (hi1.sub hi2) (hi3.const_mul Complex.I)
  have ha3:=integral_add ((hi1.sub hi2).sub (hi3.const_mul Complex.I)) (hi4.const_mul Complex.I)
  simp only [Pi.sub_apply] at ha1 ha2 ha3
  rw [integral_div,ha3,ha2,ha1,integral_const_mul,integral_const_mul]
  exact (four_norm _ _ _ _).trans (by linarith only [hp1,hp2,hp3,hp4])

private def wordMoment:List End → Bool → (μ:ℝ) → 0 < μ → ℕ → ℕ → Index → QuantumTest → QuantumTest → ℝ → ℂ
  | [],advanced,μ,hμ,m,ell,F,g,h,w=>pairMoment advanced μ hμ m ell F g h w
  | G::word,advanced,μ,hμ,m,ell,F,g,h,w=>
      -wordMoment word advanced μ hμ m ell F (G g) h w-
        wordMoment word advanced μ hμ m ell F g (G h) w

private theorem word_moment_tail(word:List End)(μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (wordMoment word advanced μ hμ m ell F g h) ∧
        ‖∫w:ℝ,wordMoment word advanced μ hμ m ell F g h w‖ ≤ ε := by
  induction word generalizing g h with
  | nil=>exact actual_pair_moment_tail μ hμ g h
  | cons G word ih=>
    intro ε hε
    obtain ⟨N1,h1⟩:=ih (G g) h (ε/2) (by positivity)
    obtain ⟨N2,h2⟩:=ih g (G h) (ε/2) (by positivity)
    refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
    filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF1 hF2
    intro advanced
    obtain ⟨hi1,hp1⟩:=hF1 advanced
    obtain ⟨hi2,hp2⟩:=hF2 advanced
    change Integrable (fun w:ℝ=>-wordMoment word advanced μ hμ m ell F (G g) h w-
      wordMoment word advanced μ hμ m ell F g (G h) w) ∧ _
    refine ⟨hi1.neg.sub hi2,?_⟩
    rw [show (fun w:ℝ=>wordMoment (G::word) advanced μ hμ m ell F g h w)=
      (fun w:ℝ=>-wordMoment word advanced μ hμ m ell F (G g) h w-
        wordMoment word advanced μ hμ m ell F g (G h) w) from rfl,
      ]
    have heI:=integral_sub hi1.neg hi2
    simp only [Pi.neg_apply] at heI
    rw [heI,integral_neg]
    have hn:=norm_sub_le (-(∫w:ℝ,wordMoment word advanced μ hμ m ell F (G g) h w))
      (∫w:ℝ,wordMoment word advanced μ hμ m ell F g (G h) w)
    rw [norm_neg] at hn
    linarith only [hn,hp1,hp2]

/-- Original Phi on the phase-squared carrier; its forced shift is available
for a carrier before phase. Both use the same actual generators. -/
def pairWardPhi(shifted:Bool):PairMatrix →ₗ[ℂ]PairMatrix:=
  pairDelta Phi+(if shifted then (2:ℂ) else 0) • LinearMap.id

def momentMatrix(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g h:QuantumTest)(w:ℝ):PairMatrix :=
  fun A B=>pairMoment advanced μ hμ m ell F (A g) (B h) w

def compensatedWardMoment(shifted advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g h:QuantumTest)(w:ℝ):ℂ :=
  InverseVolumeWardAlgebra.inverseWard (pairWardPhi shifted) (pairDelta Gauge) (pairDelta Coframe)
    (vacuumJetCoefficient:ℂ) (momentMatrix advanced μ hμ m ell F g h w) 1 1

private def wordMatrix:List End → PairMatrix → PairMatrix
  | [],P=>P
  | G::word,P=>pairDelta G (wordMatrix word P)

private theorem word_matrix_source(word:List End)(advanced:Bool)(μ:ℝ)(hμ:0 < μ)
    (m ell:ℕ)(F:Index)(g h:QuantumTest)(w:ℝ)(A B:End):
    wordMatrix word (momentMatrix advanced μ hμ m ell F g h w) A B=
      wordMoment word advanced μ hμ m ell F (A g) (B h) w := by
  induction word generalizing A B with
  | nil=>rfl
  | cons G word ih=>
    change -wordMatrix word (momentMatrix advanced μ hμ m ell F g h w) (G*A) B-
      wordMatrix word (momentMatrix advanced μ hμ m ell F g h w) A (G*B)=_
    rw [ih,ih]
    rfl

private def wardCoefficient(shifted:Bool)(γ:ℂ)(i:Fin 19):ℂ:=
  let s:ℂ:=if shifted then 2 else 0
  let b:ℂ:=2*s-3
  let k:ℂ:=s^2-3*s+2
  ![1,-1,-5,5+s,4,-4-5*s,4*s,
    γ,12*γ,44*γ,48*γ,
    b*γ,12*b*γ,44*b*γ,48*b*γ,
    k*γ,12*k*γ,44*k*γ,48*k*γ] i
private def wardWord(i:Fin 19):List End:=
  ![[Gauge,Gauge,Phi],[Gauge,Gauge,Gauge],[Gauge,Phi],[Gauge,Gauge],[Phi],[Gauge],[],
    [Phi,Phi,Coframe,Coframe,Coframe],[Phi,Phi,Coframe,Coframe],[Phi,Phi,Coframe],[Phi,Phi],
    [Phi,Coframe,Coframe,Coframe],[Phi,Coframe,Coframe],[Phi,Coframe],[Phi],
    [Coframe,Coframe,Coframe],[Coframe,Coframe],[Coframe],[]] i

private theorem whole_polynomial_words(shifted:Bool)(γ:ℂ)(P:PairMatrix):
    InverseVolumeWardAlgebra.inverseWard (pairWardPhi shifted) (pairDelta Gauge) (pairDelta Coframe)
      γ P=
      ∑i:Fin 19,wardCoefficient shifted γ i • wordMatrix (wardWord i) P := by
  unfold InverseVolumeWardAlgebra.inverseWard InverseVolumeWardAlgebra.mixedPolynomial
    InverseVolumeWardAlgebra.affinePolynomial InverseVolumeWardAlgebra.inverseLocalPolynomial pairWardPhi
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_add,map_sub,map_smul]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,wardCoefficient,wardWord,
    Matrix.cons_val_zero,Matrix.cons_val_succ,wordMatrix]
  module

/-- The full ordered source words preserve all three coframe derivatives
and the real source vacuum coefficient. Inputs remain fixed before F. -/
theorem actual_compensated_ward_source(shifted advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g h:QuantumTest)(w:ℝ):
    compensatedWardMoment shifted advanced μ hμ m ell F g h w=
      ∑i:Fin 19,wardCoefficient shifted (vacuumJetCoefficient:ℂ) i*wordMoment (wardWord i) advanced μ hμ m ell F g h w := by
  unfold compensatedWardMoment
  rw [whole_polynomial_words]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,word_matrix_source,Module.End.one_apply]

private theorem coefficient_word_tail(coeff:Fin 19→ℂ)(μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>∑i:Fin 19,coeff i*wordMoment (wardWord i) advanced μ hμ m ell F g h w) ∧
        ‖∫w:ℝ,∑i:Fin 19,coeff i*wordMoment (wardWord i) advanced μ hμ m ell F g h w‖ ≤ ε := by
  intro ε hε
  let C:ℝ:=∑i:Fin 19,‖coeff i‖
  have hC:0 ≤ C:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let δ:ℝ:=ε/(C+1)
  have hd:0<δ:=by dsimp only [δ];positivity
  choose N hN using (fun i:Fin 19=>word_moment_tail (wardWord i) μ hμ g h δ hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hevent:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 19,∀advanced:Bool,
      Integrable (wordMoment (wardWord i) advanced μ hμ m ell F g h) ∧
      ‖∫w:ℝ,wordMoment (wardWord i) advanced μ hμ m ell F g h w‖ ≤ δ := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hevent] with F hF
  intro advanced
  have hi(i:Fin 19):Integrable (fun w:ℝ=>coeff i*
      wordMoment (wardWord i) advanced μ hμ m ell F g h w):=
    (hF i advanced).1.const_mul (coeff i)
  refine ⟨integrable_finsetSum Finset.univ (fun i _=>hi i),?_⟩
  rw [integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [integral_const_mul]
  apply (norm_sum_le Finset.univ _).trans
  simp only [norm_mul]
  apply (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hF i advanced).2 (norm_nonneg _))).trans
  rw [←Finset.sum_mul]
  change C*δ ≤ ε
  dsimp only [δ]
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0<C+1)).mpr
  nlinarith only [hε,hC]

/-- The physical consumer uses original Phi on the phase-squared carrier;
+2 is a separate polynomial evaluation, never another physical phase shift. -/
theorem actual_compensated_ward_moment_tail(shifted:Bool)(μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (compensatedWardMoment shifted advanced μ hμ m ell F g h) ∧
        ‖∫w:ℝ,compensatedWardMoment shifted advanced μ hμ m ell F g h w‖ ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=coefficient_word_tail (wardCoefficient shifted (vacuumJetCoefficient:ℂ)) μ hμ g h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have he:compensatedWardMoment shifted advanced μ hμ m ell F g h=
      fun w:ℝ=>∑i:Fin 19,wardCoefficient shifted (vacuumJetCoefficient:ℂ) i*
        wordMoment (wardWord i) advanced μ hμ m ell F g h w :=
    funext (fun w=>actual_compensated_ward_source shifted advanced μ hμ m ell F g h w)
  rw [he]
  exact hF advanced

/-- The actual mixed source component, with the entire complex compensation
retained; the central coframe department is handled by its own source identity. -/
def mixedMoment(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g h:QuantumTest)(w:ℝ):ℂ :=
  InverseVolumeWardAlgebra.mixedPolynomial (pairDelta Phi) (pairDelta Gauge)
    (momentMatrix advanced μ hμ m ell F g h w) 1 1

private theorem mixed_polynomial_words(P:PairMatrix):
    InverseVolumeWardAlgebra.mixedPolynomial (pairDelta Phi) (pairDelta Gauge) P=
      ∑i:Fin 19,wardCoefficient false 0 i • wordMatrix (wardWord i) P := by
  have h:=whole_polynomial_words false 0 P
  simpa only [InverseVolumeWardAlgebra.inverseWard,pairWardPhi,Bool.false_eq_true,
    ite_false,zero_smul,add_zero] using h

/-- The pure mixed polynomial is generated by the same original fixed words,
without deleting an unpriced coframe summand from a whole bound. -/
theorem actual_physical_mixed_moment_source(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g h:QuantumTest)(w:ℝ):
    mixedMoment advanced μ hμ m ell F g h w=
      ∑i:Fin 19,wardCoefficient false 0 i*wordMoment (wardWord i) advanced μ hμ m ell F g h w := by
  unfold mixedMoment
  rw [mixed_polynomial_words]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,word_matrix_source,Module.End.one_apply]

theorem actual_physical_mixed_moment_tail(μ:ℝ)(hμ:0 < μ)(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (mixedMoment advanced μ hμ m ell F g h) ∧
        ‖∫w:ℝ,mixedMoment advanced μ hμ m ell F g h w‖ ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=coefficient_word_tail (wardCoefficient false 0) μ hμ g h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have he:mixedMoment advanced μ hμ m ell F g h=
      fun w:ℝ=>∑i:Fin 19,wardCoefficient false 0 i*
        wordMoment (wardWord i) advanced μ hμ m ell F g h w :=
    funext (fun w=>actual_physical_mixed_moment_source advanced μ hμ m ell F g h w)
  rw [he]
  exact hF advanced

private theorem source_mu_positive:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large

theorem actual_source_physical_compensated_ward_moment_tail(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (compensatedWardMoment false advanced sourceMu source_mu_positive m ell F g h) ∧
        ‖∫w:ℝ,compensatedWardMoment false advanced sourceMu source_mu_positive m ell F g h w‖ ≤ ε :=
  actual_compensated_ward_moment_tail false sourceMu source_mu_positive g h

theorem actual_source_physical_mixed_moment_tail(g h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (mixedMoment advanced sourceMu source_mu_positive m ell F g h) ∧
        ‖∫w:ℝ,mixedMoment advanced sourceMu source_mu_positive m ell F g h w‖ ≤ ε :=
  actual_physical_mixed_moment_tail sourceMu source_mu_positive g h

end LowEnergy.ActualCompensatedQuadraticWardMoment
