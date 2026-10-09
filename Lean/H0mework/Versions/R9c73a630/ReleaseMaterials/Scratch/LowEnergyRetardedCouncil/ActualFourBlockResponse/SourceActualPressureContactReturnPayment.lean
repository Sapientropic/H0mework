import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPressureFixedReturnPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualPressureContactReturnPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceNativeCutoffContact SourceResolventBandLimit
open ActualMixedCovarianceTail ActualMixedWindowGram ActualVectorJointCost ActualScalarPhaseJet
open ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment ActualCompensatedQuadraticWardMoment
open ActualBalancedPressureMomentPayment ActualBalancedLocalizationContactReturn ActualBalancedPressureWardPayment
open ActualPressureFixedReturnPayment ActualShiftedQuadraticWardPayment SourceInverseFullResponse SourceScalarPositiveBulkWard
open SourcePhysicalKineticSquare
open SourceJointResidualEnergy SourceRetardedGraph SourceInverseNoetherChannelGap
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair resolventCore compressionCore diagonalAction phaseJet phaseSecond
  pressureFullJet pressureOperator phaseGenerator inverseVolumeAction phaseCoefficient coreWindow
elab "paid_contact%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseQuadraticMoment 0) "LowEnergy") "ActualScalarPhaseQuadraticMoment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
private theorem nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):(causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'
private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private theorem phase_pair_left(f h:QuantumTest):sourcePair (phaseGenerator f) h= -sourcePair f (phaseGenerator h) := by
  linear_combination (norm:=ring) (paid_quadratic_phase% phase_skew) f h
private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_left(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_left(c:ℂ)(f h:QuantumTest):sourcePair (c • f) h=star c*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem theta_pair(m ell:ℕ)(f h:QuantumTest):sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h :=
  GaussNativeForm.multiply_pair _ _ _ _
private theorem inverse_theta(m ell:ℕ):inverseVolumeAction*thetaAction m ell=thetaAction m ell*inverseVolumeAction :=
by
  apply LinearMap.ext
  exact (paid_contact% inverse_theta) m ell

private theorem jet_adjoint(A B:End)(hAB:∀f h:QuantumTest,sourcePair f (B h)=sourcePair (A f) h)
    (f h:QuantumTest):sourcePair f (phaseJet B h)=sourcePair (phaseJet A f) h := by
  simp only [(paid_quadratic_phase% phase_apply),pair_sub_left,(paid_phase_frequency% pair_sub_right)]
  rw [(paid_quadratic_phase% phase_skew),hAB,hAB,phase_pair_left]
  ring
private theorem second_adjoint(A B:End)(hAB:∀f h:QuantumTest,sourcePair f (B h)=sourcePair (A f) h)
    (f h:QuantumTest):sourcePair f (phaseSecond B h)=sourcePair (phaseSecond A f) h := by
  unfold phaseSecond
  exact jet_adjoint (phaseJet A) (phaseJet B) (jet_adjoint A B hAB) f h
private theorem resolvent_adjoint(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair f (resolventCore F (star z) (star_nonreal z hz) h)=sourcePair (resolventCore F z hz f) h :=
  (paid_balanced_covariance% resolvent_pair) F z hz f h

private def contactPair(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f h:QuantumTest)(w:ℝ):ℂ :=
  let z:=causalFrequency advanced μ w
  let R:=resolventCore F z (nonreal advanced μ hμ w)
  (2:ℂ)*sourcePair (thetaAction m ell (phaseJet R f)) (thetaAction m ell (phaseJet diagonalAction h))+
    sourcePair (thetaAction m ell (phaseSecond R f)) (thetaAction m ell (diagonalAction h))+
    (sourcePair (coreWindow m ell F z (nonreal advanced μ hμ w) f)
      (thetaAction m ell (phaseSecond diagonalAction h))-
      sourcePair (thetaAction m ell f) (thetaAction m ell (phaseSecond diagonalAction h))*star (escapePole advanced μ w))+
    (z*sourcePair (thetaAction m ell (phaseSecond R f)) (thetaAction m ell h)-
      sourcePair (thetaAction m ell (phaseSecond diagonalAction f)) (thetaAction m ell h)*star (escapePole advanced μ w))

private theorem contact_pair_zero(f h:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,
      Integrable (contactPair advanced μ hμ m ell F f h) ∧
      (∫w:ℝ,contactPair advanced μ hμ m ell F f h w)=0 := by
  filter_upwards [(paid_quadratic_phase% fixed_source_jets) f] with F hF advanced μ hμ m ell
  obtain ⟨_,_,h2⟩:=hF
  have h1:=(paid_contact% jet_endpoint_integral) phaseJet (paid_quadratic_phase% phase_one)
    advanced μ hμ m ell F f (phaseJet diagonalAction h)
  have hs:=actual_phase_whole_endpoint_pair_integral advanced μ hμ m ell F f (diagonalAction h)
  have hb:=(paid_contact% bare_endpoint_integral) advanced μ hμ m ell F f (phaseSecond diagonalAction h)
  have hz:=(paid_contact% weighted_jet_endpoint_integral) phaseSecond (paid_quadratic_phase% phase_second_one)
    advanced μ hμ m ell F f h
  dsimp only at h1 hs hb hz
  rw [h2] at hz
  change Integrable (fun w:ℝ=>(2:ℂ)*_+_+_+_) ∧ _
  constructor
  · exact (((h1.1.const_mul (2:ℂ)).add hs.1).add hb.1).add hz.1
  · simp only [contactPair]
    have ha1:=integral_add (h1.1.const_mul (2:ℂ)) hs.1
    have ha2:=integral_add ((h1.1.const_mul (2:ℂ)).add hs.1) hb.1
    have ha3:=integral_add (((h1.1.const_mul (2:ℂ)).add hs.1).add hb.1) hz.1
    simp only [Pi.add_apply] at ha1 ha2 ha3
    rw [ha3,ha2,ha1,integral_const_mul,h1.2,hs.2,hb.2,hz.2]
    ring

private def contactCarrier(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ):End :=
  let z:=causalFrequency advanced μ w
  let E:=resolventCore F (star z) (star_nonreal z (nonreal advanced μ hμ w))*thetaAction m ell*thetaAction m ell
  phaseSecond (E*compressionCore F)+z • phaseSecond E+
    ((2*(phaseCoefficient:ℂ))*star (escapePole advanced μ w)) •
      (thetaAction m ell*inverseVolumeAction*thetaAction m ell)

private theorem phase_theta_product(A:End)(m ell:ℕ):
    phaseSecond (A*thetaAction m ell*thetaAction m ell)=phaseSecond A*thetaAction m ell*thetaAction m ell := by
  have ht:phaseJet (thetaAction m ell)=0:=(paid_quadratic_phase% theta_phase_zero) m ell
  have h2:phaseSecond (thetaAction m ell)=0 := by
    unfold phaseSecond
    change phaseJet (phaseJet (thetaAction m ell))=0
    rw [ht,(paid_quadratic_phase% phase_zero)]
  simp only [actual_phase_second_product,(paid_quadratic_phase% phase_mul),ht,h2,mul_zero,
    add_zero,smul_zero]

private theorem contact_source_return(f h:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,∀w:ℝ,
      sourcePair f (contactCarrier advanced μ hμ m ell F w h)=contactPair advanced μ hμ m ell F f h w := by
  filter_upwards [(paid_quadratic_phase% fixed_source_jets) h] with F hF advanced μ hμ m ell w
  obtain ⟨h0,h1,h2⟩:=hF
  let z:=causalFrequency advanced μ w
  let hz:=nonreal advanced μ hμ w
  let R:=resolventCore F z hz
  let Rb:=resolventCore F (star z) (star_nonreal z hz)
  let T:=thetaAction m ell
  have had:∀a b:QuantumTest,sourcePair a (Rb b)=sourcePair (R a) b:=resolvent_adjoint F z hz
  have hp:∀a b:QuantumTest,sourcePair a (phaseJet Rb b)=sourcePair (phaseJet R a) b:=jet_adjoint R Rb had
  have hs:∀a b:QuantumTest,sourcePair a (phaseSecond Rb b)=sourcePair (phaseSecond R a) b:=second_adjoint R Rb had
  have ht:phaseJet T=0:=(paid_quadratic_phase% theta_phase_zero) m ell
  have htt:phaseJet (Rb*T*T)=phaseJet Rb*T*T := by
    simp only [(paid_quadratic_phase% phase_mul),ht,mul_zero,add_zero]
  have hu:phaseSecond diagonalAction=-(phaseCoefficient:ℂ) • inverseVolumeAction := by
    simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using actual_source_inverse_volume_phase_jet
  have hr:star (phaseCoefficient:ℂ)=(phaseCoefficient:ℂ):=Complex.conj_ofReal _
  unfold contactCarrier contactPair
  change sourcePair f ((phaseSecond (Rb*T*T*compressionCore F)+z • phaseSecond (Rb*T*T)+
    ((2*(phaseCoefficient:ℂ))*star (escapePole advanced μ w)) • (T*inverseVolumeAction*T)) h)=_
  rw [actual_phase_second_product,phase_theta_product,htt]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_smul_right),h0,h1,h2,
    hs,hp,had,theta_pair]
  have hi(a b:QuantumTest):sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b :=
    by unfold inverseVolumeAction;exact GaussNativeForm.multiply_pair _ _ _ _
  have hit(a:QuantumTest):inverseVolumeAction (thetaAction m ell a)=thetaAction m ell (inverseVolumeAction a) :=
    congrArg (fun X:End=>X a) (inverse_theta m ell)
  simp only [hu,LinearMap.smul_apply,map_smul,pair_smul_left,(paid_phase_frequency% pair_smul_right),star_neg,hr]
  unfold coreWindow
  dsimp only [T,R,Rb,z,hz,Module.End.mul_apply]
  simp only [theta_pair,hi,hit]
  ring

private theorem carrier_pair_zero(f h:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,
      Integrable (fun w:ℝ=>sourcePair f (contactCarrier advanced μ hμ m ell F w h)) ∧
      (∫w:ℝ,sourcePair f (contactCarrier advanced μ hμ m ell F w h))=0 := by
  filter_upwards [contact_source_return f h,contact_pair_zero f h] with F h1 h2 advanced μ hμ m ell
  simp_rw [h1 advanced μ hμ m ell]
  exact h2 advanced μ hμ m ell

private def contactWord:List End → Bool → (μ:ℝ) → 0 < μ → ℕ → ℕ → Index → QuantumTest → QuantumTest → ℝ → ℂ
  | [],advanced,μ,hμ,m,ell,F,f,h,w=>sourcePair f (contactCarrier advanced μ hμ m ell F w h)
  | G::word,advanced,μ,hμ,m,ell,F,f,h,w=>
    -contactWord word advanced μ hμ m ell F (G f) h w-contactWord word advanced μ hμ m ell F f (G h) w

private theorem contact_word_zero(word:List End)(f h:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,
      Integrable (contactWord word advanced μ hμ m ell F f h) ∧
      (∫w:ℝ,contactWord word advanced μ hμ m ell F f h w)=0 := by
  induction word generalizing f h with
  | nil=>exact carrier_pair_zero f h
  | cons G word ih=>
    filter_upwards [ih (G f) h,ih f (G h)] with F h1 h2 advanced μ hμ m ell
    obtain ⟨hi1,hz1⟩:=h1 advanced μ hμ m ell
    obtain ⟨hi2,hz2⟩:=h2 advanced μ hμ m ell
    refine ⟨hi1.neg.sub hi2,?_⟩
    change (∫w:ℝ,-contactWord word advanced μ hμ m ell F (G f) h w-
      contactWord word advanced μ hμ m ell F f (G h) w)=0
    have hh:=integral_sub hi1.neg hi2
    simp only [Pi.neg_apply] at hh
    rw [hh,integral_neg,hz1,hz2]
    ring

private theorem matrix_nil(P:PairMatrix):(paid_pressure_moment% wordMatrix) [] P=P := rfl
private theorem matrix_cons(G:End)(word:List End)(P:PairMatrix):
    (paid_pressure_moment% wordMatrix) (G::word) P=pairDelta G ((paid_pressure_moment% wordMatrix) word P) := rfl
private theorem matrix_contact_source(word:List End)(advanced:Bool)(μ:ℝ)(hμ:0 < μ)
    (m ell:ℕ)(F:Index)(w:ℝ)(f h:QuantumTest)(A B:End):
    (paid_pressure_moment% wordMatrix) word (responseRead f h (contactCarrier advanced μ hμ m ell F w)) A B=
      contactWord word advanced μ hμ m ell F (A f) (B h) w := by
  induction word generalizing A B with
  | nil=>rfl
  | cons G word ih=>
    rw [matrix_cons]
    change -(paid_pressure_moment% wordMatrix) word (responseRead f h (contactCarrier advanced μ hμ m ell F w)) (G*A) B-
      (paid_pressure_moment% wordMatrix) word (responseRead f h (contactCarrier advanced μ hμ m ell F w)) A (G*B)=_
    rw [ih,ih]
    rfl

/-- Both left-window orders and the natural star escape are one source contact. -/
def pressureContactGroup(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ):End :=
  pressureOperator (contactCarrier advanced μ hμ m ell F w)

theorem actual_pressure_contact_same_carrier(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ):
    pressureContactGroup advanced μ hμ m ell F w=
      ((2*(phaseCoefficient:ℂ))*star (escapePole advanced μ w)) •
        pressureOperator (thetaAction m ell*inverseVolumeAction*thetaAction m ell)+
      pressureFullJet ((paid_fixed_pressure% leftWindow) m ell F (causalFrequency advanced μ w)
        (nonreal advanced μ hμ w)*compressionCore F)+
      (causalFrequency advanced μ w) • pressureFullJet ((paid_fixed_pressure% leftWindow) m ell F
        (causalFrequency advanced μ w) (nonreal advanced μ hμ w)) := by
  unfold pressureContactGroup contactCarrier pressureFullJet
  simp only [map_add,map_smul,LinearMap.comp_apply]
  have he:(paid_fixed_pressure% leftWindow) m ell F (causalFrequency advanced μ w)
      (nonreal advanced μ hμ w)=resolventCore F (star (causalFrequency advanced μ w))
        (star_nonreal _ (nonreal advanced μ hμ w))*thetaAction m ell*thetaAction m ell := rfl
  rw [he]
  module

theorem actual_pressure_contact_words(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ)(f h:QuantumTest):
    sourcePair f (pressureContactGroup advanced μ hμ m ell F w h)=
      ∑i:Fin 8,(paid_fixed_pressure% pressureCoefficient) i*
        contactWord ((paid_fixed_pressure% pressureWord) i) advanced μ hμ m ell F f h w := by
  have hp:=(paid_fixed_pressure% response_pressure) f h (contactCarrier advanced μ hμ m ell F w)
  have he:=congrArg (fun P:PairMatrix=>P 1 1) hp
  rw [(paid_fixed_pressure% response_one)] at he
  unfold pressureContactGroup
  rw [he,(paid_fixed_pressure% pressure_matrix_words)]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,matrix_contact_source,Module.End.one_apply]

/-- The actual compensated contact has complex L1 and exact zero integral
on one source event, for every cutoff and both original causes. -/
theorem actual_pressure_contact_integral_zero(f h:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,
      Integrable (fun w:ℝ=>sourcePair f (pressureContactGroup advanced μ hμ m ell F w h)) ∧
      (∫w:ℝ,sourcePair f (pressureContactGroup advanced μ hμ m ell F w h))=0 := by
  have hF:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 8,∀advanced:Bool,∀μ:ℝ,∀hμ:0 < μ,∀m ell:ℕ,
      Integrable (contactWord ((paid_fixed_pressure% pressureWord) i) advanced μ hμ m ell F f h) ∧
      (∫w:ℝ,contactWord ((paid_fixed_pressure% pressureWord) i) advanced μ hμ m ell F f h w)=0 := by
    apply Filter.eventually_all.mpr
    intro i
    exact contact_word_zero _ f h
  filter_upwards [hF] with F hF advanced μ hμ m ell
  have hi(i:Fin 8):Integrable (fun w:ℝ=>(paid_fixed_pressure% pressureCoefficient) i*
      contactWord ((paid_fixed_pressure% pressureWord) i) advanced μ hμ m ell F f h w):=
    (hF i advanced μ hμ m ell).1.const_mul _
  simp_rw [actual_pressure_contact_words]
  refine ⟨integrable_finsetSum Finset.univ (fun i _=>hi i),?_⟩
  rw [integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [integral_const_mul]
  simp only [(hF _ advanced μ hμ m ell).2,mul_zero,Finset.sum_const_zero]

/-- The complete contact group is removed only after its complex zero
integral has been generated from the actual source. -/
def contactClearedInvoice(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  fixedReturnClearedInvoice advanced μ hμ m ell F g w-
    (1/12:ℝ)*(sourcePair g (pressureContactGroup advanced μ hμ m ell F w g)).re

def remainingPressureCorrection(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ):End :=
  let z:=causalFrequency advanced μ w
  let hz:=nonreal advanced μ hμ w
  (-pressureRadialCurrent m ell F z hz+pressureCFCurrent m ell F z hz+
    coreCovariance m ell F z hz*pressureFullJet (phaseSquareOwn F)-
    pressureProductCross (coreCovariance m ell F z hz) (compressionCore F*compressionCore F))

/-- The actual Own, ordered product and both moving source currents remain. -/
theorem actual_contact_cleared_invoice_source(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g:QuantumTest)(w:ℝ):
    contactClearedInvoice advanced μ hμ m ell F g w=
      retardedPressureSource m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w) g+
        (1/12:ℝ)*(sourcePair g (remainingPressureCorrection advanced μ hμ m ell F w g)).re-
        (phaseCoefficient*sourceTime 0*‖SourceQuantumScalarChart.vacuum‖^2/4)*
          ‖embed (thetaAction m ell (resolventCore F (causalFrequency advanced μ w)
            (nonreal advanced μ hμ w) g))‖^2 := by
  have hop:pressureCorrection advanced μ hμ m ell F w+
      pressureFullJet (coreCovariance m ell F (causalFrequency advanced μ w) (nonreal advanced μ hμ w))*
        (compressionCore F*compressionCore F)-pressureContactGroup advanced μ hμ m ell F w=
      remainingPressureCorrection advanced μ hμ m ell F w := by
    rw [actual_pressure_contact_same_carrier]
    unfold pressureCorrection remainingPressureCorrection
    dsimp only
    module
  have hh:=congrArg (fun X:End=>(sourcePair g (X g)).re) hop
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
    (paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right),Complex.add_re,Complex.sub_re] at hh
  unfold contactClearedInvoice fixedReturnClearedInvoice correctedSourceNativeInvoice
  dsimp only
  simp only [Module.End.mul_apply]
  linear_combination (norm:=ring) (1/12:ℝ)*hh

private theorem source_mu_positive:0 < sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large

/-- Direct original-mu consumer: the source contact is cleared exactly,
while the fixed-square debit uses its common-N absolute L1 payment. -/
theorem actual_source_contact_cleared_native_lower(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (contactClearedInvoice advanced sourceMu source_mu_positive m ell F g) ∧
        (∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (nonreal advanced sourceMu source_mu_positive w) g).re) ≥
          (∫w:ℝ,contactClearedInvoice advanced sourceMu source_mu_positive m ell F g w)-ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=actual_source_fixed_return_native_lower g ε hε
  obtain ⟨N2,h2⟩:=actual_source_native_pressure_integral_payment g ε hε
  obtain ⟨N3,h3⟩:=actual_pressure_fixed_return_price sourceMu source_mu_positive g ε hε
  refine ⟨max (max N1 N2) N3,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,
    h3 m (by omega) ell hml,actual_pressure_contact_integral_zero g g] with F hF1 hF2 hF3 hF4
  intro advanced
  have hc:Integrable (fixedReturnClearedInvoice advanced sourceMu source_mu_positive m ell F g) := by
    have hi:=(hF2 advanced).1.add ((hF3 advanced).1.re.const_mul (1/12:ℝ))
    apply hi.congr
    exact Eventually.of_forall (fun w=>by
      unfold fixedReturnClearedInvoice
      rfl)
  obtain ⟨ht,hz⟩:=hF4 advanced sourceMu source_mu_positive m ell
  have hr:(∫w:ℝ,(sourcePair g (pressureContactGroup advanced sourceMu source_mu_positive m ell F w g)).re)=0 := by
    simpa only [RCLike.re_to_complex,hz,Complex.zero_re] using integral_re ht
  have htc:=ht.re.const_mul (1/12:ℝ)
  have he:(∫w:ℝ,contactClearedInvoice advanced sourceMu source_mu_positive m ell F g w)=
      (∫w:ℝ,fixedReturnClearedInvoice advanced sourceMu source_mu_positive m ell F g w) := by
    have hh:=integral_sub hc htc
    simp only [RCLike.re_to_complex] at hh
    unfold contactClearedInvoice
    rw [hh,integral_const_mul,hr]
    ring
  refine ⟨?_,?_⟩
  · apply (hc.sub htc).congr
    exact Eventually.of_forall (fun w=>by unfold contactClearedInvoice;rfl)
  · rw [he]
    exact hF1 advanced

end LowEnergy.ActualPressureContactReturnPayment
