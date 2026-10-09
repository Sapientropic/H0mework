import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureWardPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCompensatedWardOperatorReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureFrequencyPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedPressureMomentPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy GaussNativeForm GaussNativePotential
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet SourceScalarPositiveBulkWard
open SourceScalarInverseBulk SourceClockPhiSecondBulk SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy
open SourceNativeCutoffContact SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceResolventBandLimit
open ActualBalancedPressureWardPayment ActualBalancedLocalizationContactReturn ActualSecondPressureMagneticPayment
open ActualPhaseBulkSquare ActualScalarPhaseJet ActualScalarPhaseFrequencyReturn ActualPhaseWardIntertwiner
open ActualCompensatedQuadraticWardMoment ActualCompensatedWardOperatorReturn ActualMixedCovarianceTail ActualMixedWindowGram
open ActualVectorJointCost SourceInverseFullResponse ActualShiftedQuadraticWardPayment SourceQuantumScalarChart
open ActualScalarPhaseQuadraticMoment SourceJointResidualEnergy SourceRetardedGraph SourceInverseNoetherChannelGap
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators Matrix
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair nonmagneticSecondField magneticSecondField phaseForce inverseVolumeAction
  phaseCoefficient sourceTime momentMatrix compensatedMomentOperator phaseSecond coreCovariance compressionCore resolventCore
  diagonalAction phaseHamiltonianSquare phaseSquareOwn defectAction responseRead
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K

elab "paid_pressure_moment%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCompensatedQuadraticWardMoment 0) "LowEnergy") "ActualCompensatedQuadraticWardMoment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_pressure_ward%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureWardPayment 0) "LowEnergy") "ActualBalancedPressureWardPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

/-- The original source weights 0, -2 and 4 determine this projector. -/
def nonmagneticProjection : (End→ₗ[ℂ]End) :=
  LinearMap.id-(1/24:ℂ) • deltaGauge.comp (deltaGauge+(2:ℂ) • LinearMap.id)
def pressureDerivation : (End→ₗ[ℂ]End) :=
  (3:ℂ) • deltaPhi-(12:ℂ) • deltaGauge-(6:ℂ) • scaleDerivative
/-- Original Phi acts after phase throughout this operator. -/
def pressureOperator : (End→ₗ[ℂ]End) :=
  pressureDerivation.comp (nonmagneticProjection.comp secondJet)
def pressureFullJet : (End→ₗ[ℂ]End) := pressureOperator.comp phaseSecond

private theorem gauge_product(X Y:End):deltaGauge (X*Y)=deltaGauge X*Y+X*deltaGauge Y := by
  rw [←SourceGaugeScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator,
    ←SourceGaugeScaleTransport.generator_commutator]
  noncomm_ring
private theorem force_gauge:deltaGauge (phaseForce*phaseForce)=0 := by
  obtain ⟨_,hg,_⟩:=actual_source_phase_force_weights
  rw [gauge_product,hg,zero_mul,mul_zero,add_zero]
private theorem shifted_gauge:deltaGauge shiftedAction=0 := by
  rw [(paid_pressure_ward% shifted_source)]
  simp only [map_add,map_sub,map_smul,(paid_pressure_virial% centered_gauge),
    (paid_pressure_virial% vacuum_linear_gauge),(paid_pressure_virial% vacuum_constant_gauge),
    sub_zero,zero_add,smul_zero]

/-- This source minimal polynomial includes the true gauge kinetic and
actual phase-force sectors; it is not imposed on raw CF. -/
theorem actual_nonmagnetic_gauge_polynomial:
    deltaGauge (deltaGauge nonmagneticSecondField)+(2:ℂ) • deltaGauge nonmagneticSecondField=0 := by
  have hf:deltaGauge phaseForce=0 := (actual_source_phase_force_weights).2.1
  have hG:deltaGauge nonmagneticSecondField=
      (12*(phaseCoefficient:ℂ)) • (gaugeKinetic*inverseVolumeAction+inverseVolumeAction*gaugeKinetic) := by
    unfold nonmagneticSecondField nonmagneticBulk
    simp only [map_sub,map_add,map_smul,gauge_product,original_scalar_kinetic_gauge,
      original_gauge_kinetic_gauge,shifted_gauge,(paid_pressure_virial% vacuum_constant_gauge),
      inverse_gauge,hf,zero_mul,mul_zero,smul_zero,sub_zero,zero_add,add_zero,
      sub_mul,mul_sub,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_sub,smul_add,smul_smul]
    module
  rw [hG,map_smul,map_add,gauge_product,gauge_product,original_gauge_kinetic_gauge,inverse_gauge]
  simp only [zero_mul,mul_zero,add_zero,zero_add,smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
  module

/-- The actual magnetic department is removed at its generated source weight. -/
theorem actual_nonmagnetic_projection_source:
    nonmagneticProjection (secondJet phaseHamiltonianSquare)=nonmagneticSecondField := by
  rw [actual_native_phase_second_pressure_split,map_add]
  have hm:nonmagneticProjection magneticSecondField=0 := by
    unfold nonmagneticProjection
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,LinearMap.comp_apply,
      LinearMap.add_apply,map_add,map_smul,actual_magnetic_gauge_weight]
    module
  have hn:nonmagneticProjection nonmagneticSecondField=nonmagneticSecondField := by
    unfold nonmagneticProjection
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,LinearMap.comp_apply,
      LinearMap.add_apply,map_add,map_smul]
    rw [actual_nonmagnetic_gauge_polynomial,smul_zero,sub_zero]
  rw [hm,hn,zero_add]

theorem actual_pressure_source_field:
    pressureFullJet (diagonalAction*diagonalAction)=balancedPressureJet nonmagneticSecondField := by
  simp only [pressureFullJet,pressureOperator,LinearMap.comp_apply]
  rw [show phaseSecond (diagonalAction*diagonalAction)=phaseHamiltonianSquare by
    unfold phaseHamiltonianSquare
    rfl]
  rw [actual_nonmagnetic_projection_source]
  unfold pressureDerivation
  simpa only [LinearMap.sub_apply,LinearMap.smul_apply] using
    ((paid_pressure_ward% jet_source) nonmagneticSecondField).symm

/-- Every one of the six original Own-square orders survives in the same
actual pressure jet; no source phase, projection cross or grade is pinched away. -/
theorem actual_pressure_own_square_shape(F:Index):
    pressureFullJet (phaseSquareOwn F)=pressureOperator
      (phaseSecond (defectAction F)*diagonalAction+defectAction F*phaseSecond diagonalAction+
        (2:ℂ) • (phaseJet (defectAction F)*phaseJet diagonalAction)+
        phaseSecond (compressionCore F)*defectAction F+compressionCore F*phaseSecond (defectAction F)+
        (2:ℂ) • (phaseJet (compressionCore F)*phaseJet (defectAction F))) := by
  simp only [pressureFullJet,LinearMap.comp_apply]
  rw [actual_phase_square_own_shape]

private def pairSecond(P:PairMatrix):PairMatrix :=
  (pairDelta Phi P-pairDelta Gauge P)-pairDelta Gauge (pairDelta Phi P-pairDelta Gauge P)
private def pairProjection(P:PairMatrix):PairMatrix :=
  P-(1/24:ℂ) • pairDelta Gauge (pairDelta Gauge P+(2:ℂ) • P)
def pressureMomentMatrix(P:PairMatrix):PairMatrix :=
  pairDelta balancedGenerator (pairProjection (pairSecond P))
private def pressureWord(i:Fin 8):List End :=
  ![[balancedGenerator,Phi],[balancedGenerator,Gauge],
    [balancedGenerator,Gauge,Phi],[balancedGenerator,Gauge,Gauge],
    [balancedGenerator,Gauge,Gauge,Phi],[balancedGenerator,Gauge,Gauge,Gauge],
    [balancedGenerator,Gauge,Gauge,Gauge,Phi],[balancedGenerator,Gauge,Gauge,Gauge,Gauge]] i
private def pressureCoefficient(i:Fin 8):ℂ := ![1,-1,-13/12,13/12,1/24,-1/24,1/24,-1/24] i

private theorem word_nil(P:PairMatrix):(paid_pressure_moment% wordMatrix) [] P=P := rfl
private theorem word_cons(G:End)(word:List End)(P:PairMatrix):
    (paid_pressure_moment% wordMatrix) (G::word) P=
      pairDelta G ((paid_pressure_moment% wordMatrix) word P) := rfl

private theorem pressure_matrix_words(P:PairMatrix):
    pressureMomentMatrix P=∑i:Fin 8,pressureCoefficient i •
      (paid_pressure_moment% wordMatrix) (pressureWord i) P := by
  unfold pressureMomentMatrix pairProjection pairSecond
  simp only [map_add,map_sub,map_smul,Fin.sum_univ_succ,Fin.sum_univ_zero,pressureCoefficient,
    pressureWord,Matrix.cons_val_zero,Matrix.cons_val_succ,word_nil,word_cons]
  module

def pressureMoment(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (f h:QuantumTest)(w:ℝ):ℂ :=
  pressureMomentMatrix (momentMatrix advanced μ hμ m ell F f h w) 1 1

theorem actual_pressure_moment_words(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (f h:QuantumTest)(w:ℝ):
    pressureMoment advanced μ hμ m ell F f h w=∑i:Fin 8,pressureCoefficient i*
      (paid_pressure_moment% wordMoment) (pressureWord i) advanced μ hμ m ell F f h w := by
  unfold pressureMoment
  rw [pressure_matrix_words]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,(paid_pressure_moment% word_matrix_source),
    Module.End.one_apply]

/-- Eight ordered source words choose their complete source jets before F,
frequency and cause. The natural compensation is never separated for integration. -/
theorem actual_pressure_moment_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (pressureMoment advanced μ hμ m ell F f h) ∧
        ‖∫w:ℝ,pressureMoment advanced μ hμ m ell F f h w‖ ≤ ε := by
  intro ε hε
  let C:ℝ:=∑i:Fin 8,‖pressureCoefficient i‖
  have hC:0 ≤ C:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  let d:ℝ:=ε/(C+1)
  have hd:0 < d := by dsimp only [d];positivity
  choose N hN using (fun i:Fin 8=>(paid_pressure_moment% word_moment_tail) (pressureWord i) μ hμ f h d hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hF:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 8,∀advanced:Bool,
      Integrable ((paid_pressure_moment% wordMoment) (pressureWord i) advanced μ hμ m ell F f h) ∧
      ‖∫w:ℝ,(paid_pressure_moment% wordMoment) (pressureWord i) advanced μ hμ m ell F f h w‖ ≤ d := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hF] with F hF
  intro advanced
  have hi(i:Fin 8):Integrable (fun w:ℝ=>pressureCoefficient i*
      (paid_pressure_moment% wordMoment) (pressureWord i) advanced μ hμ m ell F f h w):=
    (hF i advanced).1.const_mul (pressureCoefficient i)
  have he:pressureMoment advanced μ hμ m ell F f h=
      fun w:ℝ=>∑i:Fin 8,pressureCoefficient i*
        (paid_pressure_moment% wordMoment) (pressureWord i) advanced μ hμ m ell F f h w :=
    funext (fun w=>actual_pressure_moment_words advanced μ hμ m ell F f h w)
  rw [he]
  refine ⟨integrable_finsetSum Finset.univ (fun i _=>hi i),?_⟩
  rw [integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [integral_const_mul]
  apply (norm_sum_le Finset.univ _).trans
  simp only [norm_mul]
  apply (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hF i advanced).2 (norm_nonneg _))).trans
  rw [←Finset.sum_mul]
  change C*d ≤ ε
  dsimp only [d]
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0 < C+1)).mpr
  linarith only [hε]

private theorem response_gauge(f h:QuantumTest)(X:End):
    responseRead f h (deltaGauge X)=pairDelta Gauge (responseRead f h X) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Gauge (paid_shifted_response% gauge_pair) f h X
private theorem response_phi(f h:QuantumTest)(X:End):
    responseRead f h (deltaPhi X)=pairDelta Phi (responseRead f h X) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Phi (paid_shifted_response% phi_pair) f h X
private theorem response_pressure(f h:QuantumTest)(X:End):
    responseRead f h (pressureOperator X)=pressureMomentMatrix (responseRead f h X) := by
  change responseRead f h (pressureDerivation (nonmagneticProjection (secondJet X)))=_
  have hA:responseRead f h (pressureDerivation (nonmagneticProjection (secondJet X)))=
      pairDelta balancedGenerator (responseRead f h (nonmagneticProjection (secondJet X))) := by
    unfold pressureDerivation
    simp only [LinearMap.sub_apply,LinearMap.smul_apply]
    rw [←(paid_pressure_ward% jet_source)]
    unfold balancedPressureJet
    exact (paid_shifted_response% response_delta) balancedGenerator (paid_pressure_ward% generator_skew) f h _
  rw [hA]
  unfold pressureMomentMatrix pairProjection pairSecond nonmagneticProjection secondJet
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,LinearMap.comp_apply,
    LinearMap.add_apply,map_sub,map_add,map_smul,response_gauge,response_phi]
  module

private theorem response_one(f h:QuantumTest)(X:End):
    responseRead f h X 1 1=sourcePair f (X h) := by
  unfold responseRead
  rfl

theorem actual_pressure_moment_operator(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (f h:QuantumTest)(w:ℝ):
    pressureMoment advanced μ hμ m ell F f h w=
      sourcePair f (pressureOperator (compensatedMomentOperator advanced μ hμ m ell F w) h) := by
  have h0:=actual_moment_matrix_operator advanced μ hμ m ell F f h w
  have h1:=response_pressure f h (compensatedMomentOperator advanced μ hμ m ell F w)
  have h2:=congrArg (fun P:PairMatrix=>P 1 1) h1
  rw [←h0] at h2
  rw [response_one] at h2
  unfold pressureMoment
  exact h2.symm

elab "paid_pressure_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseFrequencyReturn 0) "LowEnergy") "ActualScalarPhaseFrequencyReturn"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private def leftWindow(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*thetaAction m ell

/-- This actual product difference preserves every ordered split of the
seven source derivatives. It is evaluated on the original CF square. -/
def pressureProductCross(X Y:End):End:=
  pressureFullJet (X*Y)-pressureFullJet X*Y-X*pressureFullJet Y

theorem actual_pressure_covariance_square_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    (z^2) • pressureFullJet (coreCovariance m ell F z hz)=
      pressureFullJet (coreCovariance m ell F z hz)*(compressionCore F*compressionCore F)+
      coreCovariance m ell F z hz*balancedPressureJet nonmagneticSecondField-
      coreCovariance m ell F z hz*pressureFullJet (phaseSquareOwn F)+
      pressureProductCross (coreCovariance m ell F z hz) (compressionCore F*compressionCore F)-
      pressureFullJet (leftWindow m ell F z hz*compressionCore F)-
      z • pressureFullJet (leftWindow m ell F z hz) := by
  have h0:coreCovariance m ell F z hz*(compressionCore F*compressionCore F)=
      leftWindow m ell F z hz*compressionCore F+z • leftWindow m ell F z hz+
        (z^2) • coreCovariance m ell F z hz := by
    have h:=congrArg (fun X:End=>leftWindow m ell F z hz*X)
      ((paid_pressure_frequency% resolvent_square_return) F z hz)
    simp only [mul_add,mul_smul_comm,mul_one] at h
    simpa only [leftWindow,coreCovariance,mul_assoc] using h
  have h1:=congrArg pressureFullJet h0
  simp only [map_add,map_smul] at h1
  have h2:pressureFullJet (compressionCore F*compressionCore F)=
      balancedPressureJet nonmagneticSecondField-pressureFullJet (phaseSquareOwn F) := by
    have hh:compressionCore F*compressionCore F=
        diagonalAction*diagonalAction-phaseSquareOwn F := by
      unfold phaseSquareOwn
      module
    rw [hh,map_sub,actual_pressure_source_field]
  unfold pressureProductCross
  rw [h2]
  simp only [mul_sub]
  linear_combination (norm:=module) -h1

def movingPressureOperator(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*
    balancedPressureJet nonmagneticSecondField*thetaAction m ell*resolventCore F z hz
def pressureRadialCurrent(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  resolventCore F (star z) (star_nonreal z hz)*thetaAction m ell*
    (thetaAction m ell*balancedPressureJet nonmagneticSecondField-
      balancedPressureJet nonmagneticSecondField*thetaAction m ell)*resolventCore F z hz
def pressureCFCurrent(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):End :=
  coreCovariance m ell F z hz*(compressionCore F*balancedPressureJet nonmagneticSecondField-
    balancedPressureJet nonmagneticSecondField*compressionCore F)*resolventCore F z hz

/-- No theta/pressure commutation is asserted: both actual currents remain. -/
theorem actual_moving_pressure_source_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    coreCovariance m ell F z hz*balancedPressureJet nonmagneticSecondField=
      movingPressureOperator m ell F z hz+pressureRadialCurrent m ell F z hz-
        pressureCFCurrent m ell F z hz := by
  have h:=paid_balanced_inverse% (balancedPressureJet nonmagneticSecondField) F z hz
  have hh:=congrArg (fun X:End=>leftWindow m ell F z hz*X) h
  unfold leftWindow at hh
  unfold movingPressureOperator pressureRadialCurrent pressureCFCurrent coreCovariance
  linear_combination (norm:=noncomm_ring) -hh

private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

/-- All contact poles, CF and radial currents, Own and ordered product splits
are kept together. Only this complete correction has a frequency integral. -/
def pressureCorrection(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(w:ℝ):End :=
  let z:=causalFrequency advanced μ w
  let hz:=causal_nonreal advanced μ hμ w
  let V:=coreCovariance m ell F z hz
  ((2*(phaseCoefficient:ℂ))*star (escapePole advanced μ w)) •
    pressureOperator (thetaAction m ell*inverseVolumeAction*thetaAction m ell)-
    pressureFullJet V*(compressionCore F*compressionCore F)-pressureRadialCurrent m ell F z hz+
    pressureCFCurrent m ell F z hz+V*pressureFullJet (phaseSquareOwn F)-
    pressureProductCross V (compressionCore F*compressionCore F)+
    pressureFullJet (leftWindow m ell F z hz*compressionCore F)+
    z • pressureFullJet (leftWindow m ell F z hz)

/-- The exact compensated source moment pays the actual moving pressure
with its complete source correction on the same CF orbit. -/
theorem actual_pressure_compensated_operator_return(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(w:ℝ):
    movingPressureOperator m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w)=
      pressureOperator (compensatedMomentOperator advanced μ hμ m ell F w)+
        pressureCorrection advanced μ hμ m ell F w := by
  let z:=causalFrequency advanced μ w
  let hz:=causal_nonreal advanced μ hμ w
  have h0:=actual_pressure_covariance_square_return m ell F z hz
  rw [actual_moving_pressure_source_return] at h0
  unfold compensatedMomentOperator pressureCorrection
  simp only [map_add,map_smul,pressureFullJet,LinearMap.comp_apply]
  dsimp only [z,hz] at h0
  simp only [pressureFullJet,LinearMap.comp_apply] at h0
  linear_combination (norm:=module) -h0

private theorem moving_pressure_pair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourcePair g (movingPressureOperator m ell F z hz g)=
      sourcePair (thetaAction m ell (resolventCore F z hz g))
        (balancedPressureJet nonmagneticSecondField (thetaAction m ell (resolventCore F z hz g))) := by
  unfold movingPressureOperator
  simp only [Module.End.mul_apply]
  rw [(paid_balanced_covariance% resolvent_pair) F z hz]
  have ht(f h:QuantumTest):sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h := by
    unfold thetaAction
    exact multiply_pair _ _ _ _
  rw [ht]

/-- This complete response, rather than any isolated pole or flux, is paid
by the fixed-source compensated moment. -/
def correctedPressure(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let z:=causalFrequency advanced μ w
  let v:=thetaAction m ell (resolventCore F z (causal_nonreal advanced μ hμ w) g)
  phaseCoefficient*balancedPressurePrice v+
    (1/2:ℝ)*(sourcePair g (pressureCorrection advanced μ hμ m ell F w g)).re-
    (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed v‖^2

theorem actual_corrected_pressure_moment_return(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g:QuantumTest)(w:ℝ):
    correctedPressure advanced μ hμ m ell F g w=
      -(1/2:ℝ)*(pressureMoment advanced μ hμ m ell F g g w).re := by
  have h0:=congrArg (fun X:End=>sourcePair g (X g))
    (actual_pressure_compensated_operator_return advanced μ hμ m ell F w)
  simp only [LinearMap.add_apply,(paid_phase_frequency% pair_add_right)] at h0
  rw [moving_pressure_pair,←actual_pressure_moment_operator] at h0
  have hr:=congrArg Complex.re h0
  simp only [Complex.add_re] at hr
  unfold correctedPressure balancedPressurePrice
  dsimp only
  have hc:phaseCoefficient≠0:=actual_phase_coefficient_positive.ne'
  field_simp [hc]
  rw [hr]
  ring

/-- A common source event pays the complete moving-pressure response. No
Own, CF-current, radial-current or contact-tail premise is supplied. -/
theorem actual_corrected_pressure_moment_tail(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (correctedPressure advanced μ hμ m ell F g) ∧
        |∫w:ℝ,correctedPressure advanced μ hμ m ell F g w| ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_pressure_moment_tail μ hμ g g (2*ε) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  obtain ⟨hi,hp⟩:=hF advanced
  have he:correctedPressure advanced μ hμ m ell F g=
      fun w:ℝ=>-(1/2:ℝ)*(pressureMoment advanced μ hμ m ell F g g w).re :=
    funext (fun w=>actual_corrected_pressure_moment_return advanced μ hμ m ell F g w)
  rw [he]
  refine ⟨hi.re.const_mul (-(1/2:ℝ)),?_⟩
  have hir:(∫w:ℝ,pressureMoment advanced μ hμ m ell F g g w).re=
      ∫w:ℝ,(pressureMoment advanced μ hμ m ell F g g w).re := by
    simpa only [RCLike.re_to_complex] using (integral_re hi).symm
  rw [integral_const_mul,←hir]
  rw [abs_mul]
  norm_num
  have hb:=Complex.abs_re_le_norm (∫w:ℝ,pressureMoment advanced μ hμ m ell F g g w)
  linarith only [hb,hp]

/-- The original pressure/source RHS, including its BF fixed-contact
component inside the native invoice. -/
def retardedPressureSource(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  let q:=resolventCore F z hz g
  let v:=thetaAction m ell q
  let u:=compensatedReader m ell F z hz g
  ActualLocalizedNativeWorkReturn.sourceNativeInvoice m ell F z hz g+
    (1/6:ℝ)*((sourcePair (thetaAction m ell (resolventCore F z hz (balancedGenerator g)))
      (nonmagneticSecondField v)).re-18*(sourcePair u (compressionCore F q)).re+
      (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q)
        (nonmagneticSecondField v)).re+
      (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed v‖^2)+
    radialBalancedContact m ell F z hz g

/-- Every correction is an actual source operator from the covariance
square return; no native flux or target budget is used to define this invoice. -/
def correctedSourceNativeInvoice(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)
    (g:QuantumTest)(w:ℝ):ℝ :=
  let z:=causalFrequency advanced μ w
  let hz:=causal_nonreal advanced μ hμ w
  let v:=thetaAction m ell (resolventCore F z hz g)
  retardedPressureSource m ell F z hz g+
    (1/12:ℝ)*(sourcePair g (pressureCorrection advanced μ hμ m ell F w g)).re-
    (phaseCoefficient*sourceTime 0*‖vacuum‖^2/4)*‖embed v‖^2

/-- Direct whole-native consumer: the positive pressure's side is preserved
when the entire corrected source response is substituted. -/
theorem actual_native_pressure_moment_return(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)
    (F:Index)(g:QuantumTest)(w:ℝ):
    (ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g).re-
      correctedSourceNativeInvoice advanced μ hμ m ell F g w=
      (1/12:ℝ)*(pressureMoment advanced μ hμ m ell F g g w).re := by
  have h0:=actual_whole_native_pressure_return m ell F (causalFrequency advanced μ w)
    (causal_nonreal advanced μ hμ w) g
  dsimp only at h0
  have h1:=actual_corrected_pressure_moment_return advanced μ hμ m ell F g w
  unfold correctedPressure at h1
  unfold correctedSourceNativeInvoice retardedPressureSource
  dsimp only
  linear_combination (norm:=ring_nf) h0-(1/6:ℝ)*h1

/-- Common-N payment of the complete signed native/source discrepancy. All
unpaid source currents remain explicitly in the corrected source invoice. -/
theorem actual_native_pressure_moment_tail(μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g).re-
          correctedSourceNativeInvoice advanced μ hμ m ell F g w) ∧
        |∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g).re-
          correctedSourceNativeInvoice advanced μ hμ m ell F g w| ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_pressure_moment_tail μ hμ g g (12*ε) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  obtain ⟨hi,hp⟩:=hF advanced
  have he:(fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
      (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g).re-
      correctedSourceNativeInvoice advanced μ hμ m ell F g w)=
      fun w:ℝ=>(1/12:ℝ)*(pressureMoment advanced μ hμ m ell F g g w).re :=
    funext (fun w=>actual_native_pressure_moment_return advanced μ hμ m ell F g w)
  rw [he]
  refine ⟨hi.re.const_mul (1/12:ℝ),?_⟩
  have hir:(∫w:ℝ,pressureMoment advanced μ hμ m ell F g g w).re=
      ∫w:ℝ,(pressureMoment advanced μ hμ m ell F g g w).re := by
    simpa only [RCLike.re_to_complex] using (integral_re hi).symm
  rw [integral_const_mul,←hir,abs_mul]
  norm_num
  have hb:=Complex.abs_re_le_norm (∫w:ℝ,pressureMoment advanced μ hμ m ell F g g w)
  linarith only [hb,hp]

private theorem source_mu_positive:0 < sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large

theorem actual_source_native_pressure_moment_tail(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g).re-
          correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g w) ∧
        |∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g).re-
          correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g w| ≤ ε :=
  actual_native_pressure_moment_tail sourceMu source_mu_positive g

private theorem frequency_same(advanced:Bool)(μ w:ℝ):
    SourceLocalizedInverseFormPayment.actualFrequency advanced μ w=causalFrequency advanced μ w := by
  cases advanced <;> simp [SourceLocalizedInverseFormPayment.actualFrequency,causalFrequency,
    SourceResolventBandLimit.line]

/-- Ordinary source integrability turns the whole signed discrepancy into
an honest difference of two full-frequency integrals. No pole is split off. -/
theorem actual_source_native_pressure_integral_payment(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g) ∧
        |(∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g).re)-
          (∫w:ℝ,correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g w)| ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_source_native_pressure_moment_tail g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  obtain ⟨hd,hp⟩:=hF advanced
  have hn:Integrable (fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
      (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g).re) := by
    have hi:=ActualBalancedPressureFrequencyPayment.actual_native_own_flux_integrable advanced m ell F g
    apply hi.re.congr (Eventually.of_forall (fun w=>?_))
    simp only [frequency_same,RCLike.re_to_complex]
  have hc:Integrable (correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g) := by
    apply (hn.sub hd).congr (Eventually.of_forall (fun w=>?_))
    change (_:ℝ) - ((_:ℝ) - (_:ℝ)) = (_:ℝ)
    ring
  refine ⟨hc,?_⟩
  rw [integral_sub hn hc] at hp
  exact hp

/-- Direct signed lower consumer. The remaining lower price belongs to the
explicit corrected source invoice, not to a supplied native-current budget. -/
theorem actual_source_native_pressure_integral_lower(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
          (causalFrequency advanced sourceMu w) (causal_nonreal advanced sourceMu source_mu_positive w) g).re) ≥
          (∫w:ℝ,correctedSourceNativeInvoice advanced sourceMu source_mu_positive m ell F g w)-ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_source_native_pressure_integral_payment g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have hp:=(abs_le.mp (hF advanced).2).1
  linarith only [hp]

end LowEnergy.ActualBalancedPressureMomentPayment
