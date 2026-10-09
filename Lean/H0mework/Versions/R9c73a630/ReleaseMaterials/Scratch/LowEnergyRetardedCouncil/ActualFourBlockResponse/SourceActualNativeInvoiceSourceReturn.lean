import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedFixedContactPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRestReaderFrequencyPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureFrequencyPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualNativeInvoiceSourceReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm SourceQuantumScalarChart SourceRetardedGraph
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolumeCurrent SourceHamiltonianScaleJet
open SourceNativeCutoffContact ActualMixedCovarianceTail ActualMixedWindowGram ActualVectorJointCost
open ActualSecondPressureMagneticPayment ActualBalancedForceRetardedPayment ActualLocalizedNativeWorkReturn
open ActualScalarPhaseFrequencyReturn ActualShiftedQuadraticWardPayment ActualBalancedFixedContactPayment
open ActualRestReaderFrequencyPayment ActualBalancedPressureFrequencyPayment ActualLocalizedJointFrequencyPayment
open SourceClockPhiRadiusSourceCurrent ActualWholeGammaPressureReturn ActualTwoResolventCascade
open ActualRawResidualTailPayment ActualPhaseBulkSquare ActualScalarPhaseJet
open SourceResolventBandLimit
open SourceLocalizedInverseFormPayment ReverseScalarGaugeWard ReverseNativeFrequencyWard
open SourceCoframeVolume SourcePhysicalKineticSquare FirstCurrentClockPrimitive
open SourceScalarInverseNativeEnergy
open FirstCurrentJointForceLoss FirstCurrentScalarForceAbsorption FirstCurrentClockPrimitiveSquare
open BalancedPrimitivePayer ReverseForcePhysicalPayment
open Lean Meta Elab Term MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private theorem mu_positive:0 < sourceMu:=lt_of_lt_of_le zero_lt_one source_mu_large
private theorem nonreal(advanced:Bool)(w:ℝ):(actualFrequency advanced sourceMu w).im≠0:=
  reverse_frequency_nonreal advanced sourceMu mu_positive w
attribute [local irreducible] sourcePair compressionCore resolventCore coreWindow nonmagneticSecondField

/-- These are the remaining actual source words, in their original order. -/
def liveNativeInvoice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  4*(fieldFlux nonmagneticSecondField m ell F z hz g g).re+
    (fieldFlux nonmagneticSecondField m ell F z hz (Gauge g) g).re+
    (fieldFlux nonmagneticSecondField m ell F z hz g (Gauge g)).re+
    (1/4:ℝ)*(orderedForcing (deltaPhi (compressionCore F)) m ell F z hz g g).re-
    (1/2:ℝ)*(orderedForcing (scaleDerivative (compressionCore F)) m ell F z hz g g).re-
    (3/2:ℝ)*(orderedForcing (compressionCore F) m ell F z hz g g).re

def retainedJoint(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  jointForceInputLoss F (1/16) (volumeAction (localizedPressureReader m ell F z hz g))
    (coreWindow m ell F z hz g)
def primitiveLoss(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  primitiveEnergy (balancedCompressionForce F (coreWindow m ell F z hz g))/21

def jointNativeWork(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  liveNativeInvoice m ell F z hz g+retainedJoint m ell F z hz g-
    primitiveLoss m ell F z hz g+balancedLocalizationContact m ell F z hz g

private theorem invoice_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourceNativeInvoice m ell F z hz g=liveNativeInvoice m ell F z hz g-
      (1/12:ℝ)*(fixedBalancedContact m ell F z hz g).re := rfl

/-- The native inventory is consumed once: its entire exact primitive
balance leaves one primitive force square with a negative sign. -/
theorem actual_primitive_inventory_return(F:Index)(w:QuantumTest):
    retainedNativePrice w-clearedNativePrice w-compensatedPrimitiveWork F w+
      (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2=
        -primitiveEnergy (balancedCompressionForce F w)/21 := by
  have hb:=(actual_native_primitive_joint_balance F w).1
  unfold primitiveNativeLoss at hb
  change retainedNativePrice w+(primitiveEnergy (balancedCompressionForce F w)/21+
      (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2)=
    clearedNativePrice w+compensatedPrimitiveWork F w at hb
  linarith only [hb]

/-- The original joint force square is retained instead of being discarded
by nonnegativity. The radius input and whole localization contact remain actual. -/
theorem actual_native_retained_joint_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    (ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g).re=
      jointNativeWork m ell F z hz g-
      (7*sourceTime 0/96)*‖embed (phiInverseAction (localizedPressureReader m ell F z hz g))‖^2-
      (1/12:ℝ)*(fixedBalancedContact m ell F z hz g).re := by
  rw [actual_whole_source_native_invoice,actual_balanced_pressure_localized_return]
  have hj:=actual_balanced_reader_joint_square F (localizedPressureReader m ell F z hz g)
    (coreWindow m ell F z hz g)
  unfold jointNativeWork retainedJoint primitiveLoss
  rw [invoice_source]
  simp only [coreWindow,Module.End.mul_apply] at hj ⊢
  linarith only [hj]

theorem actual_retained_joint_nonnegative(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    0 ≤ retainedJoint m ell F z hz g :=
  (actual_joint_force_input_loss F (1/16)
    (volumeAction (localizedPressureReader m ell F z hz g)) (coreWindow m ell F z hz g)).2

private theorem coefficient_nonnegative(sharp:Bool):0 ≤ bulkCoefficient sharp := by
  unfold bulkCoefficient
  have hn:0 < sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  apply div_nonneg (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  change 0 ≤ 8*sourceTime 0*sourceMu^2
  positivity
private theorem beta_nonnegative(sharp:Bool):0 ≤ 3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient) := by
  have ha:=coefficient_nonnegative sharp
  have hc:=actual_phase_coefficient_positive
  have hm:0 < sourceMu:=lt_of_lt_of_le zero_lt_one source_mu_large
  positivity

/-- The same principal Reserve pays the reader input while the complete
positive joint square is kept. No primitive gain is reused. -/
theorem actual_whole_retained_joint_lower(sharp advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):
    let z:=actualFrequency advanced sourceMu ω
    let hz:=nonreal advanced ω
    let β:=3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)
    β*(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g).re+
      (1/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell (resolventCore F z hz g) ≥
      β*(jointNativeWork m ell F z hz g-(1/12:ℝ)*(fixedBalancedContact m ell F z hz g).re)-
      β*nativeReaderWard advanced ω (restReader m ell F z hz g)/(512*(sourceMu-2*sourceTime 0)) := by
  dsimp only
  rw [actual_native_retained_joint_source]
  have hr:=actual_inverse_radius_reader_price (localizedPressureReader m ell F
    (actualFrequency advanced sourceMu ω) (nonreal advanced ω) g)
  have hp:=actual_complete_reader_reserve_noether_payment sharp advanced m ell F g ω
  dsimp only at hp
  have hb:=beta_nonnegative sharp
  have hmul:=mul_le_mul_of_nonneg_left hr hb
  nlinarith only [hp,hmul]

elab "paid_invoice_rest%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRestReaderFrequencyPayment 0) "LowEnergy") "ActualRestReaderFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_invoice_joint%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedJointFrequencyPayment 0) "LowEnergy") "ActualLocalizedJointFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_invoice_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureFrequencyPayment 0) "LowEnergy") "ActualBalancedPressureFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_invoice_reserve%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRawResidualTailPayment 0) "LowEnergy") "ActualRawResidualTailPayment"
  mkConstWithFreshMVarLevels (Name.str ns "reserve_frequency_integrable")

private def q(advanced:Bool)(F:Index)(g:QuantumTest)(w:ℝ):QuantumTest:=
  resolventCore F (actualFrequency advanced sourceMu w) (nonreal advanced w) g
private def k(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):QuantumTest:=
  localizedPressureReader m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g
private def c(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ:=
  fixedBalancedContact m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g
private theorem re_symm(f h:QuantumTest):(sourcePair f h).re=(sourcePair h f).re:=by
  unfold sourcePair
  exact inner_re_symm (𝕜:=ℂ) _ _

private theorem primitive_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>primitiveLoss m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g) := by
  have hi:=(paid_invoice_rest% single_pair_integrable) advanced F
    (balancedCompressionForce F*thetaAction m ell)
    (positivePrimitive*balancedCompressionForce F*thetaAction m ell) g
  apply (hi.re.div_const 21).congr
  exact Eventually.of_forall (fun w=>by simp only [primitiveLoss,primitiveEnergy,coreWindow,Module.End.mul_apply,RCLike.re_to_complex])
private theorem reader_radius_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>‖embed (phiInverseAction (k advanced m ell F g w))‖^2) := by
  have hi:=(actual_localized_reader_pair_integrable advanced m ell F g phiInverseAction phiInverseAction).re
  apply hi.congr
  exact Eventually.of_forall (fun w=>by
    simpa only [sourcePair,k,RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ)
      (embed (phiInverseAction (k advanced m ell F g w))))
private theorem joint_cross_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>(sourcePair (k advanced m ell F g w)
      (balancedCompressionForce F (thetaAction m ell (q advanced F g w)))).re) := by
  have hi:=(paid_invoice_rest% mixed_pair_integrable) advanced F
    (nonmagneticSecondField*thetaAction m ell) (balancedCompressionForce F*thetaAction m ell) (1:End) g
  apply hi.re.congr
  apply Eventually.of_forall
  intro w
  simp only [RCLike.re_to_complex,Module.End.one_apply,Module.End.mul_apply]
  rw [re_symm]
  dsimp only [q,k]
  rw [(paid_invoice_joint% localized_reader_double)]

/-- The full actual joint square is ordinary L1 on the complete one-plus-two
resolvent source orbit. Its positive sign does not require a graph budget. -/
theorem actual_retained_joint_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>retainedJoint m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g) := by
  have hX:=joint_cross_integrable advanced m ell F g
  have hP:=primitive_integrable advanced m ell F g
  have hK:=reader_radius_integrable advanced m ell F g
  apply (((hX.const_mul (1/6:ℝ)).add hP).add (hK.const_mul (7*sourceTime 0/96))).congr
  apply Eventually.of_forall
  intro w
  have he:=actual_balanced_reader_joint_square F (k advanced m ell F g w)
    (thetaAction m ell (q advanced F g w))
  simpa only [retainedJoint,primitiveLoss,coreWindow,Module.End.mul_apply,k,q,Pi.add_apply] using he
private theorem localization_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>balancedLocalizationContact m ell F
      (actualFrequency advanced sourceMu w) (nonreal advanced w) g) := by
  have hp:=(paid_invoice_frequency% balanced_pair_integrable) advanced m ell F g
  have hX:=joint_cross_integrable advanced m ell F g
  apply (hp.sub (hX.const_mul (1/6:ℝ))).congr
  apply Eventually.of_forall
  intro w
  have he:=actual_balanced_pressure_localized_return m ell F (actualFrequency advanced sourceMu w)
    (nonreal advanced w) g
  dsimp only [k,q,Pi.sub_apply,Pi.add_apply]
  linarith only [he]

private theorem work_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)
    (hc:Integrable (c advanced m ell F g)):
    Integrable (fun w:ℝ=>jointNativeWork m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g) := by
  have hi:=(actual_source_native_invoice_integrable advanced m ell F g).add (hc.re.const_mul (1/12:ℝ))
  have hl:Integrable (fun w:ℝ=>liveNativeInvoice m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g):=by
    apply hi.congr
    apply Eventually.of_forall
    intro w
    simp only [Pi.add_apply,RCLike.re_to_complex]
    rw [invoice_source]
    dsimp only [c]
    ring
  exact ((hl.add (actual_retained_joint_integrable advanced m ell F g)).sub
    (primitive_integrable advanced m ell F g)).add (localization_integrable advanced m ell F g)

private def beta(sharp:Bool):ℝ:=3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)

private theorem contact_congr(m ell:ℕ)(F:Index)(z u:ℂ)(hz:z.im≠0)(hu:u.im≠0)
    (g:QuantumTest)(he:z=u):fixedBalancedContact m ell F z hz g=fixedBalancedContact m ell F u hu g := by
  cases he
  rfl
private theorem resolvent_congr(F:Index)(z u:ℂ)(hz:z.im≠0)(hu:u.im≠0)(he:z=u):
    resolventCore F z hz=resolventCore F u hu := by
  cases he
  rfl
private theorem beta_price_nonnegative(sharp:Bool):0 ≤ beta sharp:=by
  unfold beta
  exact beta_nonnegative sharp
private theorem beta_source(sharp:Bool):
    3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)=beta sharp:=rfl
attribute [local irreducible] beta
private theorem causal_actual(advanced:Bool)(μ w:ℝ):causalFrequency advanced μ w=actualFrequency advanced μ w := by
  cases advanced
  · rfl
  · simp only [causalFrequency,actualFrequency,ite_true,line,Complex.star_def,
      map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
    ring
private theorem reserve_frequency_return(advanced sharp:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    reserveFrequency advanced sharp m ell F g w=sourceReserve sharp m ell (q advanced F g w) := by
  unfold reserveFrequency q
  change sourceReserve sharp m ell (resolventCore F (causalFrequency advanced sourceMu w) _ g)=_
  rw [resolvent_congr F (causalFrequency advanced sourceMu w) (actualFrequency advanced sourceMu w)
    _ (nonreal advanced w) (causal_actual advanced sourceMu w)]

/-- The generated fixed-contact tail is consumed inside the whole retained
joint invoice. Every Phi/coframe/CF forcing order and the actual remainder
Noether debit remains in the same frequency integral. -/
theorem actual_retained_joint_invoice_causal_lower(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced sharp:Bool,
      Integrable (fun w:ℝ=>jointNativeWork m ell F (actualFrequency advanced sourceMu w)
        (nonreal advanced w) g) ∧
      beta sharp*(∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
        (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re)+
      (1/4:ℝ)*(2/sourceMu)*(∫w:ℝ,reserveFrequency advanced sharp m ell F g w) ≥
      beta sharp*(∫w:ℝ,jointNativeWork m ell F (actualFrequency advanced sourceMu w)
        (nonreal advanced w) g)-
      beta sharp*(∫w:ℝ,nativeReaderWard advanced w
        (restReader m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g))/
        (512*(sourceMu-2*sourceTime 0))-ε := by
  intro ε hε
  let B:=beta false+beta true
  have hB:0 ≤ B:=add_nonneg (beta_price_nonnegative false) (beta_price_nonnegative true)
  let δ:=ε/(B+1)
  have hδ:0 < δ:=by
    dsimp only [δ]
    exact div_pos hε (by linarith only [hB])
  obtain ⟨N,hN⟩:=actual_fixed_balanced_contact_tail g δ hδ
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced sharp
  have he(w:ℝ):causalFrequency advanced sourceMu w=actualFrequency advanced sourceMu w:=by
    cases advanced
    · rfl
    · simp only [causalFrequency,actualFrequency,ite_true,line,Complex.star_def,
        map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
      ring
  have hc:Integrable (c advanced m ell F g):=by
    obtain ⟨hi,_⟩:=hF advanced
    apply hi.congr
    exact Eventually.of_forall (fun w=>by
      dsimp only [c]
      exact contact_congr m ell F _ _ _ _ g (he w))
  have hpContact:‖∫w:ℝ,c advanced m ell F g w‖ ≤ δ:=by
    have hp:=(hF advanced).2
    have hfun:(fun w:ℝ=>fixedBalancedContact m ell F (causalFrequency advanced sourceMu w)
      ((paid_fixed_contact% causal_nonreal) advanced sourceMu
        (lt_of_lt_of_le zero_lt_one source_mu_large) w) g)=c advanced m ell F g:=by
      funext w;dsimp only [c]
      exact contact_congr m ell F _ _ _ _ g (he w)
    rwa [hfun] at hp
  have hcRe:Integrable (fun w:ℝ=>(c advanced m ell F g w).re):=by
    simpa only [RCLike.re_to_complex] using hc.re
  have hW:=work_integrable advanced m ell F g hc
  have hFlux:Integrable (fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
    (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re):=
      (actual_native_own_flux_integrable advanced m ell F g).re
  have hReserve:Integrable (reserveFrequency advanced sharp m ell F g):=
    (paid_invoice_reserve%) advanced sharp m ell F g
  have hRest:=actual_rest_reader_noether_integrable advanced m ell F g
  have hRHS:Integrable (fun w:ℝ=>beta sharp*
      (jointNativeWork m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g-
        (c advanced m ell F g w).re/12)-
      beta sharp*nativeReaderWard advanced w (restReader m ell F
        (actualFrequency advanced sourceMu w) (nonreal advanced w) g)/(512*(sourceMu-2*sourceTime 0))):=
    ((hW.sub (hcRe.div_const 12)).const_mul _).sub ((hRest.const_mul _).div_const _)
  have hLHS:Integrable (fun w:ℝ=>beta sharp*(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
      (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re+
      ((1/4:ℝ)*(2/sourceMu))*reserveFrequency advanced sharp m ell F g w):=
    (hFlux.const_mul _).add (hReserve.const_mul _)
  have hPaid:=integral_mono_ae hRHS hLHS (Eventually.of_forall (fun w=>by
    have hp:=actual_whole_retained_joint_lower sharp advanced m ell F g w
    dsimp only at hp
    dsimp only
    rw [reserve_frequency_return]
    rw [beta_source sharp] at hp
    dsimp only [c,q]
    nlinarith only [hp]))
  have hRsplit:=integral_sub
    ((hW.sub (hcRe.div_const (12:ℝ))).const_mul (beta sharp))
    ((hRest.const_mul (beta sharp)).div_const (512*(sourceMu-2*sourceTime 0)))
  simp only [Pi.sub_apply] at hRsplit
  rw [hRsplit] at hPaid
  have hWsplit:=integral_sub hW (hcRe.div_const (12:ℝ))
  have hLsplit:=integral_add (hFlux.const_mul (beta sharp))
    (hReserve.const_mul ((1/4:ℝ)*(2/sourceMu)))
  rw [integral_const_mul,hWsplit,integral_div,integral_div,integral_const_mul,
    hLsplit,integral_const_mul,integral_const_mul] at hPaid
  have hRe:|∫w:ℝ,(c advanced m ell F g w).re| ≤ δ:=by
    have hre:=integral_re hc
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans hpContact
  have hb:=beta_price_nonnegative sharp
  have hsharp:beta sharp ≤ B:=by
    cases sharp
    · exact le_add_of_nonneg_right (beta_price_nonnegative true)
    · exact le_add_of_nonneg_left (beta_price_nonnegative false)
  have hSmall:beta sharp*δ/12 ≤ ε:=by
    have h1:=mul_le_mul_of_nonneg_right hsharp hδ.le
    have h2:B*δ ≤ ε:=by
      dsimp only [δ]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by linarith only [hB] : 0 < B+1)).mpr
      nlinarith only [hε]
    nlinarith only [h1,h2,hε]
  have hUpper:beta sharp*(∫w:ℝ,(c advanced m ell F g w).re)/12 ≤ ε:=by
    have hu:=(le_abs_self _).trans hRe
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu hb)
      (by norm_num : (0:ℝ) ≤ 12)).trans hSmall
  refine ⟨hW,?_⟩
  linarith only [hPaid,hUpper]

attribute [local irreducible] sourceQ sourceReserve reserveFrequency bulkCoefficient
  ActualUnweightedSquareCurrentPayment.shiftedSquare ActualShiftedQuadraticWardPayment.shiftedSquare
  ActualUnweightedSquareCurrentPayment.shiftedResponse
  ActualNativeOwnSquareWardPayment.nativeOwnFlux
  ActualShiftedQuadraticWardPayment.radialResponseCorrection
  ActualShiftedQuadraticWardPayment.liveResponseCorrection
  ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual
  ActualBulkCurrentSquareReturn.forceResponse phaseSecond ActualPhaseWardIntertwiner.shiftedInverseWard diagonalAction

private def radialFrequency(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  ActualShiftedQuadraticWardPayment.radialResponseCorrection m ell F
    (actualFrequency advanced sourceMu w) (nonreal advanced w) g
private def correctedFrequency(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g w-
    ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
      (actualFrequency advanced sourceMu w) (nonreal advanced w) g-
    radialFrequency advanced m ell F g w
attribute [local irreducible] radialFrequency correctedFrequency
private theorem radial_frequency_source(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    (radialFrequency advanced m ell F g w).re=
      ActualUnweightedSquareCurrentPayment.radialSlot m ell (q advanced F g w) := by
  rw [ActualUnweightedSquareCurrentPayment.actual_radial_slot_commutator]
  unfold radialFrequency ActualShiftedQuadraticWardPayment.radialResponseCorrection q
  have hB:ActualShiftedQuadraticWardPayment.shiftedSquare=
      ActualUnweightedSquareCurrentPayment.shiftedSquare := by
    unfold ActualShiftedQuadraticWardPayment.shiftedSquare ActualUnweightedSquareCurrentPayment.shiftedSquare
    rfl
  rw [hB]
  simp only [coreWindow,Module.End.mul_apply]

private theorem shifted_response_source(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g w=
      sourcePair (coreWindow m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g)
        (ActualShiftedQuadraticWardPayment.shiftedSquare
          (coreWindow m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g)) := by
  unfold ActualUnweightedSquareCurrentPayment.shiftedResponse
  have hB:ActualUnweightedSquareCurrentPayment.shiftedSquare=
      ActualShiftedQuadraticWardPayment.shiftedSquare:=by
    unfold ActualShiftedQuadraticWardPayment.shiftedSquare ActualUnweightedSquareCurrentPayment.shiftedSquare
    rfl
  rw [hB]
  change sourcePair (thetaAction m ell (resolventCore F (causalFrequency advanced sourceMu w)
      ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g))
    (ActualShiftedQuadraticWardPayment.shiftedSquare
      (thetaAction m ell (resolventCore F (causalFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g)))=_
  have hr:=resolvent_congr F (causalFrequency advanced sourceMu w)
    (actualFrequency advanced sourceMu w)
    ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w)
    (nonreal advanced w) (causal_actual advanced sourceMu w)
  rw [hr]
  simp only [coreWindow,Module.End.mul_apply]

private theorem flux_congr(m ell:ℕ)(F:Index)(z v:ℂ)(hz:z.im≠0)(hv:v.im≠0)
    (g:QuantumTest)(he:z=v):
    ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g=
      ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F v hv g:=by cases he;rfl
private theorem radial_congr(m ell:ℕ)(F:Index)(z v:ℂ)(hz:z.im≠0)(hv:v.im≠0)
    (g:QuantumTest)(he:z=v):
    ActualShiftedQuadraticWardPayment.radialResponseCorrection m ell F z hz g=
      ActualShiftedQuadraticWardPayment.radialResponseCorrection m ell F v hv g:=by cases he;rfl

private theorem corrected_native_tail(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
        Integrable (correctedFrequency advanced m ell F g) ∧
        ‖∫w:ℝ,correctedFrequency advanced m ell F g w‖ ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=ActualShiftedQuadraticWardPayment.actual_corrected_shifted_response_tail g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have he(w:ℝ):
      sourcePair (coreWindow m ell F (causalFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g)
        (ActualShiftedQuadraticWardPayment.shiftedSquare
          (coreWindow m ell F (causalFrequency advanced sourceMu w)
            ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g))-
        ActualShiftedQuadraticWardPayment.liveResponseCorrection m ell F (causalFrequency advanced sourceMu w)
          ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g=
        correctedFrequency advanced m ell F g w := by
    have hz:=causal_actual advanced sourceMu w
    have hr:=resolvent_congr F _ _
      ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) (nonreal advanced w) hz
    have hwin:coreWindow m ell F (causalFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w)=
        coreWindow m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w):=by
      unfold coreWindow
      rw [hr]
    rw [ActualShiftedQuadraticWardPayment.actual_live_response_parts,
      ActualNativeOwnSquareWardPayment.actual_native_own_flux_source,hwin,
      flux_congr m ell F (causalFrequency advanced sourceMu w) (actualFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) (nonreal advanced w) g hz,
      radial_congr m ell F (causalFrequency advanced sourceMu w) (actualFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) (nonreal advanced w) g hz]
    unfold correctedFrequency radialFrequency
    rw [shifted_response_source]
    ring
  have hf:=hF advanced
  dsimp only at hf
  have hfun:(fun w:ℝ=>sourcePair (coreWindow m ell F (causalFrequency advanced sourceMu w)
      ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g)
      (ActualShiftedQuadraticWardPayment.shiftedSquare
        (coreWindow m ell F (causalFrequency advanced sourceMu w)
          ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g))-
      ActualShiftedQuadraticWardPayment.liveResponseCorrection m ell F (causalFrequency advanced sourceMu w)
        ((paid_fixed_contact% causal_nonreal) advanced sourceMu mu_positive w) g)=
        correctedFrequency advanced m ell F g := funext he
  rw [hfun] at hf
  exact hf

elab "paid_invoice_unweighted%" field:ident : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualUnweightedSquareCurrentPayment 0) "LowEnergy")
    "ActualUnweightedSquareCurrentPayment") field.getId.eraseMacroScopes.toString)

private def radialHalfPrice(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):ℝ :=
  (∫w:ℝ,inverseForm (thetaAction (m/2) m (q advanced F g w)))+
    (∫w:ℝ,inverseForm (thetaAction (ell/2) ell (q advanced F g w)))

private theorem radial_integral_lower(advanced:Bool)(m ell:ℕ)(hm:1 ≤ m)(hml:m ≤ ell)
    (F:Index)(g:QuantumTest):
    -(432*phaseCoefficient/3481)*radialHalfPrice advanced m ell F g ≤
      ∫w:ℝ,(radialFrequency advanced m ell F g w).re := by
  have hfun:(paid_invoice_unweighted% causalCore) advanced F g=q advanced F g:=by
    funext w
    change resolventCore F (causalFrequency advanced sourceMu w) _ g=
      resolventCore F (actualFrequency advanced sourceMu w) _ g
    exact LinearMap.congr_fun (resolvent_congr F _ _ _ _
      (causal_actual advanced sourceMu w)) g
  obtain ⟨hi,hp⟩:=ActualUnweightedSquareCurrentPayment.actual_radial_slot_causal_window_price
    advanced m ell hm hml F g
  rw [hfun] at hi hp
  have hread:(fun w:ℝ=>ActualUnweightedSquareCurrentPayment.radialSlot m ell (q advanced F g w))=
      (fun w:ℝ=>(radialFrequency advanced m ell F g w).re):=by
    funext w;exact (radial_frequency_source advanced m ell F g w).symm
  rw [hread] at hi
  simp_rw [←radial_frequency_source] at hp
  change (∫w:ℝ,|(radialFrequency advanced m ell F g w).re|)/(2*phaseCoefficient) ≤
    (216/3481:ℝ)*radialHalfPrice advanced m ell F g at hp
  have hpc:=actual_phase_coefficient_positive
  have hu: (∫w:ℝ,|(radialFrequency advanced m ell F g w).re|) ≤
      (432*phaseCoefficient/3481)*radialHalfPrice advanced m ell F g:=by
    apply (div_le_iff₀ (by positivity : 0 < 2*phaseCoefficient)).mp at hp
    nlinarith only [hp]
  -- The lower integrand is minus the absolute value, not the absolute value.
  have hneg:-(∫w:ℝ,|(radialFrequency advanced m ell F g w).re|) ≤
      ∫w:ℝ,(radialFrequency advanced m ell F g w).re:=by
    have hh:=integral_mono hi.abs.neg hi (fun w:ℝ=>neg_abs_le
      ((radialFrequency advanced m ell F g w).re))
    simpa only [Pi.neg_apply,integral_neg] using hh
  linarith only [hu,hneg]

/-- The original raw residual receives the retained joint square, three
quarters of its Reserve, its actual two-resolvent boundary and the complete
radial source price. The remaining native invoice stays as actual words. -/
theorem actual_raw_retained_joint_source_lower(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced sharp:Bool,
      (∫w:ℝ,ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual advanced sharp m ell F g w) ≥
        Real.pi*sourceQ sharp m ell g+
        (3/4:ℝ)*(2/sourceMu)*(∫w:ℝ,reserveFrequency advanced sharp m ell F g w)+
        2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
          (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2+
        (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*
          (∫w:ℝ,ActualBulkCurrentSquareReturn.forceResponse advanced m ell F g w)+
        beta sharp*(∫w:ℝ,jointNativeWork m ell F (actualFrequency advanced sourceMu w)
          (nonreal advanced w) g)-
        beta sharp*(∫w:ℝ,nativeReaderWard advanced w
          (restReader m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g))/
          (512*(sourceMu-2*sourceTime 0))-
        beta sharp*(432*phaseCoefficient/3481)*radialHalfPrice advanced m ell F g-ε := by
  intro ε hε
  let B:=beta false+beta true
  have hB:0 ≤ B:=add_nonneg (beta_price_nonnegative false) (beta_price_nonnegative true)
  obtain ⟨N0,h0⟩:=ActualUnweightedSquareCurrentPayment.actual_raw_shifted_square_paid_return g
    (ε/3) (by positivity)
  obtain ⟨N1,h1⟩:=actual_retained_joint_invoice_causal_lower g (ε/3) (by positivity)
  obtain ⟨N2,h2⟩:=corrected_native_tail g ((ε/3)/(B+1)) (by positivity)
  refine ⟨max 1 (max N0 (max N1 N2)),fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml,
    h2 m (by omega) ell hml] with F hF0 hF1 hF2
  intro advanced sharp
  have hp0:=hF0 advanced sharp
  have hp1:=(hF1 advanced sharp).2
  obtain ⟨hi,hsmall⟩:=hF2 advanced
  have hFlux:=actual_native_own_flux_integrable advanced m ell F g
  have hShift:=ActualUnweightedSquareCurrentPayment.actual_shifted_response_integrable advanced m ell F g
  have hRad:Integrable (radialFrequency advanced m ell F g):=by
    have hsum:=hShift.sub hFlux
    apply (hsum.sub hi).congr
    exact Eventually.of_forall (fun w=>by unfold correctedFrequency;simp only [Pi.sub_apply];ring)
  have hEq:(∫w:ℝ,(correctedFrequency advanced m ell F g w).re)=
      (∫w:ℝ,(ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g w).re)-
      (∫w:ℝ,(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
        (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re)-
      (∫w:ℝ,(radialFrequency advanced m ell F g w).re) := by
    have hs:Integrable (fun w:ℝ=>(ActualUnweightedSquareCurrentPayment.shiftedResponse advanced m ell F g w).re):=by
      simpa only [RCLike.re_to_complex] using hShift.re
    have hf:Integrable (fun w:ℝ=>(ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F
      (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re):=by
      simpa only [RCLike.re_to_complex] using hFlux.re
    have hr:Integrable (fun w:ℝ=>(radialFrequency advanced m ell F g w).re):=by
      simpa only [RCLike.re_to_complex] using hRad.re
    simp only [correctedFrequency,Complex.sub_re]
    have hsplit:=integral_sub (hs.sub hf) hr
    simp only [Pi.sub_apply] at hsplit
    rw [hsplit,integral_sub hs hf]
  have hRe:|∫w:ℝ,(correctedFrequency advanced m ell F g w).re| ≤ (ε/3)/(B+1):=by
    have hre:=integral_re hi
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    exact (Complex.abs_re_le_norm _).trans hsmall
  have hb:=beta_price_nonnegative sharp
  have hsharp:beta sharp ≤ B:=by
    cases sharp
    · exact le_add_of_nonneg_right (beta_price_nonnegative true)
    · exact le_add_of_nonneg_left (beta_price_nonnegative false)
  have hError:beta sharp*|∫w:ℝ,(correctedFrequency advanced m ell F g w).re| ≤ ε/3:=by
    have hp:=mul_le_mul_of_nonneg_left hRe hb
    have hh:beta sharp*((ε/3)/(B+1)) ≤ ε/3:=by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by linarith only [hB] : 0 < B+1)).mpr
      nlinarith only [hsharp,hε]
    exact hp.trans hh
  have hLower:=mul_le_mul_of_nonneg_left (neg_abs_le (∫w:ℝ,(correctedFrequency advanced m ell F g w).re)) hb
  have hPenalty:-(ε/3) ≤ beta sharp*(∫w:ℝ,(correctedFrequency advanced m ell F g w).re):=by
    nlinarith only [hLower,hError]
  rw [beta_source sharp] at hp0
  rw [hEq] at hPenalty
  have hrad:=radial_integral_lower advanced m ell (by omega) hml F g
  have hradPaid:=mul_le_mul_of_nonneg_left hrad hb
  nlinarith only [hp0,hp1,hPenalty,hradPaid]

end LowEnergy.ActualNativeInvoiceSourceReturn
