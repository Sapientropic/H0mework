import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedForceRetardedPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRawResidualTailPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualLocalizedNativeWorkReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum SourceQuantumScalarChart
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy
open SourceHamiltonianScaleJet SourceClockPhiRadiusSourceCurrent SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceScalarNativeComparison SourceScalarEssentialBudget SourceScalarInverseBulk
open ActualMixedWindowGram ActualSecondPressureMagneticPayment ActualBalancedForceRetardedPayment
open ActualScalarPhaseFrequencyReturn ActualScalarPhaseJet ActualPhaseBulkSquare ActualTwoResolventCascade ActualRawResidualTailPayment
open SourceRetardedGraph SourceJointResidualEnergy FullYSourceResolventGraphSplice SourceNativeCutoffContact
open ReverseNativeFrequencyWard FirstCurrentScalarForceAbsorption FirstCurrentJointBudget ScalarInputJointNoether
open SourceLocalizedInverseFormPayment BalancedPrimitivePayer ReverseForcePhysicalPayment
open Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair resolventCore compressionCore diagonalAction nonmagneticSecondField

private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- All non-scalar Hamiltonian departments stay in the source remainder. -/
def pressureDepartments:End:=nonmagneticBulk+(2:ℂ) • diagonalAction

def readerRemainderAction(F:Index):End:=
  (4*(phaseCoefficient:ℂ)) • (inverseVolumeAction*defectAction F)+
  (4*(phaseCoefficient:ℂ)) • (inverseVolumeAction*compressionCore F-compressionCore F*inverseVolumeAction)+
  (2*(phaseCoefficient:ℂ)) • (diagonalAction*inverseVolumeAction-inverseVolumeAction*diagonalAction)-
  (phaseCoefficient:ℂ) • (pressureDepartments*inverseVolumeAction+inverseVolumeAction*pressureDepartments)-
  (4:ℂ) • (phaseForce*phaseForce)

/-- The principal scalar part is the actual compressed Hamiltonian; the
whole inverse-volume and Own corrections are retained in the same equation. -/
theorem actual_reader_principal_source(F:Index):
    nonmagneticSecondField=(4*(phaseCoefficient:ℂ)) • (compressionCore F*inverseVolumeAction)+
      readerRemainderAction F := by
  unfold nonmagneticSecondField readerRemainderAction pressureDepartments defectAction
  simp only [add_mul,mul_add,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add,smul_sub]
  module

def restReader(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest:=
  let w:=thetaAction m ell (resolventCore F z hz g)
  let Rbar:=resolventCore F (star z) (star_nonreal z hz)
  (4*(phaseCoefficient:ℂ)*star z) • Rbar (inverseVolumeAction w)+Rbar (readerRemainderAction F w)

theorem actual_localized_reader_principal_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    localizedPressureReader m ell F z hz g=
      (4*(phaseCoefficient:ℂ)) • inverseVolumeAction (thetaAction m ell (resolventCore F z hz g))+
        restReader m ell F z hz g := by
  have hi:=(actual_original_cf_inverses F (star z) (star_nonreal z hz)).2
  have hRC:resolventCore F (star z) (star_nonreal z hz)*compressionCore F=
      (1:End)+star z • resolventCore F (star z) (star_nonreal z hz) := by
    change resolventCore F (star z) (star_nonreal z hz)*(compressionCore F-star z • (1:End))=1 at hi
    simp only [mul_sub,mul_smul_comm,mul_one] at hi
    linear_combination (norm:=module) hi
  unfold localizedPressureReader
  rw [actual_reader_principal_source F]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,map_add,map_smul]
  have h:=LinearMap.congr_fun hRC (inverseVolumeAction (thetaAction m ell (resolventCore F z hz g)))
  simp only [Module.End.mul_apply,LinearMap.add_apply,Module.End.one_apply,LinearMap.smul_apply] at h
  rw [h]
  unfold restReader
  dsimp only
  simp only [smul_add,smul_smul]
  module

private theorem square_add{V:Type*}[NormedAddCommGroup V](x y:V):
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h:=norm_add_le x y
  have hn:=norm_nonneg (x+y)
  have hx:=norm_nonneg x
  have hy:=norm_nonneg y
  nlinarith only [h,hn,hx,hy,sq_nonneg (‖x‖-‖y‖)]

theorem actual_reader_native_principal_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    nativeScalarEnergy (localizedPressureReader m ell F z hz g) ≤
      32*phaseCoefficient^2*inverseNativeEnergy (thetaAction m ell (resolventCore F z hz g))+
      2*nativeScalarEnergy (restReader m ell F z hz g) := by
  rw [actual_localized_reader_principal_return,←original_inverse_native_return]
  unfold nativeScalarEnergy
  simp only [map_add,map_smul]
  have h(a:ScalarIndex):
      ‖embed (covariantMomentum (scalarDirection a)
        ((4*(phaseCoefficient:ℂ)) • inverseVolumeAction (thetaAction m ell (resolventCore F z hz g))+
          restReader m ell F z hz g))‖^2 ≤
      32*phaseCoefficient^2*‖embed (covariantMomentum (scalarDirection a)
        (inverseVolumeAction (thetaAction m ell (resolventCore F z hz g))))‖^2+
      2*‖embed (covariantMomentum (scalarDirection a) (restReader m ell F z hz g))‖^2 := by
    have hp:=square_add ((4*(phaseCoefficient:ℂ)) • embed (covariantMomentum (scalarDirection a)
      (inverseVolumeAction (thetaAction m ell (resolventCore F z hz g)))))
      (embed (covariantMomentum (scalarDirection a) (restReader m ell F z hz g)))
    have hc:(4*(phaseCoefficient:ℂ))=((4*phaseCoefficient:ℝ):ℂ):=by push_cast;rfl
    simp only [map_add,map_smul,hc,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at hp ⊢
    nlinarith only [hp]
  have ht:=Finset.sum_le_sum (fun a (_:a∈Finset.univ)=>h a)
  simp only [map_add,map_smul] at ht
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum] using ht

elab "paid_local_native_gap%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherCommon 0) "LowEnergy") "FirstCurrentJointBudget"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem n_positive:0<sourceTime 0:=by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

/-- The original phase coefficient, lapse and actual vacuum fix the gain. -/
theorem actual_phase_coefficient_reserve_bound:phaseCoefficient ≤ 16 := by
  have hn:=n_positive
  have hl:sourceTime 0<1:=paid_local_native_gap% n_lt_one
  have hc:=actual_affine_hardy_source_cost
  unfold affineHardyCost at hc
  have hv:‖vacuum‖^2 ≤16:=by linarith only [hc]
  have hn3:(sourceTime 0)^3≤1:=by nlinarith only [hn,hl,sq_nonneg (sourceTime 0-1)]
  unfold phaseCoefficient
  exact (mul_le_mul_of_nonneg_right hn3 (sq_nonneg _)).trans (by simpa only [one_mul] using hv)

/-- In the actual raw-price normalization, one quarter of the same-window
native Reserve pays the reader's principal scalar component. -/
theorem actual_principal_reader_reserve_payment(sharp:Bool)(m ell:ℕ)(F:Index)(z:ℂ)
    (hz:z.im≠0)(g:QuantumTest):
    (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*(sourceTime 0/256)*
      (32*phaseCoefficient^2*inverseNativeEnergy (thetaAction m ell (resolventCore F z hz g))) ≤
      (1/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell (resolventCore F z hz g) := by
  have hcost:0 ≤ coefficientCost sharp:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hc:=actual_phase_coefficient_positive
  have hmu:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large
  have hn:=n_positive
  have he:0 ≤ inverseNativeEnergy (thetaAction m ell (resolventCore F z hz g)):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hS:(3/4:ℝ)*coefficientCost sharp*inverseNativeEnergy (thetaAction m ell (resolventCore F z hz g)) ≤
      sourceReserve sharp m ell (resolventCore F z hz g) := by
    unfold sourceReserve
    dsimp only
    have hg:=SourceScalarVirialBulk.original_gauge_kinetic_nonnegative
      (inverseRootAction (thetaAction m ell (resolventCore F z hz g)))
    have ha:0 ≤ 27*coefficientCost sharp/(4*sourceTime 0):=by positivity
    have hv:0 ≤ (3/8:ℝ)*coefficientCost sharp*‖vacuum‖^2+(3/2:ℝ)*sourceMu^2:=by positivity
    nlinarith only [mul_nonneg ha hg,mul_nonneg hv (sq_nonneg ‖embed (thetaAction m ell (resolventCore F z hz g))‖)]
  have hcoef: (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*(sourceTime 0/256)*
      (32*phaseCoefficient^2)=3*coefficientCost sharp*phaseCoefficient/(128*sourceMu) := by
    unfold bulkCoefficient
    field_simp [hn.ne',hmu.ne',hc.ne']
    ring
  rw [←mul_assoc,hcoef]
  have hb:=actual_phase_coefficient_reserve_bound
  have hcb:3*coefficientCost sharp*phaseCoefficient/(128*sourceMu) ≤
      (1/4:ℝ)*(2/sourceMu)*((3/4:ℝ)*coefficientCost sharp) := by
    apply (div_le_iff₀ (show 0<128*sourceMu by positivity)).mpr
    field_simp [hmu.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hb hcost]
  exact (mul_le_mul_of_nonneg_right hcb he).trans
    (by convert mul_le_mul_of_nonneg_left hS (show 0 ≤ (1/4:ℝ)*(2/sourceMu) by positivity) using 1; ring)

def readerInput(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest:=
  volumeAction (localizedPressureReader m ell F z hz g)

def readerForcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest:=
  let k:=localizedPressureReader m ell F z hz g
  volumeAction (nonmagneticSecondField (thetaAction m ell (resolventCore F z hz g)))+
    (diagonalAction*volumeAction-volumeAction*diagonalAction) k+
    volumeAction (defectAction F k)

/-- The actual reader enters the original H0 Noether law with its generated
volume commutator and whole Own forcing, not a supplied equation. -/
theorem actual_reader_full_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    diagonalAction (readerInput m ell F z hz g)=readerForcing m ell F z hz g+
      star z • readerInput m ell F z hz g := by
  let k:=localizedPressureReader m ell F z hz g
  let w:=thetaAction m ell (resolventCore F z hz g)
  have hi:=(actual_original_cf_inverses F (star z) (star_nonreal z hz)).1
  have h:=LinearMap.congr_fun hi (nonmagneticSecondField w)
  change compressionCore F k-star z • k=nonmagneticSecondField w at h
  have he:diagonalAction k=nonmagneticSecondField w+defectAction F k+star z • k := by
    unfold defectAction
    simp only [LinearMap.sub_apply]
    linear_combination (norm:=module) h
  have hv:=congrArg volumeAction he
  simp only [map_add,map_smul] at hv
  unfold readerInput readerForcing
  change diagonalAction (volumeAction k)=volumeAction (nonmagneticSecondField w)+
    (diagonalAction*volumeAction-volumeAction*diagonalAction) k+volumeAction (defectAction F k)+
      star z • volumeAction k
  simp only [Module.End.mul_apply,LinearMap.sub_apply]
  linear_combination (norm:=module) hv

private theorem frequency_nonreal(advanced:Bool)(ω:ℝ):
    (actualFrequency advanced sourceMu ω).im≠0 := by
  have hmu:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large
  cases advanced <;> simpa [actualFrequency,SourceResolventBandLimit.line_im,Complex.star_def] using hmu.ne'
private theorem source_gap:2*sourceTime 0<sourceMu := by
  have hn:=n_positive
  have hl:sourceTime 0<1:=paid_local_native_gap% n_lt_one
  have hm:3<sourceMu:=by
    change 3<1+(2*Real.pi)^2
    nlinarith only [Real.pi_gt_three]
  linarith only [hl,hm]
private theorem reflected_frequency(advanced:Bool)(ω:ℝ):
    star (actualFrequency advanced sourceMu ω)=actualFrequency (!advanced) sourceMu ω := by
  cases advanced <;> simp [actualFrequency]

/-- Native reader inventory is paid by its original full-source scalar
current at the original damping and opposite resolvent orientation. -/
def nativeReaderWard(advanced:Bool)(ω:ℝ)(k:QuantumTest):ℝ:=
  inputScalarWardPrice (!advanced) (volumeAction k)
    (diagonalAction (volumeAction k)-star (actualFrequency advanced sourceMu ω) • volumeAction k)

theorem actual_native_reader_noether_payment(advanced:Bool)(ω:ℝ)(k:QuantumTest):
    (sourceTime 0)*nativeScalarEnergy k ≤
      nativeReaderWard advanced ω k/(4*(sourceMu-2*sourceTime 0)) := by
  have he:diagonalAction (volumeAction k)=
      (diagonalAction (volumeAction k)-star (actualFrequency advanced sourceMu ω) • volumeAction k)+
        actualFrequency (!advanced) sourceMu ω • volumeAction k := by
    rw [←reflected_frequency]
    abel
  have hs:=(actual_full_source_input_scalar_gap sourceMu source_gap (!advanced) ω
    (volumeAction k) _ he).1
  have hn:=n_positive
  have hg:0<sourceMu-2*sourceTime 0:=sub_pos.mpr source_gap
  have hp:4*sourceTime 0*nativeScalarEnergy k ≤ scalarEnergy (volumeAction k) := by
    unfold scalarEnergy
    rw [ActualWholeGammaPressureReturn.actual_reader_native_inventory]
    have hshift:0 ≤ shiftedMoment (volumeAction k):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    nlinarith only [mul_nonneg hn.le hshift]
  have hb:=mul_le_mul_of_nonneg_left hp hg.le
  unfold nativeReaderWard
  apply (le_div_iff₀ (show 0<4*(sourceMu-2*sourceTime 0) by positivity)).mpr
  nlinarith only [hs,hb]

theorem actual_reader_forcing_noether_return(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(ω:ℝ):
    nativeReaderWard advanced ω (localizedPressureReader m ell F
      (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g)=
      inputScalarWardPrice (!advanced)
        (readerInput m ell F (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g)
        (readerForcing m ell F (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g) := by
  unfold nativeReaderWard
  change inputScalarWardPrice (!advanced) (readerInput m ell F _ _ g)
    (diagonalAction (readerInput m ell F _ _ g)-
      star (actualFrequency advanced sourceMu ω) • readerInput m ell F _ _ g)=_
  rw [actual_reader_full_source]
  congr 1
  abel

/-- The moving reader's principal native part consumes one quarter of the
same original Reserve. Every residual reader is paid by a generated Noether
current, with no graph or reader-current hypothesis. -/
theorem actual_complete_reader_reserve_noether_payment(sharp advanced:Bool)(m ell:ℕ)
    (F:Index)(g:QuantumTest)(ω:ℝ):
    let z:=actualFrequency advanced sourceMu ω
    let hz:=frequency_nonreal advanced ω
    (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*(sourceTime 0/256)*
      nativeScalarEnergy (localizedPressureReader m ell F z hz g) ≤
      (1/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell (resolventCore F z hz g)+
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
        nativeReaderWard advanced ω (restReader m ell F z hz g)/(512*(sourceMu-2*sourceTime 0)) := by
  dsimp only
  have hc:=actual_phase_coefficient_positive
  have hm:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large
  have hn:=n_positive
  have ha:0 ≤ bulkCoefficient sharp:=by
    unfold bulkCoefficient
    exact div_nonneg (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity)
  have hfactor:0 ≤ (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*(sourceTime 0/256):=by positivity
  have hp:=mul_le_mul_of_nonneg_left (actual_reader_native_principal_price m ell F
    (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g) hfactor
  have hreserve:=actual_principal_reader_reserve_payment sharp m ell F
    (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g
  have hreader:=actual_native_reader_noether_payment advanced ω (restReader m ell F
    (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g)
  have hg:0<sourceMu-2*sourceTime 0:=sub_pos.mpr source_gap
  have hr:=mul_le_mul_of_nonneg_left hreader
    (show 0 ≤ (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))/128 by positivity)
  have hscale:(3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))/128*
      (nativeReaderWard advanced ω (restReader m ell F (actualFrequency advanced sourceMu ω)
        (frequency_nonreal advanced ω) g)/(4*(sourceMu-2*sourceTime 0)))=
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
        nativeReaderWard advanced ω (restReader m ell F (actualFrequency advanced sourceMu ω)
          (frequency_nonreal advanced ω) g)/(512*(sourceMu-2*sourceTime 0)) := by
    field_simp [hg.ne']
    ring
  rw [hscale] at hr
  nlinarith only [hp,hreserve,hr]

elab "paid_native_pressure%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWholeGammaPressureReturn 0) "LowEnergy") "ActualWholeGammaPressureReturn"
  mkConstWithFreshMVarLevels (Name.str ns "current_reduce")
private theorem pair_neg_right(f h:QuantumTest):sourcePair f (-h)= -sourcePair f h := by
  simp only [sourcePair,map_neg,inner_neg_right]

def fixedBalancedContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let Z:=R*ReverseScalarGaugeWard.balancedCompressionForce F*R
  sourcePair (thetaAction m ell (Z g)) (coreWindow m ell F z hz (nonmagneticSecondField g))+
    sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (Z (nonmagneticSecondField g)))

/-- The actual BF four orders are cancelled together before the localized
pressure invoice is consumed. Both fixed-input contacts remain complex. -/
theorem actual_ordered_balanced_pressure_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    (orderedForcing (ReverseScalarGaugeWard.balancedCompressionForce F) m ell F z hz g g).re=
      -12*balancedPressure m ell F z hz g+(fixedBalancedContact m ell F z hz g).re := by
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let S:=nonmagneticSecondField
  let Q:=ReverseScalarGaugeWard.balancedCompressionForce F
  let Z:=R*Q*R
  let T:=R*(C*S-S*C)*R
  have hT:T=S*R-R*S:=paid_native_pressure% S F z hz
  have hA:-(R*Q*T)-T*Q*R+R*(Q*S-S*Q)*R= -S*Z+Z*S := by
    rw [hT]
    dsimp only [Z]
    noncomm_ring
  have hp:=congrArg (fun A:End=>sourcePair (coreWindow m ell F z hz g)
    (thetaAction m ell (A g))) hA
  have ht:=congrArg (fun A:End=>sourcePair (thetaAction m ell (Z g))
    (thetaAction m ell (A g))) hT
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,map_add,map_sub,map_neg,
    (paid_phase_frequency% pair_add_right),
    (paid_phase_frequency% pair_sub_right),pair_neg_right] at hp
  simp only [LinearMap.sub_apply,map_sub,
    (paid_phase_frequency% pair_sub_right)] at ht
  have he:orderedForcing Q m ell F z hz g g=
      (0:ℂ)-sourcePair (thetaAction m ell (Z g)) (thetaAction m ell (S (R g)))-
      sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (S (Z g)))+
      fixedBalancedContact m ell F z hz g := by
    unfold orderedForcing fixedBalancedContact
    change (0:ℂ)-sourcePair (thetaAction m ell ((R*Q*R) g)) (thetaAction m ell (T g))-
      sourcePair (coreWindow m ell F z hz g) (thetaAction m ell ((R*Q*T) g))-
      sourcePair (coreWindow m ell F z hz g) (thetaAction m ell ((T*Q*R) g))+
      sourcePair (coreWindow m ell F z hz g) (thetaAction m ell ((R*(Q*S-S*Q)*R) g))=_
    simp only [LinearMap.neg_apply,map_neg,pair_neg_right,Module.End.mul_apply] at hp ht
    dsimp only [R,C,S,Q,Z,T] at hp ht ⊢
    simp only [coreWindow,Module.End.mul_apply] at hp ht ⊢
    linear_combination hp-ht
  rw [he]
  unfold balancedPressure
  dsimp only [R,C,S,Q,Z,T]
  simp only [Module.End.mul_apply,coreWindow,Complex.add_re,Complex.sub_re,Complex.zero_re]
  ring

/-- Phi, coframe, frequency and the two fixed Gauge legs form one source
invoice. Its BF contact is retained rather than assigned a free tail. -/
def sourceNativeInvoice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  4*(fieldFlux nonmagneticSecondField m ell F z hz g g).re+
    (fieldFlux nonmagneticSecondField m ell F z hz (Gauge g) g).re+
    (fieldFlux nonmagneticSecondField m ell F z hz g (Gauge g)).re+
    (1/4:ℝ)*(orderedForcing (deltaPhi (compressionCore F)) m ell F z hz g g).re-
    (1/2:ℝ)*(orderedForcing (scaleDerivative (compressionCore F)) m ell F z hz g g).re-
    (3/2:ℝ)*(orderedForcing (compressionCore F) m ell F z hz g g).re-
    (1/12:ℝ)*(fixedBalancedContact m ell F z hz g).re

theorem actual_whole_source_native_invoice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    (ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g).re=
      sourceNativeInvoice m ell F z hz g+balancedPressure m ell F z hz g := by
  have h:=congrArg Complex.re (actual_native_own_balanced_return m ell F z hz g)
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at h
  norm_num only [Complex.div_re,Complex.div_im,Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,Complex.one_re,Complex.one_im,zero_mul,mul_zero,zero_div,
    zero_add,add_zero,sub_zero] at h
  rw [actual_ordered_balanced_pressure_return] at h
  unfold sourceNativeInvoice
  linarith only [h]

/-- Whole source consumer: the original Reserve internally absorbs the
principal reader price and its complete remainder receives a source Noether
price. Native/Own work and localization contact remain one signed invoice. -/
theorem actual_whole_localized_native_work_lower(sharp advanced:Bool)(m ell:ℕ)(F:Index)
    (g:QuantumTest)(ω:ℝ):
    let z:=actualFrequency advanced sourceMu ω
    let hz:=frequency_nonreal advanced ω
    let w:=thetaAction m ell (resolventCore F z hz g)
    (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
      (ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g).re+
      (1/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell (resolventCore F z hz g) ≥
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
        (sourceNativeInvoice m ell F z hz g+
          retainedNativePrice w-clearedNativePrice w-compensatedPrimitiveWork F w+
          (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
          (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2+
          balancedLocalizationContact m ell F z hz g)-
        (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
          nativeReaderWard advanced ω (restReader m ell F z hz g)/(512*(sourceMu-2*sourceTime 0)) := by
  dsimp only
  rw [actual_whole_source_native_invoice]
  have hp:=actual_localized_balanced_pressure_small_gain m ell F
    (actualFrequency advanced sourceMu ω) (frequency_nonreal advanced ω) g
  dsimp only at hp
  have hc:=actual_phase_coefficient_positive
  have hm:0<sourceMu:=lt_of_lt_of_le (by norm_num) source_mu_large
  have hn:=n_positive
  have ha:0 ≤ bulkCoefficient sharp:=by
    unfold bulkCoefficient
    exact div_nonneg (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity)
  have hf:0 ≤ 3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient):=by positivity
  have hs:=mul_le_mul_of_nonneg_left hp hf
  have hb:=actual_complete_reader_reserve_noether_payment sharp advanced m ell F g ω
  dsimp only at hb
  nlinarith only [hs,hb]

end LowEnergy.ActualLocalizedNativeWorkReturn
