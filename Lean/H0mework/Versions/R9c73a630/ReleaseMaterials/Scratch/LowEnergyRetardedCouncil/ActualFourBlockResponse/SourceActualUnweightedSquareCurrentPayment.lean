import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBulkCurrentSquareReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseWardIntertwiner
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeContactWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualUnweightedSquareCurrentPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourceQuantumScalarChart
open SourcePhysicalKineticSquare SourceScalarInverseEnergyExchange SourceInverseVolumeContact
open SourceInverseContactHardy SourceInverseNoetherEnergy
open SourceScalarPairedTransport SourceNativeCutoffContact SourceScalarInverseNativeEnergy
open SourceInverseFixedEnergyTail SourceScalarInverseBulk SourceRetardedGraph
open SourceClockYukawaCubicCurrent SourceJointResidualEnergy SourceResolventBandLimit
open ActualBulkCurrentSquareReturn ActualPhaseWardIntertwiner ActualScalarPhaseJet ActualPhaseBulkSquare
open ActualTwoResolventCascade ActualVectorJointCost FullYSourceResolventGraphSplice MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
elab "paid_unweighted_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawFrequencyBalance 0) "LowEnergy")
    "ActualExactSylvesterRawFrequencyBalance"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_unweighted_theta_pair%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade 0) "LowEnergy") "ActualTwoResolventCascade") "theta_pair")
private theorem mu_positive : 0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large
private theorem causal_nonreal (advanced:Bool)(w:ℝ):(causalFrequency advanced sourceMu w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using mu_positive.ne'
private def causalCore(advanced:Bool)(F:Index)(g:QuantumTest)(w:ℝ):QuantumTest :=
  resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced w) g

/-- This operator is the entire actual source inverse Ward crossed through the
phase jet, including its forced Phi shift and the three coframe derivatives. -/
def shiftedSquare : End := phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction))
def shiftedResponse(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  let q:=thetaAction m ell (causalCore advanced F g w)
  sourcePair q (shiftedSquare q)
def shiftedSeed(m ell:ℕ)(g:QuantumTest):ℝ :=
  (sourcePair (thetaAction m ell g) (shiftedSquare (thetaAction m ell g))).re
attribute [local irreducible] sourcePair compressionCore resolventCore thetaAction
  shiftedSquare phaseSecond phaseForce phaseCoefficient phaseHamiltonianSquare
  inverseWeightedBulkJet shiftedInverseWard diagonalAction

private theorem actual_shifted_source : inverseWeightedBulkJet phaseHamiltonianSquare=shiftedSquare := by
  unfold phaseHamiltonianSquare shiftedSquare
  exact actual_source_inverse_ward_phase_shift _
private theorem source_response(m ell:ℕ)(f:QuantumTest):
    sourcePair f ((thetaAction m ell*inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell) f)=
      sourcePair (thetaAction m ell f) (shiftedSquare (thetaAction m ell f)) := by
  simp only [Module.End.mul_apply]
  rw [(paid_unweighted_theta_pair%) m ell f,actual_shifted_source]

/-- Integrability is paid on the actual CF finite spectral orbit, including
its zero escape channel; no boundedness of the unweighted H0 square is needed. -/
theorem actual_shifted_response_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (shiftedResponse advanced m ell F g) := by
  have h:=(paid_unweighted_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    (thetaAction m ell*inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell) g
  exact h.congr (Filter.Eventually.of_forall (fun _=>source_response m ell _))

theorem actual_square_current_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (squareWardCurrent advanced m ell F g) := by
  let T:=thetaAction m ell*inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell
  have h:=((paid_unweighted_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    ((Complex.I*(causalSign advanced:ℂ)) • (compressionCore F*T-T*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _=>rfl))

/-- The whole original CF commutator returns to the shifted source response.
No cofinal replacement of CF by H0 is made. -/
theorem actual_square_current_shifted_balance(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    (∫w:ℝ,squareWardCurrent advanced m ell F g w)=
      2*sourceMu*(∫w:ℝ,(shiftedResponse advanced m ell F g w).re)-2*Real.pi*shiftedSeed m ell g := by
  let T:=thetaAction m ell*inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell
  have h:=ActualExactSylvesterRawFrequencyBalance.actual_core_lyapunov_frequency_balance
    advanced F sourceMu mu_positive T g
  have he:=congrArg Complex.re h.2
  have hir:=integral_re h.1
  simp only [RCLike.re_to_complex] at hir
  rw [←hir] at he
  have hp(w:ℝ):(sourcePair (causalCore advanced F g w)
      ((paid_unweighted_frequency% frequencyLyapunov) advanced F sourceMu T (causalCore advanced F g w))).re=
      2*sourceMu*(shiftedResponse advanced m ell F g w).re-squareWardCurrent advanced m ell F g w := by
    let q:=causalCore advanced F g w
    change (sourcePair q (((2*(sourceMu:ℂ)) • T-
      (Complex.I*(causalSign advanced:ℂ)) • (compressionCore F*T-T*compressionCore F)) q)).re=_
    simp only [LinearMap.sub_apply,LinearMap.smul_apply]
    have hs(x y:QuantumTest):sourcePair q (x-y)=sourcePair q x-sourcePair q y := by
      simp only [sourcePair,map_sub,inner_sub_right]
    have hc(c:ℂ)(x:QuantumTest):sourcePair q (c • x)=c*sourcePair q x := by
      simp only [sourcePair,map_smul,inner_smul_right]
    rw [hs,hc,Complex.sub_re]
    change ((2*(sourceMu:ℂ))*sourcePair q (T q)).re-squareWardCurrent advanced m ell F g w=_
    norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]
    rw [source_response]
    rfl
  change (∫w:ℝ,(sourcePair (causalCore advanced F g w)
    ((paid_unweighted_frequency% frequencyLyapunov) advanced F sourceMu T (causalCore advanced F g w))).re)=
    (2*(Real.pi:ℂ)*sourcePair g (T g)).re at he
  simp_rw [hp] at he
  have hi:Integrable (fun w:ℝ=>(shiftedResponse advanced m ell F g w).re):=
    (actual_shifted_response_integrable advanced m ell F g).re
  rw [integral_sub (hi.const_mul (2*sourceMu)) (actual_square_current_integrable advanced m ell F g),
    integral_const_mul] at he
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero] at he
  rw [source_response] at he
  change _=2*Real.pi*shiftedSeed m ell g at he
  linarith only [he]

/-- The original force-square return pays the entire fixed shifted Ward seed. -/
theorem actual_shifted_seed_source(m ell:ℕ)(g:QuantumTest):
    shiftedSeed m ell g= -2*phaseCoefficient*inverseForm (thetaAction m ell g)-
      16*‖embed (phaseForce (thetaAction m ell g))‖^2 := by
  have h:=actual_inverse_form_shifted_source_square (thetaAction m ell g)
  have hc:=actual_phase_coefficient_positive
  have hs : shiftedSeed m ell g=(sourcePair (thetaAction m ell g)
      (phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction)) (thetaAction m ell g))).re := by
    unfold shiftedSeed shiftedSquare
    rfl
  rw [←hs] at h
  field_simp at h
  nlinarith only [h]

/-- Both source components of the fixed seed vanish with the same original
cutoff; the response square is not assumed small. -/
theorem actual_shifted_seed_tail(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell → |shiftedSeed m ell g|  ≤  ε := by
  intro ε hε
  let δ:=ε/(2*phaseCoefficient+16)
  have hc:=actual_phase_coefficient_positive
  have hd:0<δ:=by dsimp only [δ];positivity
  obtain ⟨N1,h1⟩:=original_fixed_energy_tail g δ hd
  obtain ⟨N2,h2⟩:=actual_fixed_phase_force_cutoff_tail g δ hd
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  have hi:=h1 m (by omega) ell hml
  have hf:=h2 m (by omega) ell hml
  have hp:=original_inverse_nonnegative (thetaAction m ell g)
  rw [actual_shifted_seed_source]
  rw [abs_of_nonpos (by nlinarith only [hc,hp,sq_nonneg ‖embed (phaseForce (thetaAction m ell g))‖])]
  have he:(2*phaseCoefficient+16)*δ=ε:=by dsimp only [δ];field_simp
  nlinarith only [hi,hf,hc,he]


elab "paid_unweighted_inverse%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard 0) "LowEnergy") "ActualMixedResolventWard"
  mkConstWithFreshMVarLevels (Name.str ns "actual_inverse")

private theorem actual_compression_frequency(advanced:Bool)(F:Index)(g:QuantumTest)(w:ℝ):
    compressionCore F (causalCore advanced F g w)=g+
      causalFrequency advanced sourceMu w • causalCore advanced F g w := by
  have h:=((paid_unweighted_inverse%) F (causalFrequency advanced sourceMu w) (causal_nonreal advanced w)).2
  have he:=LinearMap.congr_fun h g
  change compressionCore F (causalCore advanced F g w)-
    causalFrequency advanced sourceMu w • causalCore advanced F g w=g at he
  exact sub_eq_iff_eq_add.mp he

/-- These are the two ordered original source-forcing legs. They are retained
as a coherent difference rather than separately assigned frequency budgets. -/
def sourceForcing(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  let q:=thetaAction m ell (causalCore advanced F g w)
  let t:=thetaAction m ell g
  (Complex.I*(causalSign advanced:ℂ))*(sourcePair t (shiftedSquare q)-sourcePair q (shiftedSquare t))

/-- The exact ALL-F CF equation pays the complete commutator, including its
H0-square OwnDefect, by two ordered fixed-source forcing legs and one response. -/
theorem actual_square_current_source_forcing(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    squareWardCurrent advanced m ell F g w=
      2*sourceMu*(shiftedResponse advanced m ell F g w).re+(sourceForcing advanced m ell F g w).re := by
  let q:=causalCore advanced F g w
  let T:=thetaAction m ell*inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell
  have hCF:=actual_compression_frequency advanced F g w
  have hc:sourcePair q (compressionCore F (T q))=sourcePair (compressionCore F q) (T q):=
    (paid_unweighted_frequency% compression_pair) F q (T q)
  have hleft:sourcePair g (T q)=sourcePair (thetaAction m ell g) (shiftedSquare (thetaAction m ell q)) := by
    simp only [T,Module.End.mul_apply]
    rw [(paid_unweighted_theta_pair%) m ell g,actual_shifted_source]
  have hright:sourcePair q (T g)=sourcePair (thetaAction m ell q) (shiftedSquare (thetaAction m ell g)) := by
    simp only [T,Module.End.mul_apply]
    rw [(paid_unweighted_theta_pair%) m ell q,actual_shifted_source]
  have hr:sourcePair q (T q)=shiftedResponse advanced m ell F g w := source_response m ell q
  have hs:(Complex.I*(causalSign advanced:ℂ))*(star (causalFrequency advanced sourceMu w)-
      causalFrequency advanced sourceMu w)=2*(sourceMu:ℂ) := by
    cases advanced <;> simp [causalFrequency,ActualTwoResolventCascade.causalSign,
      SourceResolventBandLimit.line,Complex.conj_ofReal,Complex.conj_I] <;> ring_nf <;> norm_num [Complex.I_sq]
  have he:sourcePair q (((Complex.I*(causalSign advanced:ℂ)) •
      (compressionCore F*T-T*compressionCore F)) q)=
      (2*(sourceMu:ℂ))*shiftedResponse advanced m ell F g w+sourceForcing advanced m ell F g w := by
    simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply]
    have psub(x y:QuantumTest):sourcePair q (x-y)=sourcePair q x-sourcePair q y := by
      simp only [sourcePair,map_sub,inner_sub_right]
    have psmul(c:ℂ)(x:QuantumTest):sourcePair q (c • x)=c*sourcePair q x := by
      simp only [sourcePair,map_smul,inner_smul_right]
    rw [psmul,psub,hc,hCF]
    simp only [map_add,map_smul]
    have pa(x y v:QuantumTest):sourcePair (x+y) v=sourcePair x v+sourcePair y v := by
      simp only [sourcePair,map_add,inner_add_left]
    have pl(c:ℂ)(x v:QuantumTest):sourcePair (c • x) v=star c*sourcePair x v := by
      simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
    have pr(x y:QuantumTest):sourcePair q (x+y)=sourcePair q x+sourcePair q y := by
      simp only [sourcePair,map_add,inner_add_right]
    rw [pa,pl,pr,psmul,hr,hleft,hright]
    unfold sourceForcing
    change _=(2*(sourceMu:ℂ))*shiftedResponse advanced m ell F g w+
      (Complex.I*(causalSign advanced:ℂ))*(sourcePair (thetaAction m ell g)
        (shiftedSquare (thetaAction m ell q))-sourcePair (thetaAction m ell q) (shiftedSquare (thetaAction m ell g)))
    linear_combination (norm:=ring) hs*shiftedResponse advanced m ell F g w
  have h:=congrArg Complex.re he
  norm_num only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero] at h
  exact h

/-- The entire ordered forcing integral is the fixed source boundary; escape
and the same cause are already included in the actual spectral payment. -/
theorem actual_source_forcing_integral(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>(sourceForcing advanced m ell F g w).re) ∧
    (∫w:ℝ,(sourceForcing advanced m ell F g w).re)= -2*Real.pi*shiftedSeed m ell g := by
  have hr:Integrable (fun w:ℝ=>(shiftedResponse advanced m ell F g w).re):=
    (actual_shifted_response_integrable advanced m ell F g).re
  have he(w:ℝ):(sourceForcing advanced m ell F g w).re=squareWardCurrent advanced m ell F g w-
      2*sourceMu*(shiftedResponse advanced m ell F g w).re := by
    linarith only [actual_square_current_source_forcing advanced m ell F g w]
  simp_rw [he]
  constructor
  · exact (actual_square_current_integrable advanced m ell F g).sub (hr.const_mul _)
  · rw [integral_sub (actual_square_current_integrable advanced m ell F g) (hr.const_mul _),integral_const_mul,
      actual_square_current_shifted_balance]
    ring

/-- The coherent forcing debt vanishes without assigning either ordered leg
an absolute tail. This uses only the original fixed seed source payment. -/
theorem actual_source_forcing_tail(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N  ≤  m → ∀ ell, m  ≤  ell → ∀ F : Index, ∀ advanced : Bool,
      |∫w:ℝ,(sourceForcing advanced m ell F g w).re| ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_shifted_seed_tail g (ε/(2*Real.pi)) (by positivity)
  refine ⟨N,fun m hm ell hml F advanced=>?_⟩
  rw [(actual_source_forcing_integral advanced m ell F g).2,abs_mul]
  have hpi:0<Real.pi:=Real.pi_pos
  rw [abs_mul,abs_of_nonpos (by norm_num : (-2:ℝ) ≤ 0),abs_of_nonneg hpi.le]
  norm_num only [neg_neg]
  have he:2*Real.pi*(ε/(2*Real.pi))=ε:=by field_simp
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hml) (by positivity)).trans_eq he


/-- The actual price now consumes the shifted source pair directly. Its fixed
boundary is favorable by the original negative-square identity; neither
ordered CF forcing leg nor a caller current budget remains in this return. -/
theorem actual_raw_shifted_square_paid_return(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m,N  ≤  m → ∀ ell,m  ≤  ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced sharp : Bool,
      (∫w:ℝ,ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual advanced sharp m ell F g w)-
        (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
          (∫w:ℝ,(shiftedResponse advanced m ell F g w).re)  ≥
      Real.pi*sourceQ sharp m ell g+(2/sourceMu)*
        (∫w:ℝ,ActualRawResidualTailPayment.reserveFrequency advanced sharp m ell F g w)+
      2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
        (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2+
      (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*(∫w:ℝ,forceResponse advanced m ell F g w)-ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_raw_unweighted_square_paid_return g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced sharp
  have hc:=actual_phase_coefficient_positive
  have ha:0 ≤ bulkCoefficient sharp:=by
    unfold bulkCoefficient
    have hn:0<sourceTime 0:=by
      rw [source_time_generated]
      exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
    exact div_nonneg (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by positivity)
  have hs:shiftedSeed m ell g ≤ 0:=by
    rw [actual_shifted_seed_source]
    have hi:=original_inverse_nonnegative (thetaAction m ell g)
    nlinarith only [hc,hi,sq_nonneg ‖embed (phaseForce (thetaAction m ell g))‖]
  have hneg:(2*Real.pi*(3*bulkCoefficient sharp/(4*phaseCoefficient)))*shiftedSeed m ell g ≤ 0:=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hs
  have hp:=hF advanced sharp
  rw [actual_square_current_shifted_balance] at hp
  have hexp:(3*bulkCoefficient sharp/(4*phaseCoefficient))*(2*sourceMu*
      (∫w:ℝ,(shiftedResponse advanced m ell F g w).re)-2*Real.pi*shiftedSeed m ell g)=
      (3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient))*
        (∫w:ℝ,(shiftedResponse advanced m ell F g w).re)-
      (2*Real.pi*(3*bulkCoefficient sharp/(4*phaseCoefficient)))*shiftedSeed m ell g := by ring
  rw [hexp] at hp
  linarith only [hp,hneg]


private theorem theta_inverse(m ell:ℕ)(f:QuantumTest):
    inverseVolumeAction (thetaAction m ell f)=thetaAction m ell (inverseVolumeAction f) := by
  unfold thetaAction
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z:ℂ) • ((SourceNativeCutoffContact.theta m ell z:ℂ) • f z)=
    (SourceNativeCutoffContact.theta m ell z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
  exact smul_comm _ _ _
private theorem theta_contact(v:GaussLiveMomentum.Ambient)(m ell:ℕ)(f:QuantumTest):
    contactAction v m ell (thetaAction m ell f)=thetaAction m ell (contactAction v m ell f) := by
  unfold thetaAction
  apply DFunLike.ext
  intro z
  change (-Complex.I*(thetaDerivative v m ell z:ℂ)) • ((SourceNativeCutoffContact.theta m ell z:ℂ) • f z)=
    (SourceNativeCutoffContact.theta m ell z:ℂ) • ((-Complex.I*(thetaDerivative v m ell z:ℂ)) • f z)
  exact smul_comm _ _ _

def phaseCutoffContact(m ell:ℕ):End := phaseForce*thetaAction m ell-thetaAction m ell*phaseForce
private theorem phase_contact_source(m ell:ℕ)(f:QuantumTest):
    phaseCutoffContact m ell f=((sourceTime 0:ℂ)^2) • ∑a:ScalarIndex,
      (inner ℝ (scalarBasis a) vacuum:ℂ) • contactAction (scalarDirection a) m ell (inverseVolumeAction f) := by
  unfold phaseCutoffContact
  simp only [LinearMap.sub_apply,Module.End.mul_apply]
  rw [actual_phase_force_cutoff_contact]
  abel
private theorem phase_contact_theta(m ell:ℕ)(f:QuantumTest):
    phaseCutoffContact m ell (thetaAction m ell f)=thetaAction m ell (phaseCutoffContact m ell f) := by
  rw [phase_contact_source,phase_contact_source]
  simp only [map_smul,map_sum,theta_inverse,theta_contact]

private theorem weighted_vector_square{ι:Type*}[Fintype ι](c:ι→ℝ)(v:ι→H):
    ‖∑i:ι,(c i:ℂ) • v i‖^2 ≤ (∑i:ι,(c i)^2)*(∑i:ι,‖v i‖^2) := by
  classical
  have h:‖∑i:ι,(c i:ℂ) • v i‖ ≤ ∑i:ι,|c i| *‖v i‖:=by
    simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i=>(c i:ℂ) • v i)
  have hp:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>|c i|) (fun i=>‖v i‖)
  simp only [sq_abs] at hp
  have hn:0 ≤ ∑i:ι,|c i| *‖v i‖:=Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (norm_nonneg _))
  nlinarith only [h,hp,hn,norm_nonneg (∑i:ι,(c i:ℂ) • v i)]

/-- The literal source vacuum direction contracts all seventy contacts by
Bessel on the original scalar basis, before the inverse weight is estimated. -/
theorem actual_phase_contact_inverse_price(m ell:ℕ)(f:QuantumTest):
    16*‖embed (phaseCutoffContact m ell f)‖^2 ≤ 4*phaseCoefficient*(inverseContact m ell f f).re := by
  have hb: (∑a:ScalarIndex,(inner ℝ (scalarBasis a) vacuum)^2) ≤ ‖vacuum‖^2:=by
    have h:=scalarBasis.orthonormal.sum_inner_products_le (s:=Finset.univ) vacuum
    simpa only [Real.norm_eq_abs,sq_abs] using h
  have hp:=weighted_vector_square (fun a:ScalarIndex=>inner ℝ (scalarBasis a) vacuum)
    (fun a=>embed (contactAction (scalarDirection a) m ell (inverseVolumeAction f)))
  have hmul:=mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_right hb
    (Finset.sum_nonneg (fun a _=>sq_nonneg _)))) (sq_nonneg ((sourceTime 0)^2))
  rw [phase_contact_source,map_smul,map_sum,norm_smul,mul_pow,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs]
  have he:=inverse_contact_real m ell f
  have hc:phaseCoefficient=(sourceTime 0)^3*‖vacuum‖^2:=by unfold phaseCoefficient;rfl
  have hcomm(a:ScalarIndex):contactAction (scalarDirection a) m ell (inverseVolumeAction f)=
      inverseVolumeAction (contactAction (scalarDirection a) m ell f):=
    (original_inverse_contact_commute _ m ell f).symm
  simp_rw [hcomm] at hmul
  rw [he,hc]
  simp only [map_smul,hcomm]
  nlinarith only [hmul]

private theorem phase_force_ims(m ell:ℕ)(f:QuantumTest):
    (sourcePair (thetaAction m ell f) ((phaseForce*phaseForce) (thetaAction m ell f))).re-
      (sourcePair (thetaAction m ell (thetaAction m ell f)) ((phaseForce*phaseForce) f)).re=
      ‖embed (phaseCutoffContact m ell f)‖^2 := by
  let T:=thetaAction m ell
  let H1:=phaseForce
  let K:=phaseCutoffContact m ell
  have h1(q:QuantumTest):H1 (T q)=T (H1 q)+K q:=by
    dsimp only [H1,T,K,phaseCutoffContact]
    simp only [LinearMap.sub_apply,Module.End.mul_apply]
    abel
  have h2:H1 (T (T f))=T (T (H1 f))+(2:ℂ) • T (K f):=by
    rw [h1,h1,phase_contact_theta]
    simp only [map_add]
    module
  have hp:sourcePair (T f) ((H1*H1) (T f))=sourcePair (H1 (T f)) (H1 (T f)):=
    actual_phase_force_pair (T f) (H1 (T f))
  have hq:sourcePair (T (T f)) ((H1*H1) f)=sourcePair (H1 (T (T f))) (H1 f):=
    actual_phase_force_pair (T (T f)) (H1 f)
  have hdiag:sourcePair (T (H1 f)) (T (H1 f))=sourcePair (T (T (H1 f))) (H1 f):=
    (paid_unweighted_theta_pair%) m ell (T (H1 f)) (H1 f)
  have hcross:sourcePair (T (K f)) (H1 f)=sourcePair (K f) (T (H1 f)):=
    ((paid_unweighted_theta_pair%) m ell (K f) (H1 f)).symm
  have hsym:(sourcePair (T (H1 f)) (K f)).re=(sourcePair (K f) (T (H1 f))).re:=by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  change (sourcePair (T f) ((H1*H1) (T f))).re-(sourcePair (T (T f)) ((H1*H1) f)).re=_
  rw [hp,hq,h1,h2]
  have padd(x y z:QuantumTest):sourcePair (x+y) z=sourcePair x z+sourcePair y z:=by
    simp only [sourcePair,map_add,inner_add_left]
  have paddr(x y z:QuantumTest):sourcePair x (y+z)=sourcePair x y+sourcePair x z:=by
    simp only [sourcePair,map_add,inner_add_right]
  have psmul(x z:QuantumTest):sourcePair ((2:ℂ) • x) z=(2:ℂ)*sourcePair x z:=by
    simp only [sourcePair,map_smul,inner_smul_left,star_ofNat,starRingEnd_apply]
  simp only [padd,paddr,psmul,hdiag,hcross,Complex.add_re]
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  have hself:(sourcePair (K f) (K f)).re=‖embed (K f)‖^2:=by
    unfold sourcePair
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed (K f))
  rw [hself]
  linarith only [hsym]

private theorem shifted_square_negative:
    shiftedSquare=(-2*(phaseCoefficient:ℂ)) • bulkAction+(-16:ℂ) • (phaseForce*phaseForce) := by
  have h:=actual_source_bulk_phase_negative_square
  rw [actual_shifted_source] at h
  have he:=congrArg (fun A:End=>(-2*(phaseCoefficient:ℂ)) • A) h
  simp only [smul_add,smul_smul] at he
  have hc: (phaseCoefficient:ℂ)≠0:=Complex.ofReal_ne_zero.mpr actual_phase_coefficient_positive.ne'
  have h1:(-2*(phaseCoefficient:ℂ))*(-(2*(phaseCoefficient:ℂ))⁻¹)=1:=by field_simp
  have h2:(-2*(phaseCoefficient:ℂ))*(-8*(phaseCoefficient:ℂ)⁻¹)=16:=by field_simp;norm_num
  rw [h1,h2,one_smul] at he
  linear_combination (norm:=module) -he

/-- This is the whole radial slot, with the actual B on the right of theta.
No theta/B commutation or scalar-only source replacement is made. -/
def radialSlot(m ell:ℕ)(f:QuantumTest):ℝ :=
  (sourcePair (thetaAction m ell f) (shiftedSquare (thetaAction m ell f))).re-
    (sourcePair (thetaAction m ell (thetaAction m ell f)) (shiftedSquare f)).re

/-- The whole radial commutator is exactly a negative sum of the original
Native70 inverse contacts and the source phase-force contact square. -/
theorem actual_radial_slot_source(m ell:ℕ)(f:QuantumTest):
    radialSlot m ell f= -2*phaseCoefficient*(inverseContact m ell f f).re-
      16*‖embed (phaseCutoffContact m ell f)‖^2 := by
  have hbulk:=original_fixed_energy_ims m ell f
  rw [←original_bulk_energy] at hbulk
  simp only [SourceScalarInverseRetardedBudget.square,SourceScalarInverseRetardedBudget.theta,Module.End.mul_apply] at hbulk
  change (sourcePair (thetaAction m ell f) (bulkAction (thetaAction m ell f))).re=
    (sourcePair (thetaAction m ell (thetaAction m ell f)) (bulkAction f)).re+(inverseContact m ell f f).re at hbulk
  have hf:=phase_force_ims m ell f
  unfold radialSlot
  rw [shifted_square_negative]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right,Complex.add_re]
  have hn2:-2*(phaseCoefficient:ℂ)=((-2*phaseCoefficient:ℝ):ℂ):=by push_cast;rfl
  have hn16:(-16:ℂ)=((-16:ℝ):ℂ):=by norm_num
  rw [hn2,hn16]
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [sourcePair] at hbulk hf
  linear_combination (norm:=ring) (-2*phaseCoefficient)*hbulk-16*hf

/-- The exact source radial slot has a strict small inverse-form price. -/
theorem actual_radial_slot_self_price(m ell:ℕ)(f:QuantumTest):
    |radialSlot m ell f|/(2*phaseCoefficient) ≤ (12/3481:ℝ)*inverseForm f := by
  have hc:=actual_phase_coefficient_positive
  have hi:=inverse_contact_real m ell f
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hip:0 ≤ (inverseContact m ell f f).re:=by rw [hi];positivity
  have hs:=actual_phase_contact_inverse_price m ell f
  have hb:=original_inverse_contact_form_bound m ell f
  change 4*sourceTime 0*(∑a:ScalarIndex,‖embed (inverseVolumeAction (contactAction (scalarDirection a) m ell f))‖^2) ≤ _ at hb
  rw [←hi] at hb
  rw [actual_radial_slot_source,abs_of_nonpos (by nlinarith only [hc,hip,sq_nonneg ‖embed (phaseCutoffContact m ell f)‖])]
  apply (div_le_iff₀ (by positivity:0<2*phaseCoefficient)).mpr
  nlinarith only [hs,hb,hc]

/-- The complete radial correction is paid by the two actual half windows,
with a source-generated factor 216/3481 below 1/16. -/
theorem actual_radial_slot_window_price(m ell:ℕ)(hm:1 ≤ m)(hell:m ≤ ell)(f:QuantumTest):
    |radialSlot m ell f|/(2*phaseCoefficient) ≤ (216/3481:ℝ)*
      (inverseForm (thetaAction (m/2) m f)+inverseForm (thetaAction (ell/2) ell f)) := by
  have hc:=actual_phase_coefficient_positive
  have hi:=inverse_contact_real m ell f
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hip:0 ≤ (inverseContact m ell f f).re:=by rw [hi];positivity
  have hs:=actual_phase_contact_inverse_price m ell f
  have hb:=original_inverse_ims_window m ell hm hell f
  rw [actual_radial_slot_source,abs_of_nonpos (by nlinarith only [hc,hip,sq_nonneg ‖embed (phaseCutoffContact m ell f)‖])]
  apply (div_le_iff₀ (by positivity:0<2*phaseCoefficient)).mpr
  nlinarith only [hs,hb,hc]


/-- The paid radial difference is exactly the original whole B/theta commutator. -/
theorem actual_radial_slot_commutator(m ell:ℕ)(f:QuantumTest):
    radialSlot m ell f=(sourcePair (thetaAction m ell f)
      ((shiftedSquare*thetaAction m ell-thetaAction m ell*shiftedSquare) f)).re := by
  unfold radialSlot
  simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right,Complex.sub_re]
  have hp:sourcePair (thetaAction m ell f) (thetaAction m ell (shiftedSquare f))=
    sourcePair (thetaAction m ell (thetaAction m ell f)) (shiftedSquare f):=
    (paid_unweighted_theta_pair%) m ell (thetaAction m ell f) (shiftedSquare f)
  simp only [sourcePair] at hp
  rw [hp]

private theorem radial_pair_source(m ell:ℕ)(f:QuantumTest):
    (sourcePair f ((thetaAction m ell*shiftedSquare*thetaAction m ell-
      thetaAction m ell*thetaAction m ell*shiftedSquare) f)).re=radialSlot m ell f := by
  have hs(x y:QuantumTest):sourcePair f (x-y)=sourcePair f x-sourcePair f y:=by
    simp only [sourcePair,map_sub,inner_sub_right]
  simp only [LinearMap.sub_apply,Module.End.mul_apply]
  rw [hs,Complex.sub_re,(paid_unweighted_theta_pair%) m ell f,
    (paid_unweighted_theta_pair%) m ell f,(paid_unweighted_theta_pair%) m ell (thetaAction m ell f)]
  rfl

private theorem inverse_cutoff_pair(a b:ℕ)(f:QuantumTest):
    (sourcePair f ((thetaAction a b*bulkAction*thetaAction a b) f)).re=
      inverseForm (thetaAction a b f) := by
  simp only [Module.End.mul_apply]
  rw [(paid_unweighted_theta_pair%) a b f,original_bulk_energy]

private theorem inverse_cutoff_integrable(advanced:Bool)(a b:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>inverseForm (thetaAction a b (causalCore advanced F g w))) := by
  have h:=((paid_unweighted_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    (thetaAction a b*bulkAction*thetaAction a b) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _=>inverse_cutoff_pair a b _))

theorem actual_radial_slot_causal_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>radialSlot m ell (causalCore advanced F g w)) := by
  have h:=((paid_unweighted_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    (thetaAction m ell*shiftedSquare*thetaAction m ell-
      thetaAction m ell*thetaAction m ell*shiftedSquare) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _=>radial_pair_source m ell _))

/-- The whole moving radial commutator has an internally paid absolute L1
price on both original causal lines. The only price is the two actual half
windows, with a strict coefficient below 1/16; no vector or current budget
is supplied by the caller. -/
theorem actual_radial_slot_causal_window_price(advanced:Bool)(m ell:ℕ)(hm:1 ≤ m)(hell:m ≤ ell)
    (F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>radialSlot m ell (causalCore advanced F g w)) ∧
    (∫w:ℝ,|radialSlot m ell (causalCore advanced F g w)|)/(2*phaseCoefficient) ≤
      (216/3481:ℝ)*((∫w:ℝ,inverseForm (thetaAction (m/2) m (causalCore advanced F g w)))+
        (∫w:ℝ,inverseForm (thetaAction (ell/2) ell (causalCore advanced F g w)))) := by
  have hr:=actual_radial_slot_causal_integrable advanced m ell F g
  have h1:=inverse_cutoff_integrable advanced (m/2) m F g
  have h2:=inverse_cutoff_integrable advanced (ell/2) ell F g
  refine ⟨hr,?_⟩
  have hp:=integral_mono (hr.abs.div_const (2*phaseCoefficient))
    ((h1.add h2).const_mul (216/3481:ℝ))
    (fun w:ℝ=>actual_radial_slot_window_price m ell hm hell (causalCore advanced F g w))
  simp only [Pi.add_apply] at hp
  rw [integral_div,integral_const_mul,integral_add h1 h2] at hp
  exact hp

end LowEnergy.ActualUnweightedSquareCurrentPayment
