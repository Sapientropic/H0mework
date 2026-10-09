import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRawResidualTailPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseBulkSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.ActualBulkCurrentSquareReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy GaussNativePotential SourceQuantumScalarChart
open SourcePhysicalKineticSquare SourceScalarShiftedBulk SourceScalarInverseNativeEnergy
open SourceNativeCutoffContact SourceHardyRetardedTail SourceCutoffDilationWard
open SourceScalarPairedTransport SourceRetardedGraph ActualPhaseBulkSquare ActualScalarPhaseJet
open ActualTwoResolventCascade ActualRawResidualTailPayment ActualVectorJointCost
open SourceJointResidualEnergy SourceResolventBandLimit FullYSourceResolventGraphSplice MeasureTheory Filter
open Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem inverse_theta (m ell : ℕ) (f : QuantumTest) :
    inverseVolumeAction (thetaAction m ell f)=thetaAction m ell (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z : ℂ) • ((theta m ell z : ℂ) • f z)=
    (theta m ell z : ℂ) • ((reciprocalVolume z : ℂ) • f z)
  exact smul_comm _ _ _

private theorem inverse_contact (v : GaussLiveMomentum.Ambient) (m ell : ℕ) (f : QuantumTest) :
    inverseVolumeAction (contactAction v m ell f)=contactAction v m ell (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z : ℂ) • ((-Complex.I*(thetaDerivative v m ell z : ℂ)) • f z)=
    (-Complex.I*(thetaDerivative v m ell z : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  exact smul_comm _ _ _

private theorem vacuum_theta (m ell : ℕ) (f : QuantumTest) :
    vacuumSymmetric (thetaAction m ell f)=thetaAction m ell (vacuumSymmetric f)+
      (2:ℂ) • ∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum : ℂ) •
        contactAction (scalarDirection a) m ell (inverseVolumeAction f) := by
  unfold vacuumSymmetric
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,
    map_sum,map_smul,map_add,Finset.smul_sum,smul_add,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [inverse_theta,sharp_core_contact,native_core_contact,map_add,inverse_theta,inverse_contact]
  module

/-- The source phase force returns on a fixed input through the two original native contacts. -/
theorem actual_phase_force_cutoff_contact (m ell : ℕ) (f : QuantumTest) :
    phaseForce (thetaAction m ell f)=thetaAction m ell (phaseForce f)+
      ((sourceTime 0 : ℂ)^2) • ∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum : ℂ) •
        contactAction (scalarDirection a) m ell (inverseVolumeAction f) := by
  have hf : phaseForce=((sourceTime 0 : ℂ)^2/2) • vacuumSymmetric := by
    unfold phaseForce
    exact paid_phase_force_source%
  rw [hf,LinearMap.smul_apply,vacuum_theta]
  simp only [LinearMap.smul_apply,map_smul,smul_add,smul_smul]
  congr 1
  have he : ((sourceTime 0 : ℂ)^2/2)*(2:ℂ)=(sourceTime 0 : ℂ)^2 := by ring
  rw [he]

private def contactPrice (f : QuantumTest) : ℝ :=
  (sourceTime 0)^2*(∑ a : ScalarIndex,|inner ℝ (scalarBasis a) vacuum| *(2*‖(scalarDirection a).1‖))*
    ‖embed (inverseVolumeAction f)‖

private theorem contact_price_nonnegative (f : QuantumTest) : 0 ≤ contactPrice f := by
  unfold contactPrice
  positivity

private theorem actual_force_contact_price (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    ‖embed (((sourceTime 0 : ℂ)^2) • ∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum : ℂ) •
      contactAction (scalarDirection a) m ell (inverseVolumeAction f))‖ ≤ contactPrice f/(m+2 : ℝ) := by
  simp only [map_smul,map_sum,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have h := norm_sum_le Finset.univ (fun a : ScalarIndex =>
    (inner ℝ (scalarBasis a) vacuum : ℂ) • embed (contactAction (scalarDirection a) m ell (inverseVolumeAction f)))
  have hb : (∑ a : ScalarIndex,‖(inner ℝ (scalarBasis a) vacuum : ℂ) •
      embed (contactAction (scalarDirection a) m ell (inverseVolumeAction f))‖) ≤
      ∑ a : ScalarIndex,|inner ℝ (scalarBasis a) vacuum| *
        ((2*‖(scalarDirection a).1‖/(m+2 : ℝ))*‖embed (inverseVolumeAction f)‖) := by
    apply Finset.sum_le_sum
    intro a _
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,←bounded_contact_core _ m ell hml]
    exact mul_le_mul_of_nonneg_left (bounded_contact_bound _ m ell hml _) (abs_nonneg _)
  apply (mul_le_mul_of_nonneg_left (h.trans hb) (sq_nonneg (sourceTime 0))).trans_eq
  unfold contactPrice
  simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The force seed is generated from fixed theta return and the actual O(1/m) contact;
no moving-force or graph-norm tail is supplied. -/
theorem actual_fixed_phase_force_cutoff_tail (g : QuantumTest) :
    ∀ ε : ℝ,0 < ε →∃ N : ℕ,∀ m,N ≤ m →∀ ell,m ≤ ell →
      ‖embed (phaseForce (thetaAction m ell g))‖^2 ≤ ε := by
  intro ε hε
  let δ := Real.sqrt ε/2
  have hd : 0 < δ := div_pos (Real.sqrt_pos.mpr hε) (by norm_num)
  obtain ⟨N1,h1⟩ := original_relative_tail (embed (phaseForce g)) δ hd
  obtain ⟨N2,h2⟩ := exists_nat_gt (contactPrice g/δ)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  have hθ := h1 m (by omega) ell hml
  rw [←theta_core m ell (phaseForce g)] at hθ
  have hcontact := actual_force_contact_price m ell hml g
  have hsmall : contactPrice g/(m+2 : ℝ) ≤ δ := by
    apply (div_le_iff₀ (by positivity : 0 < (m+2 : ℝ))).mpr
    have hN : (N2 : ℝ) ≤ m := by exact_mod_cast (show N2 ≤ m by omega)
    have hp := (div_lt_iff₀ hd).mp h2
    have hmδ := mul_le_mul_of_nonneg_right hN hd.le
    nlinarith only [hp,hmδ,hd]
  rw [actual_phase_force_cutoff_contact,map_add]
  have hn := (norm_add_le _ _).trans (add_le_add hθ.le (hcontact.trans hsmall))
  have hs := Real.sq_sqrt hε.le
  have hnorm := norm_nonneg (embed (thetaAction m ell (phaseForce g))+
    embed (((sourceTime 0 : ℂ)^2) • ∑ a : ScalarIndex,(inner ℝ (scalarBasis a) vacuum : ℂ) •
      contactAction (scalarDirection a) m ell (inverseVolumeAction g)))
  dsimp only [δ] at hn
  nlinarith only [hn,hnorm,hs,Real.sqrt_nonneg ε]


elab "paid_square_frequency%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawFrequencyBalance 0) "LowEnergy")
    "ActualExactSylvesterRawFrequencyBalance"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_square_theta_pair%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade 0) "LowEnergy") "ActualTwoResolventCascade") "theta_pair")

private theorem mu_positive : 0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large
private theorem causal_nonreal (advanced : Bool) (w : ℝ) : (causalFrequency advanced sourceMu w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using mu_positive.ne'
private def causalCore (advanced : Bool) (F : Index) (g : QuantumTest) (w : ℝ) : QuantumTest :=
  SourceClockYukawaCubicCurrent.resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced w) g

/-- The new word contains the actual unweighted H0 square and its entire source inverse Ward. -/
def squareWardCurrent (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) : ℝ :=
  let q := causalCore advanced F g w
  let T := thetaAction m ell
  let B := SourceScalarInverseBulk.inverseWeightedBulkJet phaseHamiltonianSquare
  (sourcePair q (((Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*(T*B*T)-(T*B*T)*compressionCore F)) q)).re

def forceResponse (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) : ℝ :=
  ‖embed (phaseForce (thetaAction m ell (causalCore advanced F g w)))‖^2
private def forceCurrent (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) : ℝ :=
  let q := causalCore advanced F g w
  let T := thetaAction m ell
  (sourcePair q (((Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*(T*(phaseForce*phaseForce)*T)-(T*(phaseForce*phaseForce)*T)*compressionCore F)) q)).re
attribute [local irreducible] sourcePair sourceMu phaseForce phaseHamiltonianSquare
  compressionCore SourceClockYukawaCubicCurrent.resolventCore thetaAction
  SourceScalarInverseBulk.inverseWeightedBulkJet SourceInverseNoetherEnergy.bulkAction phaseCoefficient bulkCoefficient

private theorem force_energy (m ell : ℕ) (f : QuantumTest) :
    (sourcePair f ((thetaAction m ell*(phaseForce*phaseForce)*thetaAction m ell) f)).re=
      ‖embed (phaseForce (thetaAction m ell f))‖^2 := by
  simp only [Module.End.mul_apply]
  rw [(paid_square_theta_pair%) m ell f]
  exact actual_phase_force_square_energy _

private theorem force_response_integrable (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    Integrable (forceResponse advanced m ell F g) := by
  have h := ((paid_square_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    (thetaAction m ell*(phaseForce*phaseForce)*thetaAction m ell) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _ => force_energy m ell _))
private theorem force_current_integrable (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    Integrable (forceCurrent advanced m ell F g) := by
  let T := thetaAction m ell*(phaseForce*phaseForce)*thetaAction m ell
  have h := ((paid_square_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    ((Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*T-T*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))
private theorem square_current_integrable (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    Integrable (squareWardCurrent advanced m ell F g) := by
  let T := thetaAction m ell*SourceScalarInverseBulk.inverseWeightedBulkJet phaseHamiltonianSquare*thetaAction m ell
  have h := ((paid_square_frequency% core_pair_integrable) advanced F sourceMu mu_positive
    ((Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*T-T*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))

private theorem force_current_balance (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    (∫ w : ℝ,forceCurrent advanced m ell F g w)=
      2*sourceMu*(∫ w : ℝ,forceResponse advanced m ell F g w)-
      2*Real.pi*‖embed (phaseForce (thetaAction m ell g))‖^2 := by
  let T := thetaAction m ell*(phaseForce*phaseForce)*thetaAction m ell
  have h := ActualExactSylvesterRawFrequencyBalance.actual_core_lyapunov_frequency_balance
    advanced F sourceMu mu_positive T g
  have he := congrArg Complex.re h.2
  have hir := integral_re h.1
  simp only [RCLike.re_to_complex] at hir
  rw [←hir] at he
  have hp (w : ℝ) : (sourcePair (causalCore advanced F g w)
      ((paid_square_frequency% frequencyLyapunov) advanced F sourceMu T (causalCore advanced F g w))).re=
      2*sourceMu*forceResponse advanced m ell F g w-forceCurrent advanced m ell F g w := by
    let q := causalCore advanced F g w
    change (sourcePair q (((2*(sourceMu:ℂ)) • T-
      (Complex.I*(causalSign advanced:ℂ)) • (compressionCore F*T-T*compressionCore F)) q)).re=_
    simp only [LinearMap.sub_apply,LinearMap.smul_apply]
    have hs (x y : QuantumTest) : sourcePair q (x-y)=sourcePair q x-sourcePair q y := by
      simp only [sourcePair,map_sub,inner_sub_right]
    have hc (c : ℂ) (x : QuantumTest) : sourcePair q (c • x)=c*sourcePair q x := by
      simp only [sourcePair,map_smul,inner_smul_right]
    rw [hs,hc,Complex.sub_re]
    change ((2*(sourceMu:ℂ))*sourcePair q (T q)).re-forceCurrent advanced m ell F g w=_
    norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]
    rw [force_energy]
    rfl
  change (∫ w : ℝ,(sourcePair (causalCore advanced F g w)
    ((paid_square_frequency% frequencyLyapunov) advanced F sourceMu T (causalCore advanced F g w))).re)=
    (2*(Real.pi:ℂ)*sourcePair g (T g)).re at he
  simp_rw [hp] at he
  rw [integral_sub ((force_response_integrable advanced m ell F g).const_mul (2*sourceMu))
    (force_current_integrable advanced m ell F g),integral_const_mul] at he
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero] at he
  rw [force_energy] at he
  linarith only [he]

private def currentRead (advanced : Bool) (F : Index) (q : QuantumTest) : End →ₗ[ℂ] ℂ where
  toFun A := sourcePair q (((Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*A-A*compressionCore F)) q)
  map_add' A B := by
    simp only [mul_add,add_mul,add_sub_add_comm,smul_add,LinearMap.add_apply,
      LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_add,inner_add_right]
  map_smul' c A := by
    simp only [mul_smul_comm,smul_mul_assoc,←smul_sub,smul_smul,
      LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,smul_eq_mul,RingHom.id_apply]
    ring

private theorem actual_bulk_current_split (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) :
    bulkCurrentFrequency advanced m ell F g w=
      (-(1/(2*phaseCoefficient)))*squareWardCurrent advanced m ell F g w-
      (8/phaseCoefficient)*forceCurrent advanced m ell F g w := by
  let q := causalCore advanced F g w
  let T := thetaAction m ell
  let B := SourceScalarInverseBulk.inverseWeightedBulkJet phaseHamiltonianSquare
  have h : T*SourceInverseNoetherEnergy.bulkAction*T=
      (-(2*(phaseCoefficient:ℂ))⁻¹) • (T*B*T)+
      (-8*(phaseCoefficient:ℂ)⁻¹) • (T*(phaseForce*phaseForce)*T) := by
    rw [actual_source_bulk_phase_negative_square]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    rfl
  have hread := congrArg (currentRead advanced F q) h
  rw [map_add,map_smul,map_smul] at hread
  have h2 : -(2*(phaseCoefficient:ℂ))⁻¹=((-(1/(2*phaseCoefficient)):ℝ):ℂ) := by
    push_cast;simp only [one_div]
  have h8 : -8*(phaseCoefficient:ℂ)⁻¹=((-(8/phaseCoefficient):ℝ):ℂ) := by
    push_cast;simp only [div_eq_mul_inv,neg_mul]
  rw [h2,h8] at hread
  have hr := congrArg Complex.re hread
  norm_num only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,smul_eq_mul] at hr
  change bulkCurrentFrequency advanced m ell F g w=
    (-(1/(2*phaseCoefficient)))*squareWardCurrent advanced m ell F g w+
      (-(8/phaseCoefficient))*forceCurrent advanced m ell F g w at hr
  linarith only [hr]

/-- The whole weighted current is returned to an actual unweighted H0-square Ward,
with its useful force response retained and its fixed force seed paid internally. -/
theorem actual_raw_unweighted_square_paid_return (g : QuantumTest) :
    ∀ ε : ℝ,0 < ε →∃ N : ℕ,∀ m,N ≤ m →∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced sharp : Bool,
      (∫ w : ℝ,ActualExactSylvesterRawFrequencyBalance.rawFrequencyResidual advanced sharp m ell F g w)-
        (3*bulkCoefficient sharp/(4*phaseCoefficient))*(∫ w : ℝ,squareWardCurrent advanced m ell F g w) ≥
      Real.pi*sourceQ sharp m ell g+(2/sourceMu)*(∫ w : ℝ,reserveFrequency advanced sharp m ell F g w)+
        2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
          (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2+
        (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*(∫ w : ℝ,forceResponse advanced m ell F g w)-ε := by
  intro ε hε
  have ha (s : Bool) : 0 ≤ bulkCoefficient s := by
    unfold bulkCoefficient
    have hn : 0 < sourceTime 0 := by
      rw [source_time_generated]
      exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  let A := bulkCoefficient false+bulkCoefficient true
  have hA : 0 ≤ A := add_nonneg (ha false) (ha true)
  have hc := actual_phase_coefficient_positive
  have hpi := Real.pi_pos
  obtain ⟨N1,h1⟩ := actual_raw_bulk_current_paid_return g (ε/2) (by positivity)
  obtain ⟨N2,h2⟩ := actual_fixed_phase_force_cutoff_tail g
    ((ε/2)/(24*Real.pi*A/phaseCoefficient+1)) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  have hseed := h2 m (by omega) ell hml
  filter_upwards [h1 m (by omega) ell hml] with F hF
  intro advanced sharp
  have hp := hF advanced sharp
  have hcurrent : (∫ w : ℝ,bulkCurrentFrequency advanced m ell F g w)=
      (-(1/(2*phaseCoefficient)))*(∫ w : ℝ,squareWardCurrent advanced m ell F g w)-
      (8/phaseCoefficient)*(∫ w : ℝ,forceCurrent advanced m ell F g w) := by
    simp_rw [actual_bulk_current_split advanced m ell F g]
    rw [integral_sub ((square_current_integrable advanced m ell F g).const_mul _)
      ((force_current_integrable advanced m ell F g).const_mul _),integral_const_mul,integral_const_mul]
  rw [hcurrent,force_current_balance] at hp
  have hs : bulkCoefficient sharp ≤ A := by
    cases sharp
    · exact le_add_of_nonneg_right (ha true)
    · exact le_add_of_nonneg_left (ha false)
  have hspos := ha sharp
  have hκ : 0 ≤ 24*Real.pi*bulkCoefficient sharp/phaseCoefficient := by positivity
  have hmul := mul_le_mul_of_nonneg_left hseed hκ
  have hsmall : (24*Real.pi*bulkCoefficient sharp/phaseCoefficient)*
      ((ε/2)/(24*Real.pi*A/phaseCoefficient+1)) ≤ ε/2 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 24*Real.pi*A/phaseCoefficient+1)).mpr
    have hcoef := (div_le_div_iff_of_pos_right hc).mpr
      (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 24*Real.pi))
    nlinarith only [hcoef,hε]
  have hexp : (3/2:ℝ)*bulkCoefficient sharp*
      ((-(1/(2*phaseCoefficient)))*(∫ w : ℝ,squareWardCurrent advanced m ell F g w)-
        (8/phaseCoefficient)*(2*sourceMu*(∫ w : ℝ,forceResponse advanced m ell F g w)-
          2*Real.pi*‖embed (phaseForce (thetaAction m ell g))‖^2))=
      -(3*bulkCoefficient sharp/(4*phaseCoefficient))*(∫ w : ℝ,squareWardCurrent advanced m ell F g w)-
        (24*bulkCoefficient sharp*sourceMu/phaseCoefficient)*(∫ w : ℝ,forceResponse advanced m ell F g w)+
        (24*Real.pi*bulkCoefficient sharp/phaseCoefficient)*‖embed (phaseForce (thetaAction m ell g))‖^2 := by ring
  rw [hexp] at hp
  linarith only [hp,hmul,hsmall]

end LowEnergy.ActualBulkCurrentSquareReturn
