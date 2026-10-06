import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeFrequencyBand
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussAdjointHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseJetEnergy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPositiveBulkWard
open SourceScalarInverseNativeEnergy SourceScalarInverseBulk SourceScalarInverseEndpoint
open FullYSourceResolventGraphSplice Filter
open scoped InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] GaussDiagonalHistory.diagonalAction
  SourceScalarPositiveBulkWard.state SourceScalarInverseNativeEnergy.inverseForm
  GaussAdjointHistory.coreStep GaussAdjointHistory.iterate
  SourceScalarInverseBulk.inverseWeightedBulkJet SourceScalarInverseBulk.inverseSymmetricScale

private theorem step_coe (g : diagonal.domain) : (GaussAdjointHistory.coreStep g : H)=diagonal g := by
  unfold GaussAdjointHistory.coreStep
  rfl

/-- Exact source update before any changed test is applied; only the fixed input is made exact in F. -/
theorem actual_source_step (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      z • state F z hz g=state F z hz (GaussAdjointHistory.coreStep g)-coreEquiv.symm g := by
  filter_upwards [GaussGradedCompression.eventually_exact g] with F hF z hz
  have h := congrArg (fun R : H →L[ℂ] H => R (g : H))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (g : H))=
    (g : H)+z • finiteResolvent F z (g : H) at h
  rw [hF] at h
  let q : Core := SourceEscapeCurrent.sourceCore F z hz g
  let qNext : Core := SourceEscapeCurrent.sourceCore F z hz (GaussAdjointHistory.coreStep g)
  let u : Core := g
  have hc : z • q=qNext-u := by
    apply Subtype.ext
    change z • finiteResolvent F z (g : H)=finiteResolvent F z (GaussAdjointHistory.coreStep g : H)-(g : H)
    rw [step_coe,h]
    abel
  have hh := congrArg coreEquiv.symm hc
  rw [coreEquiv.symm.map_smul] at hh
  have hd : coreEquiv.symm (qNext-u)=coreEquiv.symm qNext-coreEquiv.symm u :=
    map_sub coreEquiv.symm.toLinearMap qNext u
  unfold state
  exact hh.trans hd

private theorem form_smul (c : ℂ) (f : QuantumTest) :
    inverseForm (c • f)=‖c‖^2*inverseForm f := by
  unfold inverseForm
  simp only [map_smul,sourcePair,inner_smul_left,inner_smul_right]
  rw [←mul_assoc,mul_comm c ((starRingEnd ℂ) c),←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

private theorem form_sub_le (u v : QuantumTest) :
    inverseForm (u-v) ≤ 2*(inverseForm u+inverseForm v) := by
  have he : inverseForm (u-v)+inverseForm (u+v)=2*(inverseForm u+inverseForm v) := by
    unfold inverseForm
    simp only [map_add,map_sub,sourcePair,inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
      Complex.add_re,Complex.sub_re]
    ring
  have hn := original_inverse_nonnegative (u+v)
  linarith only [he,hn]

def stepWeight (z : ℂ) : ℝ := 2/‖z‖^2

/-- Every original core endomorphism may consume the update, including unbounded scalar/volume readers. -/
theorem actual_energy_step (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0, ∀ A : End,
      inverseForm (A (state F z hz g)) ≤ stepWeight z*
        (inverseForm (A (coreEquiv.symm g))+inverseForm (A (state F z hz (GaussAdjointHistory.coreStep g)))) := by
  filter_upwards [actual_source_step g] with F hF z hz A
  have hz0 : z≠0 := by intro h;exact hz (h ▸ rfl)
  have hn : 0<‖z‖^2 := pow_pos (norm_pos_iff.mpr hz0) 2
  have he : ‖z‖^2*inverseForm (A (state F z hz g))=
      inverseForm (A (state F z hz (GaussAdjointHistory.coreStep g))-A (coreEquiv.symm g)) := by
    have hh := congrArg (fun q => inverseForm (A q)) (hF z hz)
    simpa only [map_smul,map_sub,form_smul] using hh
  have hb := form_sub_le (A (state F z hz (GaussAdjointHistory.coreStep g))) (A (coreEquiv.symm g))
  calc
    _ ≤ (2*(inverseForm (A (coreEquiv.symm g))+
        inverseForm (A (state F z hz (GaussAdjointHistory.coreStep g)))))/‖z‖^2 := by
      apply (le_div_iff₀ hn).mpr
      nlinarith only [he,hb]
    _ = _ := by unfold stepWeight;ring

private theorem iterate_next (r : ℕ) (g : diagonal.domain) :
    GaussAdjointHistory.coreStep (GaussAdjointHistory.iterate r g)=GaussAdjointHistory.iterate (r+1) g := by
  simp only [GaussAdjointHistory.iterate,pow_succ',Module.End.mul_apply]

/-- One common eventual F precedes all nonreal frequencies and all changed source tests at the chosen jet depth. -/
theorem actual_source_jet_energy (r : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0, ∀ A : End,
      inverseForm (A (state F z hz g)) ≤
        (∑ j ∈ Finset.range r,(stepWeight z)^(j+1)*inverseForm (A (coreEquiv.symm (GaussAdjointHistory.iterate j g))))+
        (stepWeight z)^r*inverseForm (A (state F z hz (GaussAdjointHistory.iterate r g))) := by
  induction r with
  | zero =>
    filter_upwards [] with F z hz A
    simp only [Finset.sum_range_zero,pow_zero,one_mul,zero_add,
      GaussAdjointHistory.iterate,Module.End.one_apply,le_refl]
  | succ r ih =>
    filter_upwards [ih,actual_energy_step (GaussAdjointHistory.iterate r g)] with F hi hs z hz A
    have h := hs z hz A
    rw [iterate_next] at h
    have hp : 0≤(stepWeight z)^r := by unfold stepWeight;positivity
    have hb := mul_le_mul_of_nonneg_left h hp
    have hh := hi z hz A
    rw [Finset.sum_range_succ,pow_succ]
    nlinarith only [hh,hb]

/-- The exact far-frequency factor depends on the complete complex frequency, not on its sign. -/
theorem source_weight_bound (z : ℂ) (L : ℝ) (hL : 0<L) (hz : L≤|z.re|) :
    stepWeight z≤2/L^2 := by
  have hn : L≤‖z‖ := hz.trans (Complex.abs_re_le_norm z)
  have hs := pow_le_pow_left₀ hL.le hn 2
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hL 2) hs

end LowEnergy.SourceInverseJetEnergy
