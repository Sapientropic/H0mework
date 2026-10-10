import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffFamilyDifference
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualThreeParticleCutoffSharp
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockSharpCausalMass
import Lean.Elab.Term

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualThreeParticleCutoffTime
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory GaussCoreLabel
open ActualThreeParticleCutoffGram ActualCutoffFrequencyBase ActualThreeParticleCutoffFamily
open SourceFamilyHilbert FullYSourceFiniteTimeIntegral FullYSourceCutoffVolterra
open FullYSourceResolventGraphSplice FullYPairedParseval FullYDynamicSourceNext
open SourceResolventBandLimit SourceResolventLorentzian MeasureTheory Filter Set
open scoped Topology InnerProductSpace FourierTransform Interval
private abbrev L2H := Lp H 2 (volume : Measure ℝ)
local instance : SecondCountableTopologyEither ℝ H := secondCountableTopologyEither_of_left ℝ H

section PaidHelpers
open Lean Meta Elab Term
elab "paid_cutoff_causal%" helper:ident : term => do
  let ns := Name.str (Name.str (Name.num
    (`_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYUncutRetardedKernel) 0) "LowEnergy") "FullYDynamicSourceNext"
  let name := Name.str ns helper.getId.toString
  unless (← getEnv).contains name do throwError "Missing paid causal helper: {name}"
  mkConstWithFreshMVarLevels name
elab "paid_cutoff_parseval%" helper:ident : term => do
  let ns := Name.str (Name.str (Name.num
    (`_private.H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYPositiveOutputParseval) 0) "LowEnergy") "FourGradeOutputParseval"
  let name := Name.str ns helper.getId.toString
  unless (← getEnv).contains name do throwError "Missing paid Parseval helper: {name}"
  mkConstWithFreshMVarLevels name
elab "paid_cutoff_square%" : term => do
  let ns := Name.str (Name.str (Name.num
    (`_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockSharpCausalMass) 0) "LowEnergy") "ActualFourBlockSharpCausalMass"
  let name := Name.str ns "polynomial_wave_square_integrable"
  unless (← getEnv).contains name do throwError "Missing paid square helper: {name}"
  mkConstWithFreshMVarLevels name
end PaidHelpers

/-- The unchanged actual C_F plus the original cutoff, or its independent adjoint. -/
def generator (F : Index) (n : ℕ) (sharp : Bool) : H →L[ℂ] H :=
  GaussGradedCompression.compression F + if sharp then (cutoff n).adjoint else cutoff n

def branchInverse (F : Index) (n : ℕ) (sharp : Bool) (z : ℂ) : H →L[ℂ] H :=
  if sharp then sharpInverse F n z else inverse F n z

theorem actual_generator_right_inverse (F : Index) (n : ℕ) (sharp : Bool)
    (z : ℂ) (hz : z.im ≠ 0) :
    (generator F n sharp-z • 1)*branchInverse F n sharp z=1 := by
  cases sharp
  · exact actual_cutoff_right_inverse F n z hz
  · exact actual_cutoff_sharp_right_inverse F n z hz

theorem actual_generator_left_inverse (F : Index) (n : ℕ) (sharp : Bool)
    (z : ℂ) (hz : z.im ≠ 0) :
    branchInverse F n sharp z*(generator F n sharp-z • 1)=1 := by
  cases sharp
  · exact actual_cutoff_left_inverse F n z hz
  · exact actual_cutoff_sharp_left_inverse F n z hz

theorem actual_time_polynomial_bound (F : Index) (n : ℕ) (sharp : Bool) (t : ℝ) :
    ‖SourceFiniteUnitary.time (generator F n sharp) t‖ ≤
      ∑j∈Finset.range 57,(|t| * ‖cutoff n‖)^j := by
  cases sharp
  · exact source_finite_time_bound n F t
  · change ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+(cutoff n).adjoint) t‖ ≤ _
    rw [← time_sum_adjoint _ _ (GaussGradedCompression.compression_selfAdjoint F),
      ContinuousLinearMap.adjoint.norm_map]
    simpa only [abs_neg,sourceGrowth] using source_finite_time_bound n F (-t)

/-- This is the actual operator exponential, with the finite Dyson expansion already paid. -/
def literalCoreTime (F : Index) (n : ℕ) (sharp : Bool) (x : H) (t : ℝ) : H :=
  SourceFiniteUnitary.time (generator F n sharp) t x

def wave (F : Index) (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (x : H) : ℝ → H :=
  causalWave μ (fun t => literalCoreTime F n sharp x (FullYPairedParseval.direction advanced*t))

private theorem time_continuous (F : Index) (n : ℕ) (sharp : Bool) (x : H) :
    Continuous (literalCoreTime F n sharp x) := by
  apply (ContinuousLinearMap.apply ℂ H x).continuous.comp
  exact continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • generator F n sharp) t).continuousAt)

private theorem time_bound (F : Index) (n : ℕ) (sharp : Bool) (x : H) (t : ℝ) :
    ‖literalCoreTime F n sharp x t‖ ≤
      (∑j∈Finset.range 57,(|t| * ‖cutoff n‖)^j)*‖x‖ :=
  ((SourceFiniteUnitary.time (generator F n sharp) t).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (actual_time_polynomial_bound F n sharp t) (norm_nonneg _))

theorem actual_wave_integrable (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) : Integrable (wave F n sharp advanced μ x) :=
  FullYPairedParseval.direction_wave_integrable μ hμ _ (time_continuous F n sharp x) ‖x‖
    ⟨‖cutoff n‖,time_bound F n sharp x⟩ advanced

theorem actual_wave_square_integrable (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) : Integrable (fun t => ‖wave F n sharp advanced μ x t‖^2) := by
  apply (paid_cutoff_square%) μ ‖cutoff n‖ ‖x‖ hμ
    (fun t => literalCoreTime F n sharp x (FullYPairedParseval.direction advanced*t))
    ((time_continuous F n sharp x).comp (continuous_const.mul continuous_id))
  intro t
  have h := time_bound F n sharp x (FullYPairedParseval.direction advanced*t)
  cases advanced <;> simpa only [FullYPairedParseval.direction,ite_true,Bool.false_eq_true,ite_false,
    one_mul,neg_one_mul,abs_neg] using h

/-- The original causal sign and Fourier normalization return the actual 57-term inverse. -/
theorem actual_wave_fourier (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) (ξ : ℝ) :
    ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • 𝓕 (wave F n sharp advanced μ x) ξ =
      branchInverse F n sharp (sourceLine advanced μ ξ) x := by
  let z := sourceLine advanced μ ξ
  have hz := source_line_half_plane advanced μ ξ hμ
  have hn : z.im≠0 := by cases advanced; exact hz.ne'; exact hz.ne
  have hc := (paid_cutoff_causal% oriented_causal_limit)
    (generator F n sharp) (branchInverse F n sharp z) advanced z hz
    (actual_generator_right_inverse F n sharp z hn) ‖cutoff n‖
    (actual_time_polynomial_bound F n sharp)
  have hca := (ContinuousLinearMap.apply ℂ H x).continuous.tendsto _ |>.comp hc
  have hi := actual_wave_integrable F n sharp advanced μ hμ x
  have hf := (causal_fourier_limit μ ξ
    (fun t => literalCoreTime F n sharp x (FullYPairedParseval.direction advanced*t)) hi).const_smul
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I)
  have he (T : ℝ) : orientedSourceCausal (generator F n sharp) advanced z T x =
      ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) • ∫t in (0:ℝ)..T,
        Complex.exp (t • (Complex.I*line μ (-2*Real.pi*ξ))) •
          literalCoreTime F n sharp x (FullYPairedParseval.direction advanced*t) := by
    cases advanced
    · have h := (paid_cutoff_causal% causal_apply) (generator F n sharp) (1 : H →L[ℂ] H) x z T
      change sourceCausal (generator F n sharp) z T x=Complex.I • ∫t in (0:ℝ)..T,
        Complex.exp (t • (Complex.I*z)) • SourceFiniteUnitary.time (generator F n sharp) t x at h
      simpa only [orientedSourceCausal,sourceLine,z,FullYPairedParseval.direction,Bool.false_eq_true,ite_false,
        Complex.ofReal_one,one_mul,literalCoreTime] using h
    · have h := (paid_cutoff_causal% causal_apply) (-generator F n sharp)
        (1 : H →L[ℂ] H) x (-z) T
      change sourceCausal (-generator F n sharp) (-z) T x=Complex.I • ∫t in (0:ℝ)..T,
        Complex.exp (t • (Complex.I*(-z))) • SourceFiniteUnitary.time (-generator F n sharp) t x at h
      change -(sourceCausal (-generator F n sharp) (-z) T x) = _
      rw [h]
      simp only [sourceLine,z,FullYPairedParseval.direction,ite_true,Complex.ofReal_neg,
        Complex.ofReal_one,neg_mul,one_mul,neg_neg,neg_smul,literalCoreTime]
      congr 2
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [(paid_cutoff_causal% time_negative)]
  have ha := hca.congr' (Eventually.of_forall he)
  exact tendsto_nhds_unique hf ha



attribute [local irreducible] GaussCoreHilbert.embed generator branchInverse wave literalCoreTime

private theorem direction_I_norm (advanced : Bool) :
    ‖(FullYPairedParseval.direction advanced:ℂ)*Complex.I‖=1 := by
  cases advanced <;> simp [FullYPairedParseval.direction]

private theorem inverse_second_jet {R : Type*} [Ring R] [Algebra ℂ R]
    (A U : R) (z : ℂ) (hz : z≠0) (hi : U*(A-z • 1)=1) :
    U+z⁻¹ • 1=z⁻¹^2 • (U*A^2-A) := by
  have h : z • U=U*A-1 := by
    simp only [mul_sub,mul_smul_comm,mul_one] at hi
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hi).symm)
  have hU : U=z⁻¹ • (U*A-1) := by rw [←h,smul_smul,inv_mul_cancel₀ hz,one_smul]
  have hUA : U*A=z⁻¹ • (U*A^2-A) := by
    conv_lhs => rw [hU]
    simp only [smul_mul_assoc,sub_mul,one_mul,mul_assoc,pow_two]
  calc
    _ = z⁻¹ • (U*A) := by
      conv_lhs => rw [hU]
      rw [smul_sub]
      abel
    _ = z⁻¹^2 • (U*A^2-A) := by
      have h := congrArg (fun B : R => z⁻¹ • B) hUA
      exact h.trans (by rw [smul_smul]; congr 1; exact (pow_two _).symm)

private theorem baseline_return (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (x : H) (ξ : ℝ) :
    ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) •
      𝓕 (causalWave μ (fun _ => x)) ξ= -(sourceLine advanced μ ξ)⁻¹ • x := by
  rw [constant_wave_fourier μ hμ,smul_smul]
  congr 1
  cases advanced <;> simp only [FullYPairedParseval.direction,sourceLine,ite_true,
    Bool.false_eq_true,ite_false,Complex.ofReal_one,Complex.ofReal_neg,one_mul,
    neg_mul,inv_neg,neg_neg,div_eq_mul_inv]
  all_goals simp only [←mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]

private theorem source_inverse_square (advanced : Bool) (μ ξ : ℝ) :
    ‖(sourceLine advanced μ ξ)⁻¹‖^2=kernel μ 0 (-2*Real.pi*ξ) := by
  have h := inverse_norm_square μ 0 (-2*Real.pi*ξ)
  cases advanced <;> simpa only [sourceLine,FullYPairedParseval.direction,ite_true,
    Bool.false_eq_true,ite_false,Complex.ofReal_one,Complex.ofReal_neg,neg_mul,
    one_mul,inv_neg,norm_neg,Complex.ofReal_zero,zero_sub,norm_inv,line,
    mul_comm (μ:ℂ) Complex.I] using h

private theorem correction_continuous (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (x : H) : Continuous (wave F n sharp advanced μ x-causalWave μ (fun _ => x)) := by
  unfold wave
  apply correction_wave_continuous
  · exact (time_continuous F n sharp x).comp (continuous_const.mul continuous_id)
  · simp only [mul_zero,literalCoreTime,SourceFiniteUnitary.time_zero,one_apply_eq_self]

/-- Both generator jets are actual H-vectors; their source time polynomial pays the Fourier correction. -/
theorem actual_correction_fourier_integrable (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) :
    Integrable (𝓕 (wave F n sharp advanced μ x-causalWave μ (fun _ => x))) := by
  let A := generator F n sharp
  let D := ‖A x‖+∫t : ℝ,‖wave F n sharp advanced μ ((A^2) x) t‖
  have hu := actual_wave_integrable F n sharp advanced μ hμ x
  have hb := constant_wave_integrable μ hμ x
  have hR (v : H) (ξ : ℝ) : ‖branchInverse F n sharp (sourceLine advanced μ ξ) v‖ ≤
      ∫t : ℝ,‖wave F n sharp advanced μ v t‖ := by
    rw [←actual_wave_fourier F n sharp advanced μ hμ v ξ,norm_smul,direction_I_norm,one_mul]
    exact fourier_bound _ ξ
  have hbound (ξ : ℝ) :
      ‖𝓕 (wave F n sharp advanced μ x-causalWave μ (fun _ => x)) ξ‖ ≤
        kernel μ 0 (-2*Real.pi*ξ)*D := by
    let z := sourceLine advanced μ ξ
    have hz : z.im≠0 := by
      have h := source_line_half_plane advanced μ ξ hμ
      cases advanced; exact h.ne'; exact h.ne
    have hz0 : z≠0 := fun h => hz (congrArg Complex.im h)
    have hid := congrArg (fun U : H →L[ℂ] H => U x)
      (inverse_second_jet A (branchInverse F n sharp z) z hz0
        (actual_generator_left_inverse F n sharp z hz))
    simp only [add_apply,smul_apply,one_apply_eq_self,sub_apply,mul_apply_eq_comp] at hid
    have hc : ((FullYPairedParseval.direction advanced:ℂ)*Complex.I) •
        𝓕 (wave F n sharp advanced μ x-causalWave μ (fun _ => x)) ξ =
        branchInverse F n sharp z x+z⁻¹ • x := by
      rw [fourier_sub_integrable _ _ hu hb,smul_sub,(actual_wave_fourier F n sharp advanced μ hμ x ξ),
        (baseline_return advanced μ hμ x ξ),neg_smul,sub_neg_eq_add]
    have hn := congrArg norm (hc.trans hid)
    rw [norm_smul,direction_I_norm,one_mul,norm_smul,norm_pow] at hn
    have hB : ‖branchInverse F n sharp z ((A^2) x)-A x‖ ≤ D :=
      (norm_sub_le _ _).trans (by
        dsimp only [D]
        linarith [hR ((A^2) x) ξ])
    calc
      _ = ‖z⁻¹‖^2*‖branchInverse F n sharp z ((A^2) x)-A x‖ := hn
      _ ≤ ‖z⁻¹‖^2*D := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
      _ = _ := congrArg (fun v : ℝ => v*D) (source_inverse_square advanced μ ξ)
  have hi := ((kernel_integrable μ 0 hμ).comp_mul_left'
    (by positivity : -2*Real.pi≠0)).mul_const D
  exact hi.mono' (fourier_continuous_of_integrable _ (hu.sub hb)).aestronglyMeasurable
    (Eventually.of_forall hbound)

private theorem parseval_from_correction (u : ℝ → H) (x : H) (μ : ℝ) (hμ : 0<μ)
    (hu : Integrable u) (hu2 : Integrable (fun t => ‖u t‖^2))
    (hc : Continuous (u-causalWave μ (fun _ => x)))
    (hFc : Integrable (𝓕 (u-causalWave μ (fun _ => x)))) :
    (∫ξ : ℝ,‖𝓕 u ξ‖^2)=∫t : ℝ,‖u t‖^2 := by
  let b := causalWave μ (fun _ => x)
  have hb : Integrable b := constant_wave_integrable μ hμ x
  have hb2 : Integrable (fun t => ‖b t‖^2) :=
    (paid_cutoff_parseval% baseline_time_square_integrable) x μ hμ
  have hbF2 : Integrable (fun ξ => ‖𝓕 b ξ‖^2) :=
    (paid_cutoff_parseval% baseline_frequency_square_integrable) x μ hμ
  have hc2 : Integrable (fun t => ‖(u-b) t‖^2) := by
    have h := ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr hu2).sub
      ((memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mpr hb2)
    exact (memLp_two_iff_integrable_sq_norm (hu.sub hb).aestronglyMeasurable).mp h
  have hbu : Integrable (fun ξ => inner ℂ (𝓕 b ξ) (𝓕 b ξ)) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact hbF2.ofReal
  have hbt : Integrable (fun t => inner ℂ (b t) (b t)) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    exact hb2.ofReal
  have hebase : (∫ξ : ℝ,inner ℂ (𝓕 b ξ) (𝓕 b ξ))=∫t : ℝ,inner ℂ (b t) (b t) := by
    simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow]
    rw [integral_ofReal,integral_ofReal]
    exact congrArg (fun r : ℝ => (r:ℂ))
      (((paid_cutoff_parseval% baseline_square_mass) x μ hμ).1.trans
        ((paid_cutoff_parseval% baseline_square_mass) x μ hμ).2.symm)
  have h := (paid_cutoff_parseval% positive_output_parseval) u b hu hb hc hFc hbu hbt
    ((paid_cutoff_parseval% square_pair_integrable) _ _ (hu.sub hb).aestronglyMeasurable
      hb.aestronglyMeasurable hc2 hb2)
    ((paid_cutoff_parseval% square_pair_integrable) _ _ hu.aestronglyMeasurable
      (hu.sub hb).aestronglyMeasurable hu2 hc2) hebase
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  rw [integral_ofReal,integral_ofReal] at h
  exact Complex.ofReal_injective h

private def frequencyScale (advanced : Bool) : ℝ := -FullYPairedParseval.direction advanced*(2*Real.pi)
private theorem scale_abs (advanced : Bool) : |frequencyScale advanced|=2*Real.pi := by
  cases advanced <;> simp [frequencyScale,FullYPairedParseval.direction,abs_of_pos Real.pi_pos]
private theorem line_scale (advanced : Bool) (μ ξ : ℝ) :
    frequency advanced μ (frequencyScale advanced*ξ)=sourceLine advanced μ ξ := by
  cases advanced <;> simp only [frequency,line,frequencyScale,sourceLine,
    FullYPairedParseval.direction,ite_true,Bool.false_eq_true,ite_false,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  all_goals ring

/-- The absolute whole-axis time mass is generated at every fixed cutoff and either independent branch. -/
theorem actual_absolute_time_mass (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫w : ℝ,‖branchInverse F n sharp (frequency advanced μ w) x‖^2)=
      (2*Real.pi)*(∫t : ℝ,‖wave F n sharp advanced μ x t‖^2) := by
  have hf (ξ : ℝ) : ‖branchInverse F n sharp (frequency advanced μ (frequencyScale advanced*ξ)) x‖^2=
      ‖𝓕 (wave F n sharp advanced μ x) ξ‖^2 := by
    rw [line_scale,←actual_wave_fourier F n sharp advanced μ hμ x ξ,
      norm_smul,direction_I_norm,one_mul]
  have hp := parseval_from_correction _ x μ hμ
    (actual_wave_integrable F n sharp advanced μ hμ x)
    (actual_wave_square_integrable F n sharp advanced μ hμ x)
    (correction_continuous F n sharp advanced μ x)
    (actual_correction_fourier_integrable F n sharp advanced μ hμ x)
  have hi := Measure.integral_comp_mul_left
    (fun w => ‖branchInverse F n sharp (frequency advanced μ w) x‖^2) (frequencyScale advanced)
  have he := hi.symm.trans ((integral_congr_ae (Eventually.of_forall hf)).trans hp)
  simp only [abs_inv,scale_abs,smul_eq_mul] at he
  have h := congrArg (fun r : ℝ => (2*Real.pi)*r) he
  simpa only [←mul_assoc,mul_inv_cancel₀ (by positivity : 2*Real.pi≠0),one_mul] using h



private theorem difference_parseval (F : Index) (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫ξ : ℝ,‖𝓕 (wave F ell sharp advanced μ x-wave F m sharp advanced μ x) ξ‖^2)=
      ∫t : ℝ,‖wave F ell sharp advanced μ x t-wave F m sharp advanced μ x t‖^2 := by
  let u := wave F ell sharp advanced μ x
  let v := wave F m sharp advanced μ x
  let b := causalWave μ (fun _ => x)
  have hu := actual_wave_integrable F ell sharp advanced μ hμ x
  have hv := actual_wave_integrable F m sharp advanced μ hμ x
  have hb : Integrable b := constant_wave_integrable μ hμ x
  have he : u-v=(u-b)-(v-b) := by funext t; simp only [Pi.sub_apply]; abel
  have hc : Continuous (u-v) := by
    rw [he]
    exact (correction_continuous F ell sharp advanced μ x).sub
      (correction_continuous F m sharp advanced μ x)
  have hF : Integrable (𝓕 (u-v)) := by
    have h := (actual_correction_fourier_integrable F ell sharp advanced μ hμ x).sub
      (actual_correction_fourier_integrable F m sharp advanced μ hμ x)
    apply h.congr
    exact Eventually.of_forall (fun ξ => by
      change 𝓕 (u-b) ξ-𝓕 (v-b) ξ=𝓕 (u-v) ξ
      rw [he,fourier_sub_integrable _ _ (hu.sub hb) (hv.sub hb)])
  have h := (paid_cutoff_parseval% one_sided_positive_parseval) (u-v) (u-v)
    (hu.sub hv) (hu.sub hv) hc hF
  simp only [inner_self_eq_norm_sq_to_K,←RCLike.ofReal_pow] at h
  rw [integral_ofReal,integral_ofReal] at h
  exact Complex.ofReal_injective h

/-- Same-F differences keep all ordered words and their complex interference on the time axis. -/
theorem actual_absolute_time_difference_mass (F : Index) (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫w : ℝ,‖branchInverse F ell sharp (frequency advanced μ w) x-
      branchInverse F m sharp (frequency advanced μ w) x‖^2)=
      (2*Real.pi)*(∫t : ℝ,‖wave F ell sharp advanced μ x t-wave F m sharp advanced μ x t‖^2) := by
  have hf (ξ : ℝ) : ‖branchInverse F ell sharp (frequency advanced μ (frequencyScale advanced*ξ)) x-
      branchInverse F m sharp (frequency advanced μ (frequencyScale advanced*ξ)) x‖^2=
      ‖𝓕 (wave F ell sharp advanced μ x-wave F m sharp advanced μ x) ξ‖^2 := by
    rw [line_scale,←actual_wave_fourier F ell sharp advanced μ hμ x ξ,
      ←actual_wave_fourier F m sharp advanced μ hμ x ξ,←smul_sub,
      ←fourier_sub_integrable _ _ (actual_wave_integrable F ell sharp advanced μ hμ x)
        (actual_wave_integrable F m sharp advanced μ hμ x),
      norm_smul,direction_I_norm,one_mul]
  have hi := Measure.integral_comp_mul_left
    (fun w => ‖branchInverse F ell sharp (frequency advanced μ w) x-
      branchInverse F m sharp (frequency advanced μ w) x‖^2) (frequencyScale advanced)
  have he := hi.symm.trans ((integral_congr_ae (Eventually.of_forall hf)).trans
    (difference_parseval F m ell sharp advanced μ hμ x))
  simp only [abs_inv,scale_abs,smul_eq_mul] at he
  have h := congrArg (fun r : ℝ => (2*Real.pi)*r) he
  simpa only [←mul_assoc,mul_inv_cancel₀ (by positivity : 2*Real.pi≠0),one_mul] using h

private def branchPrice (n : ℕ) (sharp : Bool) (μ : ℝ) : ℝ :=
  if sharp then 1 else responsePrice n μ
private theorem branch_price_nonnegative (n : ℕ) (sharp : Bool) (μ : ℝ) (hμ : 0<μ) :
    0≤branchPrice n sharp μ := by
  cases sharp
  · exact actual_response_price_nonnegative n μ hμ
  · exact zero_le_one

def finiteFrequency (F : Index) (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) : L2H :=
  if sharp then finiteBase F advanced μ hμ (embed q) else finiteResponse F n advanced μ hμ q hq

theorem actual_finite_frequency_read (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    (fun w : ℝ => finiteFrequency F n sharp advanced μ hμ q hq w) =ᵐ[volume]
      (fun w => branchInverse F n sharp (frequency advanced μ w) (embed q)) := by
  cases sharp
  · simpa only [finiteFrequency,branchInverse,Bool.false_eq_true,ite_false] using
      actual_finite_response_read F n advanced μ hμ q hq
  · have h := actual_finite_base_read F advanced μ hμ (embed q)
    simpa only [finiteFrequency,branchInverse,ite_true] using
      h.trans (Eventually.of_forall (fun w =>
        (actual_sharp_response F n _ (frequency_nonreal advanced μ hμ w) q hq).symm))

private theorem finite_frequency_bound (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteFrequency F n sharp advanced μ hμ q hq‖≤
      branchPrice n sharp μ*Real.sqrt (Real.pi/μ*‖embed q‖^2) := by
  cases sharp
  · exact actual_finite_response_bound F n advanced μ hμ q hq
  · simpa only [finiteFrequency,branchPrice,ite_true,one_mul] using
      actual_finite_base_bound F advanced μ hμ (embed q)

def frequencyFamily (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) : Family L2H sourceFilter where
  val F := finiteFrequency F n sharp advanced μ hμ q hq
  property := ⟨branchPrice n sharp μ*Real.sqrt (Real.pi/μ*‖embed q‖^2),
    mul_nonneg (branch_price_nonnegative n sharp μ hμ) (Real.sqrt_nonneg _),
    fun F => finite_frequency_bound F n sharp advanced μ hμ q hq⟩

def sourceBranchFrequency (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) : TimeSpace (volume : Measure ℝ) :=
  (frequencyFamily n sharp advanced μ hμ q hq : TimeSpace (volume : Measure ℝ))

theorem actual_primal_frequency (n : ℕ) (advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    sourceBranchFrequency n false advanced μ hμ q hq=sourceFrequency n advanced μ hμ q hq := rfl

private theorem wave_memLp (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (x : H) : MemLp (wave F n sharp advanced μ x) 2 (volume : Measure ℝ) :=
  (memLp_two_iff_integrable_sq_norm
    (actual_wave_integrable F n sharp advanced μ hμ x).aestronglyMeasurable).mpr
      (actual_wave_square_integrable F n sharp advanced μ hμ x)

/-- The component is the actual damped operator exponential on the whole time axis. -/
def finiteTime (F : Index) (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) : L2H :=
  (wave_memLp F n sharp advanced μ hμ (embed q)).toLp (wave F n sharp advanced μ (embed q))

theorem actual_finite_time_read (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) :
    (fun t : ℝ => finiteTime F n sharp advanced μ hμ q t) =ᵐ[volume]
      wave F n sharp advanced μ (embed q) :=
  (wave_memLp F n sharp advanced μ hμ (embed q)).coeFn_toLp

private theorem finite_time_square (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) :
    ‖finiteTime F n sharp advanced μ hμ q‖^2=
      ∫t : ℝ,‖wave F n sharp advanced μ (embed q) t‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  exact integral_congr_ae ((actual_finite_time_read F n sharp advanced μ hμ q).mono
    (fun t ht => congrArg (fun x : H => ‖x‖^2) ht))

theorem actual_finite_time_energy (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteFrequency F n sharp advanced μ hμ q hq‖^2=
      (2*Real.pi)*‖finiteTime F n sharp advanced μ hμ q‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral,finite_time_square]
  exact (integral_congr_ae ((actual_finite_frequency_read F n sharp advanced μ hμ q hq).mono
    (fun t ht => congrArg (fun x : H => ‖x‖^2) ht))).trans
      (actual_absolute_time_mass F n sharp advanced μ hμ (embed q))

private theorem finite_time_bound (F : Index) (n : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteTime F n sharp advanced μ hμ q‖≤
      branchPrice n sharp μ*Real.sqrt (Real.pi/μ*‖embed q‖^2) := by
  apply le_trans _ (finite_frequency_bound F n sharp advanced μ hμ q hq)
  have he := actual_finite_time_energy F n sharp advanced μ hμ q hq
  have hpi := Real.pi_gt_three
  nlinarith [norm_nonneg (finiteTime F n sharp advanced μ hμ q),
    norm_nonneg (finiteFrequency F n sharp advanced μ hμ q hq),
    sq_nonneg ‖finiteTime F n sharp advanced μ hμ q‖]

/-- This family uses the existing sourceFilter after the actual whole-axis time integral. -/
def timeFamily (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) : Family L2H sourceFilter where
  val F := finiteTime F n sharp advanced μ hμ q
  property := ⟨branchPrice n sharp μ*Real.sqrt (Real.pi/μ*‖embed q‖^2),
    mul_nonneg (branch_price_nonnegative n sharp μ hμ) (Real.sqrt_nonneg _),
    fun F => finite_time_bound F n sharp advanced μ hμ q hq⟩

def sourceTime (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) : TimeSpace (volume : Measure ℝ) :=
  (timeFamily n sharp advanced μ hμ q hq : TimeSpace (volume : Measure ℝ))

theorem actual_time_family_read (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) (F : Index) :
    (fun t : ℝ => value (timeFamily n sharp advanced μ hμ q hq) F t) =ᵐ[volume]
      (Ioi 0).indicator (fun t : ℝ => (Real.exp (-μ*t):ℂ) •
        SourceFiniteUnitary.time (GaussGradedCompression.compression F+
          if sharp then (cutoff n).adjoint else cutoff n)
          (FullYPairedParseval.direction advanced*t) (embed q)) := by
  change (fun t : ℝ => finiteTime F n sharp advanced μ hμ q t) =ᵐ[volume] _
  simpa only [wave,literalCoreTime,generator,causalWave] using actual_finite_time_read F n sharp advanced μ hμ q

/-- Both completions read the same source occurrence and the unchanged 2π normalization. -/
theorem actual_source_time_energy (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖sourceBranchFrequency n sharp advanced μ hμ q hq‖^2=
      (2*Real.pi)*‖sourceTime n sharp advanced μ hμ q hq‖^2 := by
  have hf := square_tendsto sourceFilter (frequencyFamily n sharp advanced μ hμ q hq)
  have ht := (square_tendsto sourceFilter (timeFamily n sharp advanced μ hμ q hq)).const_mul (2*Real.pi)
  have he (F : Index) : ‖value (frequencyFamily n sharp advanced μ hμ q hq) F‖^2=
      (2*Real.pi)*‖value (timeFamily n sharp advanced μ hμ q hq) F‖^2 :=
    actual_finite_time_energy F n sharp advanced μ hμ q hq
  have h := tendsto_nhds_unique hf (ht.congr' (Eventually.of_forall (fun F => (he F).symm)))
  simpa only [sourceBranchFrequency,sourceTime,UniformSpace.Completion.norm_coe] using h



private theorem finite_frequency_difference_square (F : Index) (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteFrequency F ell sharp advanced μ hμ q hq-finiteFrequency F m sharp advanced μ hμ q hq‖^2=
      ∫w : ℝ,‖branchInverse F ell sharp (frequency advanced μ w) (embed q)-
        branchInverse F m sharp (frequency advanced μ w) (embed q)‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (finiteFrequency F ell sharp advanced μ hμ q hq)
    (finiteFrequency F m sharp advanced μ hμ q hq),
    actual_finite_frequency_read F ell sharp advanced μ hμ q hq,
    actual_finite_frequency_read F m sharp advanced μ hμ q hq] with w hs he hm
  rw [hs,Pi.sub_apply,he,hm]

private theorem finite_time_difference_square (F : Index) (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) :
    ‖finiteTime F ell sharp advanced μ hμ q-finiteTime F m sharp advanced μ hμ q‖^2=
      ∫t : ℝ,‖wave F ell sharp advanced μ (embed q) t-wave F m sharp advanced μ (embed q) t‖^2 := by
  rw [FullYSourceCutoffTimeGraph.square_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (finiteTime F ell sharp advanced μ hμ q)
    (finiteTime F m sharp advanced μ hμ q),
    actual_finite_time_read F ell sharp advanced μ hμ q,
    actual_finite_time_read F m sharp advanced μ hμ q] with t hs he hm
  rw [hs,Pi.sub_apply,he,hm]

theorem actual_finite_time_difference_energy (F : Index) (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖finiteFrequency F ell sharp advanced μ hμ q hq-finiteFrequency F m sharp advanced μ hμ q hq‖^2=
      (2*Real.pi)*‖finiteTime F ell sharp advanced μ hμ q-finiteTime F m sharp advanced μ hμ q‖^2 := by
  rw [finite_frequency_difference_square,finite_time_difference_square]
  exact actual_absolute_time_difference_mass F m ell sharp advanced μ hμ (embed q)

/-- The actual whole-axis time family and full-frequency family have the same cutoff difference energy. -/
theorem actual_source_time_difference_energy (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖sourceBranchFrequency ell sharp advanced μ hμ q hq-sourceBranchFrequency m sharp advanced μ hμ q hq‖^2=
      (2*Real.pi)*‖sourceTime ell sharp advanced μ hμ q hq-sourceTime m sharp advanced μ hμ q hq‖^2 := by
  have hf := square_tendsto sourceFilter
    (frequencyFamily ell sharp advanced μ hμ q hq-frequencyFamily m sharp advanced μ hμ q hq)
  have ht := (square_tendsto sourceFilter
    (timeFamily ell sharp advanced μ hμ q hq-timeFamily m sharp advanced μ hμ q hq)).const_mul (2*Real.pi)
  have he (F : Index) :
      ‖value (frequencyFamily ell sharp advanced μ hμ q hq-frequencyFamily m sharp advanced μ hμ q hq) F‖^2=
      (2*Real.pi)*‖value (timeFamily ell sharp advanced μ hμ q hq-timeFamily m sharp advanced μ hμ q hq) F‖^2 :=
    actual_finite_time_difference_energy F m ell sharp advanced μ hμ q hq
  have h := tendsto_nhds_unique hf (ht.congr' (Eventually.of_forall (fun F => (he F).symm)))
  simpa only [sourceBranchFrequency,sourceTime,←UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe] using h

/-- Direct consumer of the previously generated primal family, with no Fourier or Cauchy premise. -/
theorem actual_original_family_time_difference_energy (m ell : ℕ) (advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    ‖sourceFrequency ell advanced μ hμ q hq-sourceFrequency m advanced μ hμ q hq‖^2=
      (2*Real.pi)*‖sourceTime ell false advanced μ hμ q hq-sourceTime m false advanced μ hμ q hq‖^2 := by
  simpa only [actual_primal_frequency] using
    actual_source_time_difference_energy m ell false advanced μ hμ q hq

theorem actual_time_energy_limit (n : ℕ) (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (q : QuantumTest) (hq : project (3,0) q=q) :
    Tendsto (fun F : Index => ∫t : ℝ,‖wave F n sharp advanced μ (embed q) t‖^2)
      sourceFilter (𝓝 (‖sourceTime n sharp advanced μ hμ q hq‖^2)) := by
  have h := (square_tendsto sourceFilter (timeFamily n sharp advanced μ hμ q hq)).congr'
    (Eventually.of_forall (fun F => finite_time_square F n sharp advanced μ hμ q))
  simpa only [sourceTime,UniformSpace.Completion.norm_coe] using h

theorem actual_time_difference_energy_limit (m ell : ℕ) (sharp advanced : Bool)
    (μ : ℝ) (hμ : 0<μ) (q : QuantumTest) (hq : project (3,0) q=q) :
    Tendsto (fun F : Index => ∫t : ℝ,
      ‖wave F ell sharp advanced μ (embed q) t-wave F m sharp advanced μ (embed q) t‖^2)
      sourceFilter
      (𝓝 (‖sourceTime ell sharp advanced μ hμ q hq-sourceTime m sharp advanced μ hμ q hq‖^2)) := by
  have h := (square_tendsto sourceFilter
    (timeFamily ell sharp advanced μ hμ q hq-timeFamily m sharp advanced μ hμ q hq)).congr'
      (Eventually.of_forall (fun F => finite_time_difference_square F m ell sharp advanced μ hμ q))
  simpa only [sourceTime,←UniformSpace.Completion.coe_sub,UniformSpace.Completion.norm_coe] using h

end LowEnergy.ActualThreeParticleCutoffTime
