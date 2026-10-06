import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFiniteResolventEnergy
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceSupportLeakage

/-! The actual finite support and its retained escape leg pay one uniform frequency integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceActualResolventEnergy
open MeasureTheory GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceRetardedIncrement FullYSourceResolventGraphSplice SourceResolventLorentzian
open scoped InnerProductSpace

def supportAction (F : Index) : supportSpan F →L[ℂ] supportSpan F :=
  ((GaussGradedCompression.compression F).codRestrict (supportSpan F)
    (compression_mem_support F)).comp (supportSpan F).subtypeL

theorem support_action_selfAdjoint (F : Index) : IsSelfAdjoint (supportAction F) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  exact GaussGradedCompression.compression_pair F (x : H) (y : H)

theorem support_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (x : supportSpan F) :
    (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H)=
      finiteResolvent F z (x : H) := by
  have hs := congrArg (fun T : supportSpan F →L[ℂ] supportSpan F => T x)
    (resolvent_right (supportAction F) (support_action_selfAdjoint F) z hz)
  change supportAction F (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x)-
    z • FullYSourceResolventGraphSplice.resolvent (supportAction F) z x=x at hs
  have he := congrArg (fun y : supportSpan F => (y : H)) hs
  change GaussGradedCompression.compression F
      (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H)-
      z • (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H)=(x : H) at he
  have h := congrArg (fun T : H →L[ℂ] H => T
      (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H))
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F
      (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H)-
      z • (FullYSourceResolventGraphSplice.resolvent (supportAction F) z x : H))=_ at h
  rw [he] at h
  exact h.symm

theorem projection_norm_square (F : Index) (x : H) :
    ‖(supportSpan F).orthogonalProjectionOnto x‖^2+‖escapeProjection F x‖^2=‖x‖^2 := by
  have hx : escapeProjection F x+supportProjection F x=x := by
    change (x-(supportSpan F).starProjection x)+(supportSpan F).starProjection x=x
    abel
  have hp : inner ℂ (escapeProjection F x) (supportProjection F x)=0 :=
    (supportSpan F).starProjection_inner_eq_zero x _
      (Submodule.starProjection_apply_mem (supportSpan F) x)
  have hn := norm_add_sq (𝕜 := ℂ) (escapeProjection F x) (supportProjection F x)
  rw [hx,hp,map_zero,mul_zero,add_zero] at hn
  change ‖x‖^2=‖escapeProjection F x‖^2+‖(supportSpan F).orthogonalProjectionOnto x‖^2 at hn
  linarith

theorem actual_norm_square (F : Index) (μ t : ℝ) (hμ : 0<μ) (x : H) :
    ‖finiteResolvent F ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2=
      ‖FullYSourceResolventGraphSplice.resolvent (supportAction F)
        ((t : ℂ)+Complex.I*(μ : ℂ)) ((supportSpan F).orthogonalProjectionOnto x)‖^2+
        kernel μ 0 t*‖escapeProjection F x‖^2 := by
  have hz : ((t : ℂ)+Complex.I*(μ : ℂ)).im≠0 := by simpa using hμ.ne'
  rw [SourceRetardedIncrement.resolvent_norm_square F _ hz x]
  have hs := support_resolvent F _ hz ((supportSpan F).orthogonalProjectionOnto x)
  have hsNorm := congrArg (fun y : H => ‖y‖^2) hs
  change _=‖finiteResolvent F _ (supportProjection F x)‖^2 at hsNorm
  rw [←hsNorm]
  have hc := inverse_norm_square μ 0 t
  simpa only [Complex.ofReal_zero,zero_sub,norm_inv,norm_neg] using!
    congrArg (fun r : ℝ => ‖FullYSourceResolventGraphSplice.resolvent (supportAction F)
      ((t : ℂ)+Complex.I*(μ : ℂ)) ((supportSpan F).orthogonalProjectionOnto x)‖^2+
        r*‖escapeProjection F x‖^2) hc

theorem actual_square_integrable (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    Integrable (fun t : ℝ => ‖finiteResolvent F ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2) := by
  simp_rw [actual_norm_square F μ _ hμ x]
  exact (SourceFiniteResolventEnergy.resolvent_square_integrable (supportAction F)
    (support_action_selfAdjoint F) μ hμ ((supportSpan F).orthogonalProjectionOnto x)).add
      ((kernel_integrable μ 0 hμ).mul_const _)

theorem actual_square_integral (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫ t : ℝ, ‖finiteResolvent F ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2)=Real.pi/μ*‖x‖^2 := by
  simp_rw [actual_norm_square F μ _ hμ x]
  rw [integral_add (SourceFiniteResolventEnergy.resolvent_square_integrable (supportAction F)
      (support_action_selfAdjoint F) μ hμ ((supportSpan F).orthogonalProjectionOnto x))
      ((kernel_integrable μ 0 hμ).mul_const _),
    SourceFiniteResolventEnergy.resolvent_square_integral _ (support_action_selfAdjoint F) μ hμ,
    integral_mul_const,kernel_integral μ 0 hμ,←mul_add,projection_norm_square]

theorem actual_square_lintegral (F : Index) (μ : ℝ) (hμ : 0<μ) (x : H) :
    (∫⁻ t : ℝ, ENNReal.ofReal (‖finiteResolvent F ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (actual_square_integrable F μ hμ x)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),actual_square_integral F μ hμ x]

end LowEnergy.SourceActualResolventEnergy
