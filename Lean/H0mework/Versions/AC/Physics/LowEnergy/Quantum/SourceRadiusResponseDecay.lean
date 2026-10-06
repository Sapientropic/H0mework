import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceRadiusClosedJointCost
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNoetherChannelGap
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussRadialHamiltonian
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussAdjointHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusResponseDecay
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport
open GaussRadialDomain SourceEscapeCurrent SourceScalarPositiveBulkWard SourceResolventBandLimit
open FullYSourceResolventGraphSplice SourceRetardedIncrement Filter
open scoped InnerProductSpace
abbrev Op := H →L[ℂ] H
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def inverseSeed (g : diagonal.domain) : diagonal.domain :=
  coreEquiv (inverseAction (coreEquiv.symm g))
private theorem inverse_seed_coe (g : diagonal.domain) :
    (inverseSeed g : H)=inverseRadius (g : H) := by
  change embed (inverseAction (coreEquiv.symm g))=_
  rw [←inverse_core]
  exact congrArg inverseRadius (congrArg Subtype.val (coreEquiv.apply_symm_apply g))

/-- The original finite compression, including its full source defect. -/
def radialCurrent (F : Index) : End := GaussRadialHamiltonian.radialAction-
  (defectAction F*inverseAction-inverseAction*defectAction F)

theorem original_radial_current (F : Index) :
    radialCurrent F=compressionCore F*inverseAction-inverseAction*compressionCore F := by
  have h := GaussRadialHamiltonian.diagonal_commutator
  unfold radialCurrent defectAction
  linear_combination (norm := noncomm_ring) -h

/-- Actual double resolvent of the corrected current; no finite compression commutation is assumed. -/
def response (F : Index) (z : ℂ) (x : H) : H :=
  finiteResolvent F z ((GaussGradedCompression.compression F*inverseRadius-
    inverseRadius*GaussGradedCompression.compression F) (finiteResolvent F z x))

private theorem resolvent_commutator (C S : Op) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) :
    FullYSourceResolventGraphSplice.resolvent C z*(C*S-S*C)*FullYSourceResolventGraphSplice.resolvent C z=S*FullYSourceResolventGraphSplice.resolvent C z-FullYSourceResolventGraphSplice.resolvent C z*S := by
  have hl := resolvent_compression C hC z hz
  have hr : C*FullYSourceResolventGraphSplice.resolvent C z=1+z • FullYSourceResolventGraphSplice.resolvent C z := by
    have h := resolvent_right C hC z hz
    simp only [sub_mul,smul_mul_assoc,one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  calc
    _=(FullYSourceResolventGraphSplice.resolvent C z*C)*S*FullYSourceResolventGraphSplice.resolvent C z-FullYSourceResolventGraphSplice.resolvent C z*S*(C*FullYSourceResolventGraphSplice.resolvent C z) := by noncomm_ring
    _=_ := by
      rw [hl,hr]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,mul_assoc]
      abel

theorem actual_response_difference (F : Index) (z : ℂ) (hz : z.im≠0) (x : H) :
    response F z x=inverseRadius (finiteResolvent F z x)-finiteResolvent F z (inverseRadius x) :=
  congrArg (fun A : Op => A x)
    (resolvent_commutator _ _ (GaussGradedCompression.compression_selfAdjoint F) z hz)

private theorem step_coe (g : diagonal.domain) : (GaussAdjointHistory.coreStep g : H)=diagonal g := rfl

private theorem source_second_expansion (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ,∀ _hz : z.im≠0,
      z^2 • finiteResolvent F z (g : H)=
        finiteResolvent F z (diagonal (GaussAdjointHistory.coreStep g))-diagonal g-z • (g : H) := by
  filter_upwards [GaussGradedCompression.eventually_exact g,
    GaussGradedCompression.eventually_exact (GaussAdjointHistory.coreStep g)] with F hg hh z hz
  have h1 := congrArg (fun A : Op => A (g : H))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  have h2 := congrArg (fun A : Op => A (GaussAdjointHistory.coreStep g : H))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (g : H))=
    (g : H)+z • finiteResolvent F z (g : H) at h1
  change finiteResolvent F z (GaussGradedCompression.compression F (GaussAdjointHistory.coreStep g : H))=
    (GaussAdjointHistory.coreStep g : H)+z • finiteResolvent F z (GaussAdjointHistory.coreStep g : H) at h2
  rw [hg] at h1
  rw [hh,step_coe] at h2
  rw [h2,h1]
  module

attribute [local irreducible] response inverseSeed inverseRadius diagonal diagonalAction GaussAdjointHistory.coreStep finiteResolvent

private theorem second_difference (S R : Op) (z : ℂ) (g h a b c d : H)
    (hinv : S g=h) (hg : z^2 • R g=R b-a-z • g) (hh : z^2 • R h=R d-c-z • h) :
    z^2 • (S (R g)-R (S g))=(c-S a)+S (R b)-R d := by
  rw [smul_sub,←map_smul,hg,map_sub,map_sub,map_smul,hinv,hh]
  abel

/-- Only fixed original inputs and their H-prefixes enter the common event; the entire moving response remains intact. -/
theorem actual_response_second_expansion (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ,∀ _hz : z.im≠0,
      z^2 • response F z (g : H)=
        (diagonal (inverseSeed g)-inverseRadius (diagonal g))+
        inverseRadius (finiteResolvent F z (diagonal (GaussAdjointHistory.coreStep g)))-
        finiteResolvent F z (diagonal (GaussAdjointHistory.coreStep (inverseSeed g))) := by
  filter_upwards [source_second_expansion g,source_second_expansion (inverseSeed g)] with F hg hi z hz
  calc
    _=z^2 • (inverseRadius (finiteResolvent F z (g : H))-finiteResolvent F z (inverseRadius (g : H))) :=
      congrArg (fun x : H => z^2 • x) (actual_response_difference F z hz (g : H))
    _=_ := second_difference inverseRadius (finiteResolvent F z) z
      (g : H) (inverseSeed g : H) (diagonal g) (diagonal (GaussAdjointHistory.coreStep g))
      (diagonal (inverseSeed g)) (diagonal (GaussAdjointHistory.coreStep (inverseSeed g)))
      (inverse_seed_coe g).symm (hg z hz) (hi z hz)

/-- A source-owned far-frequency price; it contains no moving graph norm and no norm of C_F. -/
def decayPrice (μ : ℝ) (g : diagonal.domain) : ℝ :=
  ‖diagonal (inverseSeed g)-inverseRadius (diagonal g)‖+
  ‖inverseRadius‖*(μ⁻¹*‖diagonal (GaussAdjointHistory.coreStep g)‖)+
  μ⁻¹*‖diagonal (GaussAdjointHistory.coreStep (inverseSeed g))‖

private theorem square_smul_bound (z : ℂ) (x y : H) (C : ℝ) (hz : z≠0)
    (h : z^2 • x=y) (hy : ‖y‖≤C) : ‖x‖ ≤ ‖z‖⁻¹^2*C := by
  have he : x=(z^2)⁻¹ • y := by
    rw [←h,smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 hz),one_smul]
  rw [he,norm_smul,norm_inv,norm_pow,←inv_pow]
  exact mul_le_mul_of_nonneg_left hy (sq_nonneg _)

/-- The complete corrected double response has inverse-square decay in both nonreal half-planes. -/
theorem actual_response_decay (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ z : ℂ, |z.im|=μ →
      ‖response F z (g : H)‖ ≤ ‖z‖⁻¹^2*decayPrice μ g := by
  filter_upwards [actual_response_second_expansion g] with F hF z hz
  have hzi : z.im≠0 := abs_pos.mp (hz.symm ▸ hμ)
  have hz0 : z≠0 := by intro he;apply hzi;rw [he];rfl
  have bound (x : H) : ‖finiteResolvent F z x‖ ≤ μ⁻¹*‖x‖ := by
    exact ((finiteResolvent F z).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by simpa only [hz,one_div] using
        (finite_resolvent_norm F z hzi)) (norm_nonneg x))
  apply square_smul_bound z _ _ (decayPrice μ g) hz0 (hF z hzi)
  unfold decayPrice
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl
      ((inverseRadius.le_opNorm _).trans (mul_le_mul_of_nonneg_left (bound _) (norm_nonneg _)))))
    (bound _))

end LowEnergy.SourceRadiusResponseDecay
