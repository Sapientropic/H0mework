import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockWindowTime
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusHalfSeedTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockFixedInputSeed
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceCoframeDilation
open SourceClockAcceleration SourceRadiusHalfWindow SourceRadiusHalfHamiltonian SourceRadiusHalfResponse
open SourceRadiusHalfSeedTail SourceScalarPositiveBulkWard SourceJointResidualEnergy SourceRetardedIncrement
open SourceActualResolventEnergy SourceInverseElectricMomentChannels FullYSourceResolventGraphSplice
open SourceScalarPairedTransport
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem half_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (halfAction m ell q)=sourcePair (halfAction m ell p) q := multiply_pair _ _ _ _

private theorem real_half (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z:ℂ) (halfCoefficient m ell z:ℂ) (f z)

private theorem volume_half (m ell : ℕ) : Commute volumeAction (halfAction m ell) := real_half _ _ _ _
private theorem inverse_half (m ell : ℕ) : Commute inverseVolumeAction (halfAction m ell) := real_half _ _ _ _

private theorem contact_volume (m ell : ℕ) (v : Ambient) : Commute (halfContact v m ell) volumeAction :=
  (scalar_volume_commutes _ _).mul_left (SourceHamiltonianVolume.real_volume _ _)

private theorem radial_volume (m ell : ℕ) : Commute (radialAction m ell) volumeAction := by
  unfold radialAction radialTerm
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact ((SourceHamiltonianVolume.native_adjoint_volume (scalarDirection a)).mul_left
    ((SourceHamiltonianVolume.real_volume _ _).mul_left (contact_volume m ell _))).add_left
      ((contact_volume m ell _).mul_left ((SourceHamiltonianVolume.real_volume _ _).mul_left
        (SourceHamiltonianVolume.native_momentum_volume (scalarDirection a))))

private theorem dilation_half (m ell : ℕ) : Commute dilation (halfAction m ell) := by
  have hh : diagonalAction*halfAction m ell-halfAction m ell*diagonalAction=radialAction m ell := by
    rw [original_diagonal_current,add_sub_cancel_left]
  have hu := (volume_half m ell).eq
  have hr := (radial_volume m ell).eq
  have hc : (diagonalAction*volumeAction-volumeAction*diagonalAction)*halfAction m ell-
      halfAction m ell*(diagonalAction*volumeAction-volumeAction*diagonalAction)=0 := by
    linear_combination (norm := noncomm_ring)
      diagonalAction*hu-hu*diagonalAction+hh*volumeAction-volumeAction*hh+hr
  rw [SourceHamiltonianVolume.full_source_volume_current,smul_mul_assoc,mul_smul_comm,←smul_sub] at hc
  have hn : (-3*Complex.I*(sourceTime 0:ℂ)/4)≠0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast lapse_pos.ne')
    · norm_num
  exact sub_eq_zero.mp ((smul_eq_zero.mp hc).resolve_left hn)

/-- The actual symmetric inverse-volume/dilation source word pays the full clock current pairing. -/
theorem original_clock_current_pair (f g : QuantumTest) :
    sourcePair f (clockCurrent g)=sourcePair (clockCurrent f) g := by
  have hV (a b : QuantumTest) : sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b :=
    multiply_pair _ _ _ _
  rw [original_clock_current]
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_smul,map_add,
    inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,map_div₀,map_mul,map_ofNat,Complex.conj_ofReal]
  change _*(sourcePair f (inverseVolumeAction (dilation g))+sourcePair f (dilation (inverseVolumeAction g)))=
    _*(sourcePair (inverseVolumeAction (dilation f)) g+sourcePair (dilation (inverseVolumeAction f)) g)
  rw [hV,SourceCoframeDilation.dilation_pair,SourceCoframeDilation.dilation_pair,←hV]
  ring

/-- The same coframe/scalar source commutators generate clock-current commutation with the half radius window. -/
theorem original_clock_half_commute (m ell : ℕ) : Commute clockCurrent (halfAction m ell) := by
  rw [original_clock_current]
  exact (((inverse_half m ell).mul_left (dilation_half m ell)).add_left
    ((dilation_half m ell).mul_left (inverse_half m ell))).smul_left _

def fixedClockSeed (m ell : ℕ) (g : QuantumTest) : ℝ :=
  (sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell g))).re

private theorem clock_current_real (f : QuantumTest) : (sourcePair f (clockCurrent f)).im=0 := by
  have h := congrArg Complex.im (pair_conjugate f (clockCurrent f))
  rw [←original_clock_current_pair] at h
  simp only [Complex.conj_im] at h
  linarith

/-- The fixed source current has a real mass, before any finite compression or frequency is chosen. -/
theorem original_fixed_clock_seed_real (m ell : ℕ) (g : QuantumTest) :
    sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell g))=(fixedClockSeed m ell g:ℂ) := by
  apply Complex.ext
  · rfl
  · change (sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell g))).im=0
    exact clock_current_real _

/-- Both fixed original inputs g and Jg pay this clock seed on the same cutoff, before F and either causal leg. -/
theorem original_fixed_clock_seed_tail (g : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell : ℕ,|fixedClockSeed m ell g| ≤ ε := by
  intro ε hε
  obtain ⟨Ng,hg⟩ := original_half_seed_tail g ε hε
  obtain ⟨Nj,hj⟩ := original_half_seed_tail (clockCurrent g) ε hε
  refine ⟨max Ng Nj,fun m hm ell => ?_⟩
  have hgs := hg m ((le_max_left _ _).trans hm) ell
  have hjs := hj m ((le_max_right _ _).trans hm) ell
  have he := LinearMap.congr_fun (original_clock_half_commute m ell).eq g
  change clockCurrent (halfAction m ell g)=halfAction m ell (clockCurrent g) at he
  unfold fixedClockSeed
  rw [he]
  have hc := (Complex.abs_re_le_norm (sourcePair (halfAction m ell g) (halfAction m ell (clockCurrent g)))).trans
    (norm_inner_le_norm (𝕜 := ℂ) (embed (halfAction m ell g)) (embed (halfAction m ell (clockCurrent g))))
  nlinarith only [hc,hgs,hjs,sq_nonneg
    (‖embed (halfAction m ell g)‖-‖embed (halfAction m ell (clockCurrent g))‖)]

private theorem fixed_pair_return (m ell : ℕ) (g q : QuantumTest) :
    sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell q))=
      sourcePair (halfAction m ell (clockCurrent (halfAction m ell g))) q :=
  (original_clock_current_pair _ _).trans (half_pair _ _ _ _)

/-- A fixed source vector for the actual finite resolvent, with both source operators already applied. -/
def fixedClockInput (m ell : ℕ) (g : QuantumTest) : H :=
  embed (halfAction m ell (clockCurrent (halfAction m ell g)))

def fixedClockCoefficient (F : Index) (m ell : ℕ) (g : QuantumTest) (i : Channel F) : ℂ :=
  inner ℂ (fixedClockInput m ell g) (channel F i (embed g))

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    embed (state F z hz (coreEquiv g))=finiteResolvent F z (embed g) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply (SourceEscapeCurrent.sourceCore F z hz (coreEquiv g)))

/-- The original current/fixed-input pairing returns its complete same-F spectral coefficients, including escape. -/
theorem actual_fixed_clock_channels (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    sourcePair (halfAction m ell g) (clockCurrent (halfAction m ell (state F z hz (coreEquiv g))))=
      ∑ i : Channel F,((channelValue F i:ℂ)-z)⁻¹*fixedClockCoefficient F m ell g i := by
  rw [fixed_pair_return]
  change inner ℂ (fixedClockInput m ell g) (embed (state F z hz (coreEquiv g)))=_
  rw [state_embed F z hz g,actual_channels F z hz (embed g),inner_sum]
  simp only [inner_smul_right,fixedClockCoefficient]

private theorem channel_resolution (F : Index) (g : H) : ∑ i : Channel F,channel F i g=g := by
  rw [Fintype.sum_option]
  simp only [channel]
  have hs := congrArg (supportSpan F).subtypeL
    ((sourceBasis F).sum_repr ((supportSpan F).orthogonalProjectionOnto g))
  simp only [map_sum,map_smul] at hs
  change escapeProjection F g+(∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i:H))=g
  change (∑ i,(sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto g) i • ((sourceBasis F) i:H))=
    ((supportSpan F).orthogonalProjectionOnto g:H) at hs
  rw [hs]
  change (g-(supportSpan F).starProjection g)+(supportSpan F).starProjection g=g
  abel

/-- Real total coefficient mass is generated by the fixed clock seed; individual channel phases remain independent. -/
theorem original_fixed_clock_coefficient_mass (F : Index) (m ell : ℕ) (g : QuantumTest) :
    (∑ i : Channel F,fixedClockCoefficient F m ell g i)=(fixedClockSeed m ell g:ℂ) := by
  unfold fixedClockCoefficient
  rw [←inner_sum,channel_resolution]
  change sourcePair (halfAction m ell (clockCurrent (halfAction m ell g))) g=(fixedClockSeed m ell g:ℂ)
  rw [←fixed_pair_return]
  exact original_fixed_clock_seed_real _ _ _

end LowEnergy.SourceClockFixedInputSeed
