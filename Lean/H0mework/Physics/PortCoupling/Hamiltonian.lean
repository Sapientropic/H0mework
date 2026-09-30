import H0mework.Physics.PortCoupling.Harmonic
import H0mework.Quantum.Generator.P257

/-!
# Self-adjoint Hamiltonian representation of the finite coupling

The real harmonic port flow is not a parallel physical theory.  Each ordered
pair `(source momentum, target position)` is real-linearly encoded as the
complex amplitude `target + i * source`.  Under that exact encoding,
`harmonicFlow t` is the repository's existing Schrödinger-sign scalar phase
flow with `omega = 1`.

Consequently the already installed coupling receipts have a faithful
representation by the existing self-adjoint Hamiltonian, skew-generator and
star-unitary certificate.  The representation is proved before the coupling
crown is consumed and contains no consciousness or body verdict.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open _root_.SaturationMonoid.AffineRelaxation
open Physical.Interface

noncomputable section

abbrev ComplexEmbodimentState := FiniteEmbodimentChannel → ℂ

/-- One port pair as the complex amplitude `position + i * momentum`. -/
def encodePort (ports : ℝ × ℝ) : ℂ :=
  (ports.2 : ℂ) + Complex.I * (ports.1 : ℂ)

/-- Position is the real coordinate and source momentum is the imaginary
coordinate. -/
def encodeComplex (state : FiniteEmbodimentState) :
    ComplexEmbodimentState :=
  fun channel => encodePort (state channel)

def decodeComplex (state : ComplexEmbodimentState) :
    FiniteEmbodimentState :=
  fun channel => ((state channel).im, (state channel).re)

@[simp] theorem decodeComplex_encodeComplex
    (state : FiniteEmbodimentState) :
    decodeComplex (encodeComplex state) = state := by
  funext channel
  rcases hstate : state channel with ⟨source, target⟩
  simp [decodeComplex, encodeComplex, encodePort, hstate]

@[simp] theorem encodeComplex_decodeComplex
    (state : ComplexEmbodimentState) :
    encodeComplex (decodeComplex state) = state := by
  funext channel
  rcases hstate : state channel with ⟨real, imaginary⟩
  apply Complex.ext <;>
    simp [decodeComplex, encodeComplex, encodePort, hstate]

/-- Exact real-linear carrier equivalence, not a lossy observation map. -/
def complexPortEquiv :
    FiniteEmbodimentState ≃ₗ[ℝ] ComplexEmbodimentState where
  toFun := encodeComplex
  invFun := decodeComplex
  left_inv := decodeComplex_encodeComplex
  right_inv := encodeComplex_decodeComplex
  map_add' := by
    intro left right
    funext channel
    apply Complex.ext <;>
      simp [encodeComplex, encodePort]
  map_smul' := by
    intro scalar state
    funext channel
    apply Complex.ext <;>
      simp [encodeComplex, encodePort]

theorem complexPortEquiv_apply (state : FiniteEmbodimentState) :
    complexPortEquiv state = encodeComplex state :=
  rfl

theorem schrodingerScalarPhase_one_eq (time : ℝ) :
    schrodingerScalarPhase 1 time =
      (Real.cos time : ℂ) - Complex.I * (Real.sin time : ℂ) := by
  simp only [schrodingerScalarPhase, unitComplexPhaseWithRate,
    unitComplexPhase, neg_mul, one_mul, Complex.ofReal_neg]
  rw [show Complex.I * -(time : ℂ) =
      ((-time : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_ofReal_mul_I]
  simp
  ring

/-- Exact channelwise conjugacy with scalar multiplication by `exp(-i t)`. -/
theorem encodePort_harmonicFlow (time : ℝ)
    (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    encodePort ((harmonicFlow time state) channel) =
      schrodingerScalarPhase 1 time • encodePort (state channel) := by
  rcases hstate : state channel with ⟨source, target⟩
  apply Complex.ext
  · rw [schrodingerScalarPhase_one_eq]
    simp [encodePort, harmonicFlow, sourcePort, targetPort, hstate,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    ring
  · rw [schrodingerScalarPhase_one_eq]
    simp [encodePort, harmonicFlow, sourcePort, targetPort, hstate,
      Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    ring

theorem encodeComplex_harmonicFlow (time : ℝ)
    (state : FiniteEmbodimentState) :
    encodeComplex (harmonicFlow time state) =
      schrodingerScalarPhase 1 time • encodeComplex state := by
  funext channel
  exact encodePort_harmonicFlow time state channel

theorem encodePort_harmonicFlowHom (time : ℝ)
    (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    encodePort ((harmonicFlow time state) channel) =
      schrodingerScalarPhaseFlowHom
        (E := ℂ) 1 (Multiplicative.ofAdd time)
          (encodePort (state channel)) := by
  rw [encodePort_harmonicFlow]
  simp [schrodingerScalarPhaseFlowHom,
    unitComplexPhaseWithRateFlowHom_apply,
    unitComplexPhaseWithRateLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul,
    schrodingerScalarPhase, unitComplexPhaseWithRate]

/-- The same conjugacy stated against the repository's bundled
Schrödinger-sign flow, channel by channel. -/
theorem encodeComplex_harmonicFlowHom (time : ℝ)
    (state : FiniteEmbodimentState) :
    encodeComplex (harmonicFlow time state) =
      fun channel =>
        schrodingerScalarPhaseFlowHom
          (E := ℂ) 1 (Multiplicative.ofAdd time)
            (encodeComplex state channel) := by
  funext channel
  rw [encodeComplex_harmonicFlow]
  simp only [Pi.smul_apply]
  simp [schrodingerScalarPhaseFlowHom,
    unitComplexPhaseWithRateFlowHom_apply,
    unitComplexPhaseWithRateLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul,
    schrodingerScalarPhase, unitComplexPhaseWithRate]

theorem encodeComplex_harmonicFlowHom_apply (time : ℝ)
    (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    encodeComplex (harmonicFlow time state) channel =
      schrodingerScalarPhaseFlowHom
        (E := ℂ) 1 (Multiplicative.ofAdd time)
          (encodeComplex state channel) :=
  congrFun (encodeComplex_harmonicFlowHom time state) channel

theorem channelEnergy_eq_complex_normSq
    (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    channelEnergy state channel =
      Complex.normSq (encodeComplex state channel) := by
  rcases hstate : state channel with ⟨source, target⟩
  simp [channelEnergy, encodeComplex, sourcePort, targetPort, hstate,
    encodePort, Complex.normSq]
  ring

abbrev HilbertEmbodimentState :=
  EuclideanSpace ℂ FiniteEmbodimentChannel

def encodeHilbert (state : FiniteEmbodimentState) :
    HilbertEmbodimentState :=
  WithLp.toLp 2 (encodeComplex state)

def decodeHilbert (state : HilbertEmbodimentState) :
    FiniteEmbodimentState :=
  decodeComplex (WithLp.ofLp state)

@[simp] theorem decodeHilbert_encodeHilbert
    (state : FiniteEmbodimentState) :
    decodeHilbert (encodeHilbert state) = state := by
  simp [decodeHilbert, encodeHilbert]

@[simp] theorem encodeHilbert_decodeHilbert
    (state : HilbertEmbodimentState) :
    encodeHilbert (decodeHilbert state) = state := by
  simp [decodeHilbert, encodeHilbert]

/-- The full ten-channel state, rather than one channel at a time, is exactly
a finite-dimensional complex Hilbert carrier. -/
def complexHilbertPortEquiv :
    FiniteEmbodimentState ≃ₗ[ℝ] HilbertEmbodimentState where
  toFun := encodeHilbert
  invFun := decodeHilbert
  left_inv := decodeHilbert_encodeHilbert
  right_inv := encodeHilbert_decodeHilbert
  map_add' := by
    intro left right
    ext channel
    apply Complex.ext <;>
      simp [encodeHilbert, encodeComplex, encodePort]
  map_smul' := by
    intro scalar state
    ext channel
    apply Complex.ext <;>
      simp [encodeHilbert, encodeComplex, encodePort]

theorem complexHilbertPortEquiv_apply (state : FiniteEmbodimentState) :
    complexHilbertPortEquiv state = encodeHilbert state :=
  rfl

theorem encodeHilbert_harmonicFlowHom (time : ℝ)
    (state : FiniteEmbodimentState) :
    encodeHilbert (harmonicFlow time state) =
      schrodingerScalarPhaseFlowHom
        (E := HilbertEmbodimentState) 1 (Multiplicative.ofAdd time)
          (encodeHilbert state) := by
  ext channel
  change encodeComplex (harmonicFlow time state) channel = _
  rw [encodeComplex_harmonicFlow]
  simp only [Pi.smul_apply]
  simp [schrodingerScalarPhaseFlowHom,
    unitComplexPhaseWithRateFlowHom_apply,
    unitComplexPhaseWithRateLinearIsometryEquiv_apply,
    relaxModule_zero_target_eq_residual_smul,
    schrodingerScalarPhase, unitComplexPhaseWithRate,
    encodeHilbert]

theorem harmonicHilbert_selfAdjointCertificate :
    SelfAdjointHamiltonianFlowCertificate HilbertEmbodimentState
      (schrodingerScalarPhaseFlowHom (E := HilbertEmbodimentState) 1)
      ((1 : ℂ) •
        (1 : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)) :=
  schrodingerScalarPhaseFlow_selfAdjointHamiltonianFlowCertificate
    (E := HilbertEmbodimentState) 1

theorem harmonicHilbert_boundedSchrodingerCertificate :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
      HilbertEmbodimentState
      ((1 : ℂ) •
        (1 : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)) := by
  apply boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
  simp

theorem energy_eq_encodeHilbert_norm_sq
    (state : FiniteEmbodimentState) :
    energy state = ‖encodeHilbert state‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold energy
  apply Finset.sum_congr rfl
  intro channel _membership
  rw [channelEnergy_eq_complex_normSq]
  rw [Complex.normSq_eq_norm_sq]
  rfl

/-- P257 supplies the bounded operator-exponential Schrödinger certificate
for the same identity Hamiltonian used by the conjugate scalar flow. -/
theorem finitePort_boundedSchrodingerCertificate :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate ℂ
      ((1 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  apply boundedSelfAdjointHamiltonianSchrodingerFlowCertificate
  simp

/-- Premise-free bridge from the exact real port carrier to the already
proved self-adjoint Hamiltonian/star-unitary flow, joined with the full
continuous coupling constructibility crown. -/
theorem sourceGeneratedFiniteSelfAdjointHamiltonianSignalCoupling_constructible :
    (∃ carrierEquiv :
        FiniteEmbodimentState ≃ₗ[ℝ] HilbertEmbodimentState,
      ∀ state, carrierEquiv state = encodeHilbert state) ∧
      Nonempty
        (SelfAdjointHamiltonianFlowCertificate HilbertEmbodimentState
          (schrodingerScalarPhaseFlowHom
            (E := HilbertEmbodimentState) 1)
          ((1 : ℂ) • (1 : HilbertEmbodimentState →L[ℂ]
            HilbertEmbodimentState))) ∧
      Nonempty
        (BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate
          HilbertEmbodimentState
          ((1 : ℂ) • (1 : HilbertEmbodimentState →L[ℂ]
            HilbertEmbodimentState))) ∧
      type_of% encodeHilbert_harmonicFlowHom ∧
      type_of% energy_eq_encodeHilbert_norm_sq ∧
      type_of% channelEnergy_eq_complex_normSq ∧
      type_of% sourceGeneratedFiniteHarmonicSignalCoupling_constructible := by
  exact ⟨⟨complexHilbertPortEquiv, complexHilbertPortEquiv_apply⟩,
    ⟨harmonicHilbert_selfAdjointCertificate⟩,
    ⟨harmonicHilbert_boundedSchrodingerCertificate⟩,
    encodeHilbert_harmonicFlowHom,
    energy_eq_encodeHilbert_norm_sq,
    channelEnergy_eq_complex_normSq,
    sourceGeneratedFiniteHarmonicSignalCoupling_constructible⟩

end


end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.encodeComplex_harmonicFlowHom
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.sourceGeneratedFiniteSelfAdjointHamiltonianSignalCoupling_constructible
