import H0mework.Quantum.Generator.P251

/-!
# Proposition 252: isometric-flow conservation certificate

P250-P251 describe generator and Hamiltonian normal-form certificates for
flows whose time slices are bundled linear isometric automorphisms
`E ≃ₗᵢ[ℂ] E`.

This file records the conservation laws that come from that carrier choice:
every such flow preserves norms, pairwise distances, and zero.  These laws are
also inherited by time-rescaled flows and by Hamiltonian normal-form
certificates.

Boundary: this still does not prove Stone's theorem, self-adjointness, or that
a concrete physical system supplies a unitary flow.  It only proves the
conservation surface already forced by the certified flow type.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Conservation laws for bundled isometric flows -/

/-- The conservation laws forced by a one-parameter flow valued in bundled
linear isometric automorphisms. -/
structure IsometricFlowConservationCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) : Prop where
  norm_orbit :
    ∀ t : ℝ, ∀ x : E,
      ‖U (Multiplicative.ofAdd t) x‖ = ‖x‖
  dist_orbit :
    ∀ t : ℝ, ∀ x y : E,
      dist (U (Multiplicative.ofAdd t) x)
        (U (Multiplicative.ofAdd t) y) = dist x y
  zero_orbit :
    ∀ t : ℝ,
      U (Multiplicative.ofAdd t) (0 : E) = 0

/-- Any bundled flow into `E ≃ₗᵢ[ℂ] E` preserves norms along every point
orbit. -/
theorem isometricFlow_norm_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) (x : E) :
    ‖U (Multiplicative.ofAdd t) x‖ = ‖x‖ := by
  simp

/-- Any bundled flow into `E ≃ₗᵢ[ℂ] E` preserves pairwise distances. -/
theorem isometricFlow_dist_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) (x y : E) :
    dist (U (Multiplicative.ofAdd t) x)
      (U (Multiplicative.ofAdd t) y) = dist x y := by
  simp

/-- Any bundled linear isometric flow fixes zero at every time. -/
theorem isometricFlow_zero_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (t : ℝ) :
    U (Multiplicative.ofAdd t) (0 : E) = 0 := by
  simp

/-- Bundle the conservation laws for any flow valued in linear isometric
automorphisms. -/
theorem isometricFlowConservationCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) :
    IsometricFlowConservationCertificate E U where
  norm_orbit := isometricFlow_norm_orbit U
  dist_orbit := isometricFlow_dist_orbit U
  zero_orbit := isometricFlow_zero_orbit U

/-! ## Stability under time rescaling and generator/Hamiltonian certificates -/

/-- Time-rescaled bundled flows inherit the same isometric conservation laws. -/
theorem isometricFlowConservationCertificate_timeRescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (omega : ℝ) :
    IsometricFlowConservationCertificate E
      (timeRescaledFlowHom (E := E) U omega) :=
  isometricFlowConservationCertificate
    (timeRescaledFlowHom (E := E) U omega)

/-- A continuous-linear-generator certificate carries the conservation laws of
its bundled isometric flow. -/
theorem LinearGeneratorFlowCertificate.toIsometricConservation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (_hU : LinearGeneratorFlowCertificate E U A) :
    IsometricFlowConservationCertificate E U :=
  isometricFlowConservationCertificate U

/-- A Hamiltonian normal-form certificate carries the conservation laws of its
bundled isometric flow. -/
theorem HamiltonianNormalFormFlowCertificate.toIsometricConservation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Multiplicative ℝ →* E ≃ₗᵢ[ℂ] E) (H : E →L[ℂ] E)
    (_hU : HamiltonianNormalFormFlowCertificate E U H) :
    IsometricFlowConservationCertificate E U :=
  isometricFlowConservationCertificate U

/-- The scalar Schrödinger sign-convention slice preserves norms, distances,
and zero because it is a bundled linear isometric flow. -/
theorem schrodingerScalarPhaseFlow_isometricConservationCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (omega : ℝ) :
    IsometricFlowConservationCertificate E
      (schrodingerScalarPhaseFlowHom (E := E) omega) :=
  isometricFlowConservationCertificate
    (schrodingerScalarPhaseFlowHom (E := E) omega)


end

end AffineRelaxation
end SaturationMonoid
