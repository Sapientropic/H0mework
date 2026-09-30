import H0mework.Physics.LowEnergy.FullQuantum.TriangularResolvent

/-! The Hamiltonian resolvent returns through the original C0 to the
independent-dual Dirac symbol, preserving its source normalization. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

def diracKernel (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  (-Complex.I*z) • currentCoframeMatterTemporalPrincipal (C.coframe p) + lowerSymbol C p k

def diracResolvent (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ) : Mother :=
  Complex.I • (fullResolvent C p k z * currentCoframeMatterTemporalPrincipalInverse (C.coframe p))

theorem diracKernel_factor (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe p) ≠ 0) :
    diracKernel C p k z = (-Complex.I) •
      (currentCoframeMatterTemporalPrincipal (C.coframe p) * fullKernel C p k z) := by
  apply LinearMap.ext
  intro v
  have lower : lowerSymbol C p k v = -currentCoframeMatterTemporalPrincipal (C.coframe p)
      (drift C p k v) := by
    have generated := dualDrift_original C p k noncharacteristic
      (currentCoframeMatterTemporalPrincipal (C.coframe p) v)
    simpa only [dualDrift, LinearMap.comp_apply,
      currentCoframeMatterTemporalPrincipalInverse_left _ noncharacteristic] using generated
  change (-Complex.I*z) • currentCoframeMatterTemporalPrincipal (C.coframe p) v + lowerSymbol C p k v =
    (-Complex.I) • currentCoframeMatterTemporalPrincipal (C.coframe p)
      (z • v - hamiltonian C p k v)
  rw [lower, map_sub, map_smul]
  simp only [hamiltonian, LinearMap.smul_apply, map_smul, smul_sub, smul_smul]
  simp [Complex.I_mul_I]
  abel

theorem diracResolvent_two_sided (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (k : Fin 3 → ℝ) (z : ℂ)
    (noncharacteristic : coframeTemporalPrincipalScalar (C.coframe p) ≠ 0)
    (regular : IsUnit (freeKernel C p k z)) :
    diracKernel C p k z * diracResolvent C p k z = 1 ∧
      diracResolvent C p k z * diracKernel C p k z = 1 := by
  have principalLeft : currentCoframeMatterTemporalPrincipalInverse (C.coframe p) *
      currentCoframeMatterTemporalPrincipal (C.coframe p) = 1 := by
    apply LinearMap.ext
    intro v
    change currentCoframeMatterTemporalPrincipalInverse (C.coframe p)
      (currentCoframeMatterTemporalPrincipal (C.coframe p) v) = v
    exact currentCoframeMatterTemporalPrincipalInverse_left (C.coframe p) noncharacteristic v
  have principalRight : currentCoframeMatterTemporalPrincipal (C.coframe p) *
      currentCoframeMatterTemporalPrincipalInverse (C.coframe p) = 1 := by
    apply LinearMap.ext
    intro v
    change currentCoframeMatterTemporalPrincipal (C.coframe p)
      (currentCoframeMatterTemporalPrincipalInverse (C.coframe p) v) = v
    exact currentCoframeMatterTemporalPrincipalInverse_right (C.coframe p) noncharacteristic v
  have inverse := fullResolvent_two_sided C p k z regular
  rw [diracKernel_factor C p k z noncharacteristic, diracResolvent]
  constructor
  · rw [smul_mul_smul]
    have product : (currentCoframeMatterTemporalPrincipal (C.coframe p) * fullKernel C p k z) *
        (fullResolvent C p k z * currentCoframeMatterTemporalPrincipalInverse (C.coframe p)) = 1 := by
      rw [mul_assoc, ← mul_assoc (fullKernel C p k z), inverse.1, one_mul, principalRight]
    rw [product]
    simp
  · rw [smul_mul_smul]
    have product : (fullResolvent C p k z * currentCoframeMatterTemporalPrincipalInverse (C.coframe p)) *
        (currentCoframeMatterTemporalPrincipal (C.coframe p) * fullKernel C p k z) = 1 := by
      rw [mul_assoc, ← mul_assoc (currentCoframeMatterTemporalPrincipalInverse (C.coframe p)),
        principalLeft, one_mul, inverse.2]
    rw [product]
    simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular
