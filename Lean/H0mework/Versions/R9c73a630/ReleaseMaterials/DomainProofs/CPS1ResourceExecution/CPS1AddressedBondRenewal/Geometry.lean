import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondResponse.Motion
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedRenewal.Renewal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondRenewal
noncomputable section
open CPS1Deformation CPS1AddressedBondResponse
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

private theorem leading_none (q : CPS1AddressedBondResponse.Generic.Quartic) :
    q.leading? = none ↔ q.c1 = 0 ∧ q.c2 = 0 ∧ q.c3 = 0 ∧ q.c4 = 0 := by
  classical
  by_cases first : q.c1 = 0 <;> by_cases second : q.c2 = 0 <;>
    by_cases third : q.c3 = 0 <;> by_cases fourth : q.c4 = 0 <;>
    simp [CPS1AddressedBondResponse.Generic.Quartic.leading?,first,second,third,fourth]

private theorem sum_squares_zero (field : Fin 3 → ℝ)
    (zero : (∑ axis : Fin 3, (field axis)^2) = 0) : field = 0 := by
  funext axis
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun index _ => sq_nonneg (field index))).mp zero axis (Finset.mem_univ axis))

theorem distance_polynomial_none (state : Material frame) (site : BridgeSite state.reference) :
    (distancePolynomial state site).leading? = none ↔
      relativeVelocity state site = 0 ∧ relativeQuadratic state site = 0 := by
  rw [leading_none]
  constructor
  · intro coefficients
    have acceleration : relativeQuadratic state site = 0 := sum_squares_zero _ coefficients.2.2.2
    have speedSquares : (∑ axis : Fin 3, (relativeVelocity state site axis)^2) = 0 := by
      simpa only [distancePolynomial,acceleration,Pi.zero_apply,mul_zero,add_zero] using coefficients.2.1
    exact ⟨sum_squares_zero _ speedSquares,acceleration⟩
  · rintro ⟨velocity,acceleration⟩
    simp [distancePolynomial,velocity,acceleration]

theorem renewed_relative_velocity (state : Material frame)
    (site : BridgeSite state.reference) (time : ℝ) :
    relativeVelocity (CPS1AddressedRenewal.renewedMaterial state time) site =
      relativeVelocity state site+(2*time) • relativeQuadratic state site := by
  funext axis
  change
    (state.momenta site.phosphate.nuclear axis+time*state.jointForce site.phosphate.nuclear axis) /
      CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear -
    (state.momenta site.oxygenNuclear axis+time*state.jointForce site.oxygenNuclear axis) /
      CPS1MolecularFrame.inertia state.reference site.oxygenNuclear =
    (state.momenta site.phosphate.nuclear axis / CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear -
      state.momenta site.oxygenNuclear axis / CPS1MolecularFrame.inertia state.reference site.oxygenNuclear) +
    (2*time)*(state.jointForce site.phosphate.nuclear axis /
      (2*CPS1MolecularFrame.inertia state.reference site.phosphate.nuclear) -
      state.jointForce site.oxygenNuclear axis / (2*CPS1MolecularFrame.inertia state.reference site.oxygenNuclear))
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

theorem renewed_velocity_eventually_nonzero (state : Material frame)
    (site : BridgeSite state.reference) (degree : CPS1AddressedBondResponse.Generic.Degree)
    (generated : (distancePolynomial state site).leading? = some degree) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time →
      relativeVelocity (CPS1AddressedRenewal.renewedMaterial state time) site ≠ 0 := by
  by_cases velocityZero : relativeVelocity state site = 0
  · have accelerationNonzero : relativeQuadratic state site ≠ 0 := by
      intro accelerationZero
      have absent := (distance_polynomial_none state site).mpr ⟨velocityZero,accelerationZero⟩
      rw [generated] at absent
      cases absent
    exact Filter.Eventually.of_forall fun time positive => by
      rw [renewed_relative_velocity,velocityZero,zero_add]
      exact smul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt positive)) accelerationNonzero
  · have continuous : ContinuousAt
        (fun time : ℝ => relativeVelocity state site+(2*time) • relativeQuadratic state site) 0 :=
      continuousAt_const.add ((continuousAt_const.mul continuousAt_id).smul continuousAt_const)
    have remains := continuous.eventually_ne (by simpa using velocityZero)
    filter_upwards [remains] with time nonzero
    intro _
    simpa only [renewed_relative_velocity] using nonzero

theorem velocity_generates_leading (state : Material frame) (site : BridgeSite state.reference)
    (nonzero : relativeVelocity state site ≠ 0) :
    ∃ degree, (distancePolynomial state site).leading? = some degree := by
  cases generated : (distancePolynomial state site).leading? with
  | none => exact False.elim (nonzero ((distance_polynomial_none state site).mp generated).1)
  | some degree => exact ⟨degree,rfl⟩

end
end CPS1AddressedBondRenewal
