import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97CommonPrincipal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97NoetherFraction

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97ClockOrder
open Polynomial Filter Set CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedOrderedStatic ActualDressedUniformMaterialCoefficients ActualDressedEMTensorClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedN3EMAnalyticPrice
open scoped Topology Matrix

private theorem specialize_coefficient (P : (ℂ[X])[X]) (eps : ℝ) (k : ℕ) :
    (clockSpecialize eps P).coeff k=(P.coeff k).eval (eps:ℂ) := by
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,Polynomial.coe_evalRingHom]

private theorem specialize_order (P : (ℂ[X])[X]) (eps : ℝ)
    (leading : (P.coeff P.natTrailingDegree).eval (eps:ℂ)≠0) :
    (clockSpecialize eps P).natTrailingDegree=P.natTrailingDegree := by
  have nonzero : clockSpecialize eps P≠0 := by
    intro zero
    apply leading
    rw [←specialize_coefficient,zero,coeff_zero]
  apply le_antisymm
  · by_contra high
    have low : P.natTrailingDegree<(clockSpecialize eps P).natTrailingDegree := Nat.lt_of_not_ge high
    apply leading
    rw [←specialize_coefficient,coeff_eq_zero_of_lt_natTrailingDegree low]
  · apply le_natTrailingDegree nonzero
    intro k low
    rw [specialize_coefficient,coeff_eq_zero_of_lt_natTrailingDegree low,eval_zero]

private theorem bivariate_clock_order_stable (P : (ℂ[X])[X]) (nonzero : P≠0) :
    ∀ᶠ eps : ℝ in 𝓝[>] 0,
      (clockSpecialize eps P).natTrailingDegree=P.natTrailingDegree := by
  have leading : P.coeff P.natTrailingDegree≠0 := coeff_natTrailingDegree_ne_zero.mpr nonzero
  have inclusion : Ioi (0:ℝ)⊆{0}ᶜ := fun eps positive => by simpa using positive.ne'
  have chart := (source_static_punctured_chart (P.coeff P.natTrailingDegree) leading).filter_mono
    (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart] with eps regular
  exact specialize_order P eps regular

attribute [local irreducible] Matrix.det sourceSchur97Polynomial sourceClockEval

private theorem original_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    (sourceSchur97Polynomial event n).det≠0 := by
  have point := (source_schur97_polynomial_original_regular_iff event n eps sigma unit positive small damping).mpr regular
  intro zero
  apply point
  rw [zero,map_zero]

/-- A single unchanged original regular point pays the full source denominator.
Its generic clock order is then stable on a source-generated spatial puncture. -/
theorem source_schur97_clock_order_stable (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    ∀ᶠ spatial : ℝ in 𝓝[>] 0,
      (clockSpecialize spatial (sourceSchur97Polynomial event n).det).natTrailingDegree=
        ((sourceSchur97Polynomial event n).det).natTrailingDegree := by
  exact bivariate_clock_order_stable ((sourceSchur97Polynomial event n).det)
    (original_denominator_nonzero event n eps sigma unit positive small damping regular)

private theorem power_quotient (P : ℂ[X]) (m : ℕ) (factor : X^m∣P) : X^m*(P/ₘX^m)=P := by
  obtain ⟨Q,same⟩ := factor
  rw [same,mul_divByMonic_cancel_left Q (monic_X_pow m)]

private theorem inner_factor (P : ℂ[X]) : X^P.natTrailingDegree*(P/ₘX^P.natTrailingDegree)=P :=
  power_quotient P P.natTrailingDegree
    (X_pow_dvd_iff.mpr (fun _ low => coeff_eq_zero_of_lt_natTrailingDegree (p:=P) low))

private theorem inner_unit_nonzero (P : ℂ[X]) (nonzero : P≠0) :
    (P/ₘX^P.natTrailingDegree).coeff 0≠0 := by
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff P.natTrailingDegree) (inner_factor P)
  have leading := coeff_X_pow_mul (P/ₘX^P.natTrailingDegree) P.natTrailingDegree 0
  simp only [zero_add] at leading
  rw [leading] at coefficient
  exact coefficient.symm ▸ coeff_natTrailingDegree_ne_zero.mpr nonzero

private theorem inner_leading_price (P : ℂ[X]) (nonzero : P≠0) :
    let U := P/ₘX^P.natTrailingDegree
    0<polynomialReadRadius U ∧ U.coeff 0≠0 ∧
    ∀ z : ℂ, ‖z‖≤polynomialReadRadius U →
      (‖U.coeff 0‖/2)*‖z‖^P.natTrailingDegree≤‖P.eval z‖ := by
  have origin := inner_unit_nonzero P nonzero
  refine ⟨polynomial_read_radius_positive _ origin,origin,?_⟩
  intro z small
  have margin := polynomial_read_margin (P/ₘX^P.natTrailingDegree) origin z small
  have factor := congrArg (fun Q : ℂ[X] => Q.eval z) (inner_factor P)
  simp only [eval_mul,eval_pow,eval_X] at factor
  calc
    (‖(P/ₘX^P.natTrailingDegree).coeff 0‖/2)*‖z‖^P.natTrailingDegree=
      ‖z‖^P.natTrailingDegree*(‖(P/ₘX^P.natTrailingDegree).coeff 0‖/2) := mul_comm _ _
    _≤‖z‖^P.natTrailingDegree*‖(P/ₘX^P.natTrailingDegree).eval z‖ :=
      mul_le_mul_of_nonneg_left margin (pow_nonneg (norm_nonneg z) _)
    _=‖P.eval z‖ := by rw [←factor,norm_mul,norm_pow]

/-- The complete denominator emits its own epsilon order and positive leading
radius. The clock-leading floor retains that exact epsilon power. -/
theorem source_schur97_clock_leading_price (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2)
    (damping : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    let D := (sourceSchur97Polynomial event n).det
    let L := D.coeff D.natTrailingDegree
    let U := L/ₘX^L.natTrailingDegree
    0<polynomialReadRadius U ∧ U.coeff 0≠0 ∧
    ∀ z : ℂ, ‖z‖≤polynomialReadRadius U →
      (‖U.coeff 0‖/2)*‖z‖^L.natTrailingDegree≤‖L.eval z‖ := by
  exact inner_leading_price _ (coeff_natTrailingDegree_ne_zero.mpr
    (original_denominator_nonzero event n eps sigma unit positive small damping regular))

end LowEnergy.GaussComposite.ActualSourcePreparedSchur97ClockOrder
