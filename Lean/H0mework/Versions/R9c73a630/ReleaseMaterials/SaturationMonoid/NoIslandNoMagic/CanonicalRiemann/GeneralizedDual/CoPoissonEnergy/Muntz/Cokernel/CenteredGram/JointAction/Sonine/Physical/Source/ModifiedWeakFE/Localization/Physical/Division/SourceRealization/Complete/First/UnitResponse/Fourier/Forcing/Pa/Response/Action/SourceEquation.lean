import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Class
import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Correction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Fourier
import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPhysicalRead

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- Both velocities consume the actual resolvent forcing before projection. -/
theorem comb_source_equations {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) :
    let q := burnolPaCombApproximation n
    let r := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
    let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let C := (1 / 2 : ℂ) • (r - F r)
    let α := observation.coordinate / 2 - 1 / 4
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (B : BurnolL2))
      ((α • C + (1 / 2 : ℂ) • (q - F q) : BurnolPaAmbientCarrier) : BurnolL2) 0 ∧
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (C : BurnolL2))
      ((α • B + (1 / 2 : ℂ) • (q + F q) : BurnolPaAmbientCarrier) : BurnolL2) 0 := by
  intro q r F B C α
  have right : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]; norm_num; linarith
  have forward := burnolDirectRightResolventOrbit_hasDerivAt
    (observation.coordinate / 2) right (q : BurnolL2)
  change HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (r : BurnolL2))
    (α • (r : BurnolL2) + (q : BurnolL2)) 0 at forward
  have reverse := burnolFourierOrbit_hasDerivAt _ _ forward
  simp only [map_add, map_smul] at reverse
  constructor
  · have generated := (forward.add reverse).const_smul (1 / 2 : ℂ)
    convert! generated using 1
    · funext h
      change burnolMultiplicativeDilation (-h / 2)
        ((1 / 2 : ℂ) • ((r : BurnolL2) + fourierL2 (r : BurnolL2))) = _
      rw [map_smul, map_add]
      rfl
    · change ((α • ((1 / 2 : ℂ) • ((r : BurnolL2) - fourierL2 (r : BurnolL2)))) +
        (1 / 2 : ℂ) • ((q : BurnolL2) - fourierL2 (q : BurnolL2))) = _
      module
  · have generated := (forward.sub reverse).const_smul (1 / 2 : ℂ)
    convert! generated using 1
    · funext h
      change burnolMultiplicativeDilation (-h / 2)
        ((1 / 2 : ℂ) • ((r : BurnolL2) - fourierL2 (r : BurnolL2))) = _
      rw [map_smul, map_sub]
      rfl
    · change ((α • ((1 / 2 : ℂ) • ((r : BurnolL2) + fourierL2 (r : BurnolL2)))) +
        (1 / 2 : ℂ) • ((q : BurnolL2) + fourierL2 (q : BurnolL2))) = _
      module

/-- The same actual physical compression reads both full source equations. -/
theorem comb_physical_equations {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) :
    let q := burnolPaCombApproximation n
    let r := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
    let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let C := (1 / 2 : ℂ) • (r - F r)
    let α := observation.coordinate / 2 - 1 / 4
    HasDerivAt (fun h : ℝ => burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (B : BurnolL2)))
      (α • C + (1 / 2 : ℂ) • (q - F q)) 0 ∧
    HasDerivAt (fun h : ℝ => burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (C : BurnolL2)))
      (α • B + (1 / 2 : ℂ) • (q + F q)) 0 := by
  intro q r F B C α
  have generated := comb_source_equations observation nontrivial rightHalf n
  constructor
  · have mapped := (burnolEvenAmbientProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.1
    convert! mapped using 1
    change _ = burnolEvenAmbientProjection _
    simp only [burnolEvenAmbientProjection,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]; rfl
  · have mapped := (burnolEvenAmbientProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.2
    convert! mapped using 1
    change _ = burnolEvenAmbientProjection _
    simp only [burnolEvenAmbientProjection,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]; rfl

/-- Pa removes exactly the generated forcing, after the whole-state action. -/
theorem comb_residual_equations {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) :
    let r := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
    let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let C := (1 / 2 : ℂ) • (r - F r)
    let α := observation.coordinate / 2 - 1 / 4
    let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    HasDerivAt (fun h : ℝ => Q (burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (B : BurnolL2)))) (α • Q C) 0 ∧
    HasDerivAt (fun h : ℝ => Q (burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (C : BurnolL2)))) (α • Q B) 0 := by
  intro r F B C α Q
  let q := burnolPaCombApproximation n
  have qPa := burnolPaCombApproximation_mem n
  have FqPa := burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange qPa
  have qZero : Q q = 0 := Submodule.starProjection_orthogonal_apply_eq_zero qPa
  have FqZero : Q (F q) = 0 := Submodule.starProjection_orthogonal_apply_eq_zero FqPa
  have generated := comb_physical_equations observation nontrivial rightHalf n
  constructor
  · have mapped := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.1
    convert! mapped using 1
    change α • Q C = Q (α • C + (1 / 2 : ℂ) • (q - F q))
    simp only [map_add, map_sub, map_smul, qZero, FqZero, sub_self, smul_zero, add_zero]
  · have mapped := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.2
    convert! mapped using 1
    change α • Q B = Q (α • B + (1 / 2 : ℂ) • (q + F q))
    simp only [map_add, map_smul, qZero, FqZero, add_zero, smul_zero]

/-- The original K reads the actual paired/odd source action, with its Pa forcing paid. -/
theorem comb_original_K_equations {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (n : Nat) :
    let r := burnolPaCombPhysicalResponse observation nontrivial rightHalf n
    let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf n
    let C := (1 / 2 : ℂ) • (r - F r)
    let α := observation.coordinate / 2 - 1 / 4
    let coordinate := burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
    let R := burnolCompletedMellinEvaluator coordinate
    HasDerivAt (fun h : ℝ => R (burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (B : BurnolL2)))) (α * R C) 0 ∧
    HasDerivAt (fun h : ℝ => R (burnolEvenAmbientProjection
      (burnolMultiplicativeDilation (-h / 2) (C : BurnolL2)))) (α * R B) 0 := by
  intro r F B C α coordinate R
  let q := burnolPaCombApproximation n
  have read (value : BurnolPaAmbientCarrier) (inside : value ∈ burnolCompactCoPoissonClosedRange) :
      R value = 0 := by
    rw [← burnolCompletedMellinRieszVector_readback]
    rw [inner_eq_zero_symm]
    exact (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
      coordinate observation.mathlibZero) value inside
  have qRead := read q (burnolPaCombApproximation_mem n)
  have FqRead := read (F q)
    (burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange
      (burnolPaCombApproximation_mem n))
  have generated := comb_physical_equations observation nontrivial rightHalf n
  constructor
  · have mapped := (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.1
    convert! mapped using 1
    change α * R C = R (α • C + (1 / 2 : ℂ) • (q - F q))
    simp only [map_add, map_sub, map_smul, qRead, FqRead, sub_self, add_zero,
      smul_eq_mul, mul_zero]
  · have mapped := (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 generated.2
    convert! mapped using 1
    change α * R B = R (α • B + (1 / 2 : ℂ) • (q + F q))
    simp only [map_add, map_smul, qRead, FqRead, add_zero, smul_eq_mul, mul_zero]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
