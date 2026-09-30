import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.Gap

/-! The same zero's two original physical response faces now share one explicit signed Dirichlet profile. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolZeroOwnedUnitOnePair_dirichlet_coeFn {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    (((one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier) : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume] fun x => burnolUnitTailDirichletRaw observation.coordinate 1 x -
        burnolUnitTailDirichletRaw (1 - observation.coordinate) 1 x := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let value := burnolUnitTailResponse coordinate 1
  change ((value + fourierL2 value : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add value (fourierL2 value),
    burnolUnitTailResponse_coeFn coordinate 1 (by norm_num) (by norm_num),
    burnolZeroOwnedUnitFourier_dirichlet_coeFn observation nontrivial rightHalf] with x addAt valueAt fourierAt
  rw [addAt]
  change value x + fourierL2 value x = _
  rw [valueAt, fourierAt]
  rfl


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
