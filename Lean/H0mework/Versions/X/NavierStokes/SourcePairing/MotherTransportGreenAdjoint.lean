import H0mework.Versions.X.NavierStokes.MaterialJets.DensitizedReceipt

set_option autoImplicit false
open scoped BigOperators Matrix

namespace SaturationMonoid.NavierStokes.NativeCanonicalGreenAdjoint

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineFullDiracAdjointMaterial StageNineFullDiracAdjointLocalOperator
open StageNineHolonomicField StageNineCartanAffineConnectionActualization
open StageNineLorentzConnectionVariation StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeMaterialAdjointPrincipal NativeMaterialMomentumJet NativeMaterialAdjointAction
open NativeCartanCompensation NativePauliCoframeAction NativeMaterialJetAction

noncomputable section

def internal (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed
    (NativeBalancedMaterialJet.gaugeConnection velocity jet direction))

/-- The original Cartan and complete generated color connection are retained as operators. -/
theorem connection_split (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (direction : Fin 4) (matter : DiracExteriorMatterCarrier) :
    NativeBalancedMaterialJet.connectionOperator velocity jet direction matter =
      spinOperator velocity jet direction matter + cartanOperator velocity direction matter +
        internal velocity jet direction matter := by
  simp only [NativeBalancedMaterialJet.connectionOperator, NativeSourceCartan.connection,
    cartanAffineSpinConnection, diracSpinConnectionLift_add,
    coframeDiracMatrixMatterAction_add_matrix, LinearMap.add_apply,
    spinOperator, cartanOperator, internal]

theorem internal_adjoint (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (direction : Fin 4) (first last : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (internal velocity jet direction first) last =
      -fullCanonicalDiracAdjoint first (internal velocity jet direction last) :=
  LinearMap.congr_fun (fullCanonicalDiracAdjoint_motherLieConnection _ first) last

theorem internal_commutes (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (direction : Fin 4) (matter : DiracExteriorMatterCarrier) :
    principal velocity direction (internal velocity jet direction matter) =
      internal velocity jet direction (principal velocity direction matter) := by
  have actual := LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal
    (inverseCoframeDiracGamma {coframe := NativeCanonicalFluidCoframe.coframe velocity, derivative := 0} direction)
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed
      (NativeBalancedMaterialJet.gaugeConnection velocity jet direction)))) matter
  simpa only [principal, internal, diracExteriorMotherLieAction, LinearMap.smul_apply,
    map_smul, LinearMap.comp_apply] using congrArg (fun value => Complex.I • value) actual

theorem connection_adjoint (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (direction : Fin 4) (first last : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (NativeBalancedMaterialJet.connectionOperator velocity jet direction first) last =
      -fullCanonicalDiracAdjoint first (NativeBalancedMaterialJet.connectionOperator velocity jet direction last) := by
  simp only [connection_split, fullCanonicalDiracAdjoint_add, LinearMap.add_apply,
    spin_adjoint, cartan_adjoint, internal_adjoint, map_add]
  ring

theorem connection_commutator (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) :
    (∑ direction, fullCanonicalDiracAdjoint first
      (principal velocity direction (NativeBalancedMaterialJet.connectionOperator velocity jet direction last) -
        NativeBalancedMaterialJet.connectionOperator velocity jet direction (principal velocity direction last))) =
      (-3 * NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet jet) 0 : ℂ) *
        fullCanonicalDiracAdjoint first (principal velocity 0 last) := by
  have term (direction : Fin 4) :
      principal velocity direction (NativeBalancedMaterialJet.connectionOperator velocity jet direction last) -
        NativeBalancedMaterialJet.connectionOperator velocity jet direction (principal velocity direction last) =
      principal velocity direction (spinOperator velocity jet direction last) -
        spinOperator velocity jet direction (principal velocity direction last) := by
    simp only [connection_split, map_add, principal_commutes_cartanOperator, internal_commutes]
    abel
  simp only [term]
  exact spin_commutator_pairing velocity jet first last

theorem divergence_balance (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) :
    (volumeFactor velocity : ℂ) * (∑ direction, fullCanonicalDiracAdjoint first
      (principal velocity direction (NativeBalancedMaterialJet.connectionOperator velocity jet direction last) -
        NativeBalancedMaterialJet.connectionOperator velocity jet direction (principal velocity direction last))) -
      (∑ direction, (coefficientDerivative velocity jet direction : ℂ) *
        fullCanonicalDiracAdjoint first (Complex.I • diracMatrixMatterAction (diracGamma direction) last)) = 0 := by
  rw [connection_commutator, principal_divergence]
  ring

def kinetic (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (matter : DiracExteriorMatterCarrier) (raw : Fin 4 → DiracExteriorMatterCarrier) : DiracExteriorMatterCarrier :=
  ∑ direction, principal velocity direction
    (raw direction + NativeBalancedMaterialJet.connectionOperator velocity jet direction matter)

def currentDerivative (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) (firstJet lastJet : Fin 4 → DiracExteriorMatterCarrier) : ℂ :=
  ∑ direction, (momentumDerivative velocity jet first firstJet last direction +
    (coefficient velocity direction : ℂ) * fullCanonicalDiracAdjoint first
      (Complex.I • diracMatrixMatterAction (diracGamma direction) (lastJet direction)))

private theorem adjoint_sum (family : Fin 4 → DiracExteriorMatterCarrier) (last : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (∑ direction, family direction) last =
      ∑ direction, fullCanonicalDiracAdjoint (family direction) last := by
  simp only [Fin.sum_univ_four, fullCanonicalDiracAdjoint_add, LinearMap.add_apply]

/-- The complete original formal Green identity exposes only the two actual kinetic legs. -/
theorem whole_green (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (first last : DiracExteriorMatterCarrier) (firstJet lastJet : Fin 4 → DiracExteriorMatterCarrier) :
    currentDerivative velocity jet first last firstJet lastJet = (volumeFactor velocity : ℂ) *
      (fullCanonicalDiracAdjoint first (kinetic velocity jet last lastJet) -
        fullCanonicalDiracAdjoint (kinetic velocity jet first firstJet) last) := by
  have balance := divergence_balance velocity jet first last
  simp only [map_sub, Finset.sum_sub_distrib] at balance
  simp only [currentDerivative, momentumDerivative, Finset.sum_add_distrib,
    ← weighted_principal, ← Finset.mul_sum, kinetic, map_sum, map_add, adjoint_sum,
    principal_adjoint, fullCanonicalDiracAdjoint_add, LinearMap.add_apply,
    connection_adjoint, neg_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linear_combination -balance

end
end SaturationMonoid.NavierStokes.NativeCanonicalGreenAdjoint
