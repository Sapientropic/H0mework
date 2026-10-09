import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrentSymbol.Projection
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.FullCurrent.Kernel

/-! Original spin, P286, joint scalar and graded phase generate the reducing
law for the complete Dirac kernel, before any inverse is requested. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
open DiracExteriorMatterAction DiracCliffordRepresentation ProofFreeRicherAnholonomicSource
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open Stage9C.Material.SpinPair SU7ExteriorBreakingYukawa ActiveSector Triangular
noncomputable section

theorem spin_reducing (M : DiracMatrix) : Commute projection (diracMatrixMatterAction M) :=
  projection_spin M

theorem connection_reducing (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (mu : LorentzianIndex) : Commute projection (connection C point mu) :=
  (spin_reducing _).add_right (projection_gauge _)

theorem principal_reducing (C : StageNineHolonomicConfiguration) (point : BasePoint) :
    Commute projection (currentCoframeMatterTemporalPrincipal (C.coframe point)) :=
  (spin_reducing _).smul_right Complex.I

theorem freeKnown_reducing (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) : Commute projection (freeKnown C point k) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro j _
  exact (spin_reducing _).mul_right
    (((Commute.one_right projection).smul_right _).add_right (connection_reducing C point j.succ))

theorem original_yukawa_reducing (point : BasePoint) :
    Commute projection (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point))) := by
  rw [actual_scalar]
  simp only [sourceGeneratedVacuumCoordinates,LinearEquiv.symm_apply_apply]
  change projection*_= _*projection
  rw [show projection*diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)=0
      from projection_yukawa_zero _,
    show diracDualRightChiralYukawaAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)*projection=0
      from actual_yukawa_projection_zero]

theorem known_reducing (point : BasePoint) (k : Fin 3 → ℝ) : Commute projection (knownSymbol actual point k) :=
  (freeKnown_reducing actual point k).add_right (original_yukawa_reducing point)

theorem lower_reducing (point : BasePoint) (k : Fin 3 → ℝ) : Commute projection (lowerSymbol actual point k) :=
  (known_reducing point k).add_right ((principal_reducing actual point).mul_right (connection_reducing actual point 0))

theorem degreeSix_projection : MixedSymbol.degreeSix*projection=0 ∧ projection*MixedSymbol.degreeSix=0 := by
  constructor
  all_goals apply LinearMap.ext; intro v; funext spin
  all_goals simp [MixedSymbol.degreeSix,projection,internalMatterLinearAction,internalProjection,
    colorTripletMatter,Fin.sum_univ_three]

theorem phase_reducing : Commute projection FullPhase.phaseGenerator := by
  apply (spin_reducing _).add_right
  apply Commute.smul_right
  change projection*MixedSymbol.degreeSix=MixedSymbol.degreeSix*projection
  rw [degreeSix_projection.1,degreeSix_projection.2]

theorem stationary_reducing (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) :
    Commute projection (FullCurrent.stationaryKernel point k z) :=
  (((principal_reducing actual point).smul_right _).add_right (lower_reducing point k)).add_right
    (((principal_reducing actual point).mul_right phase_reducing).smul_right _)

theorem stationaryGreen_reducing (point : BasePoint) (k : Fin 3 → ℝ) (z : ℂ) :
    Commute projection (FullCurrent.stationaryGreen point k z) := by
  unfold FullCurrent.stationaryGreen
  by_cases regular : IsUnit (FullCurrent.stationaryKernel point k z)
  · obtain ⟨unit,same⟩ := regular
    have reduced := stationary_reducing point k z
    rw [← same] at reduced ⊢
    simpa only [Ring.inverse_unit] using reduced.units_inv_right
  · rw [Ring.inverse_non_unit _ regular]
    exact Commute.zero_right _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullCurrentSymbol
