import H0mework.Versions.AB.Physics.MotherSource.CanonicalGauss.Regularity
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenRegularity

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineConjugateMatterVariation DiracExteriorMatterAction
open Stage10.CanonicalGauss Stage10.ChargedPreparation GaussSource
open StageNineGlobalIntegratedAction StageNineDiracDualFormNativeMotherAction Stage10.StaticHamiltonian
open BasinRefinement SourceFiniteData
open scoped ContDiff
noncomputable section
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

theorem preparedMatter_smooth (basis : Basis) (scale : ℝ) :
    ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (preparedMatter basis scale point)) := by
  let linear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
    ((matterCoordinateEquiv.toLinearMap.comp
      (preparation.comp matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap).restrictScalars ℝ
  have same : (fun point => matterCoordinateEquiv (preparedMatter basis scale point)) =
      fun point => orbitalWeight basis scale point • linear (matterCoordinateEquiv (Stage10.Runtime.configuration.matter point)) := by
    funext point
    simp only [preparedMatter, map_smul]
    congr 1
    exact (congrArg (fun value => matterCoordinateEquiv (preparation value))
      (matterCoordinateEquiv.symm_apply_apply _)).symm
  rw [same]
  exact (orbitalWeight_smooth basis scale).smul (linear.contDiff.comp original_matter_smooth)

theorem original_dual_evaluation_smooth (value : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => Stage10.Runtime.configuration.conjugateMatter point value) := by
  have same : (fun point => Stage10.Runtime.configuration.conjugateMatter point value) =
      fun point => ∑ index : MatterCoordinateIndex, matterCoordinateEquiv value index *
        Stage10.Runtime.configuration.conjugateMatter point
          (matterCoordinateEquiv.symm (EuclideanSpace.single index 1)) := by
    funext point
    conv_lhs => rw [← matterDualOfCoordinates_surjective (Stage10.Runtime.configuration.conjugateMatter point),
      matterDualOfCoordinates_apply]
    rfl
  rw [same]
  exact ContDiff.sum fun index _ => contDiff_const.mul
    (Stage10.Recovery.stageOneThroughTenClosure.final.classical.smooth.2.2.2.2.2.2.2.2 index)

theorem preparedDual_smooth (basis : Basis) (scale : ℝ) (index : MatterCoordinateIndex) :
    ContDiff ℝ ∞ (fun point => preparedDual basis scale point
      (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))) := by
  simp only [preparedDual, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  exact (Complex.conjCLE.contDiff.comp (orbitalWeight_smooth basis scale)).mul (original_dual_evaluation_smooth _)

theorem generated_prepared_smooth (first second : Basis) (scale : ℝ) :
    (Stage10.CanonicalGauss.withMatter (abelianPotential fieldPotential)
      (preparedMatter second scale) (preparedDual first scale)).Smooth := by
  rcases generated_configuration_smooth fieldPotential fieldPotential_smooth with
    ⟨coframe, gravity, auxiliary, multiplier, gauge, gaugeAux, scalar, _, _⟩
  exact ⟨coframe, gravity, auxiliary, multiplier, gauge, gaugeAux, scalar,
    preparedMatter_smooth second scale, preparedDual_smooth first scale⟩

theorem generated_prepared_legendre (first second : Basis) (scale : ℝ) (point : BasePoint) :
    HasDerivAt (fun rate : ℝ => sourceGeneratedDiracDualFormNativeUnifiedLocalDensity Stage10.Runtime.source 0 point
      (toContinuumPointField (timeStretch (Stage10.CanonicalGauss.withMatter (abelianPotential fieldPotential)
        (preparedMatter second scale) (preparedDual first scale)) point rate) point))
      (ordinaryTimePairing Stage10.Runtime.source (Stage10.CanonicalGauss.withMatter (abelianPotential fieldPotential)
        (preparedMatter second scale) (preparedDual first scale)) point) 0 :=
  source_time_legendre _ _ (generated_prepared_smooth first second scale) point

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
