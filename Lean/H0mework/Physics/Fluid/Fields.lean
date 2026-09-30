import H0mework.Physics.Actual.FieldsRegularity
import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Dirac.DiracMatterCoordinateCalculus
import H0mework.Physics.Fluid.CurrentReadout

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fluid

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCanonicalCauchyState StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineConjugateMatterVariation
open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

local instance matterFintype : Fintype MatterCoordinateIndex := Fintype.ofFinite _

/-- Full spacetime current from the actual primal and independent dual fields. -/
def spatialCurrent (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : StageNineSpatialPoint :=
  WithLp.toLp 2 fun coordinate =>
    (configuration.conjugateMatter point
      (diracMatrixMatterAction (diracGamma coordinate.succ) (configuration.matter point))).re

namespace CurrentReadout

theorem configuration_spatial (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : Fin 3) :
    current configuration.matter configuration.conjugateMatter direction.succ point =
      spatialCurrent configuration point direction := rfl

end CurrentReadout

theorem spatialCurrent_contDiff (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) : ContDiff ℝ ∞ (spatialCurrent configuration) := by
  apply (contDiff_piLp 2).2
  intro direction
  exact CurrentReadout.current_contDiff configuration.matter configuration.conjugateMatter
    smooth.2.2.2.2.2.2.2.1 (fun index => smooth.2.2.2.2.2.2.2.2 index) direction.succ

def velocity (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    StageNineSpatialPoint :=
  spatialCurrent configuration point -
    spatialCurrent configuration (EuclideanSpace.single (0 : Fin 4) (point 0))

theorem velocity_contDiff (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) : ContDiff ℝ ∞ (velocity configuration) := by
  have temporal : ContDiff ℝ ∞ (fun point : BasePoint =>
      EuclideanSpace.single (0 : Fin 4) (point 0)) := by
    apply (contDiff_piLp 2).2
    intro coordinate
    by_cases same : coordinate = 0
    · subst coordinate
      simpa using (EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).contDiff
    · simp only [PiLp.single_apply, if_neg same]
      exact contDiff_const
  exact (spatialCurrent_contDiff configuration smooth).sub
    ((spatialCurrent_contDiff configuration smooth).comp temporal)


end
end SaturationMonoid.PhysicsCore.Stage9CU.Fluid
