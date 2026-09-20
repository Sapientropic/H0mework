import H0mework.Physics.LowEnergyQuantum.Preparation
import H0mework.Physics.DualVariation.MatterVariation

/-! An actual holonomic affine time jet on the original coframe and connections. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair StageNineHolonomicField
open DiracExteriorMatterAction StageNineFullDiracAdjointMaterial StageNineMatterVariation
noncomputable section

def profile (matter velocity : DiracExteriorMatterCarrier) (point : BasePoint) : DiracExteriorMatterCarrier :=
  matter + (point 0 : ℂ) • velocity

theorem profile_derivative (matter velocity : DiracExteriorMatterCarrier) (point : BasePoint) :
    HasFDerivAt (fun p => matterCoordinateEquiv (profile matter velocity p))
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
        (matterCoordinateEquiv velocity)) point := by
  have derivative := (hasFDerivAt_const (matterCoordinateEquiv matter) point).add
    (((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).hasFDerivAt).smul_const
      (matterCoordinateEquiv velocity))
  convert! derivative using 1 <;> simp [profile, map_add, map_smul]
  rfl

theorem profile_directional (matter velocity : DiracExteriorMatterCarrier)
    (point : BasePoint) (mu : LorentzianIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun p => matterCoordinateEquiv (profile matter velocity p)) point mu) =
      if mu=0 then velocity else 0 := by
  unfold fieldDirectionalDerivative
  rw [(profile_derivative matter velocity point).fderiv]
  by_cases temporal : mu=0
  · subst mu
    simp [coordinateDirection]
  · simp [coordinateDirection, temporal, Ne.symm temporal]

def configuration (density : ℝ) (matter velocity : DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { actual with
    matter := profile matter velocity
    conjugateMatter := fun point => (density : ℂ) • fullCanonicalDiracAdjoint (profile matter velocity point) }

def timeIncrement (velocity : DiracExteriorMatterCarrier) : LorentzianIndex → DiracExteriorMatterCarrier :=
  fun mu => if mu=0 then velocity else 0

theorem covariant_origin (density : ℝ) (matter velocity : DiracExteriorMatterCarrier) :
    holonomicMatterCovariantDerivative (configuration density matter velocity) 0 =
      holonomicMatterCovariantDerivative (configuration density matter 0) 0 + timeIncrement velocity := by
  funext mu
  unfold holonomicMatterCovariantDerivative
  simp only [configuration, Pi.add_apply]
  rw [profile_directional, profile_directional]
  by_cases temporal : mu=0
  · simp [profile, timeIncrement, temporal]
    abel
  · simp [profile, timeIncrement, temporal]

theorem point_origin (density : ℝ) (matter velocity : DiracExteriorMatterCarrier) :
    toContinuumPointField (configuration density matter velocity) 0 =
      withMatterJets (toContinuumPointField (configuration density matter 0) 0) matter
        (holonomicMatterCovariantDerivative (configuration density matter 0) 0 + timeIncrement velocity) := by
  unfold toContinuumPointField withMatterJets
  rw [covariant_origin]
  simp [configuration, profile]
  exact ⟨rfl,rfl,rfl⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.Kinetic
