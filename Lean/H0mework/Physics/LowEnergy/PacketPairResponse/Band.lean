import H0mework.Physics.LowEnergy.VertexTensor.Continuity
import H0mework.Physics.LowEnergy.PacketPairResponse.Branch

/-! The already generated light-root radius fixes one physical momentum ball, including the continuous zero-momentum extension. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open FullQuantum FullSpace PacketNoise LightCausal LightSpace Stage9C.Material.SpinPair VertexTensor
noncomputable section

def bandRadius : ℝ := spinScale*LightModes.momentumRadius
abbrev LightBand := {momentum : Position // ‖momentum‖ ≤ bandRadius}

def bandMomentum (point : LightBand) : Fin 3 → ℝ := fun j => point.val j
def bandShift (point : LightBand) : Position := physicalTransfer point.val

theorem radius_norm (momentum : Position) : Rotation.momentumRadius (fun j => momentum j)=‖momentum‖ := by
  simp only [Rotation.momentumRadius,EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs,Fin.sum_univ_three]

theorem band_small (point : LightBand) :
    Rotation.momentumRadius (bandMomentum point) ≤ spinScale*LightModes.momentumRadius := by
  change Rotation.momentumRadius (fun j => point.val j) ≤ _
  rw [radius_norm]
  exact point.property

theorem bandShift_physical (point : LightBand) : physicalMomentum (bandShift point)=bandMomentum point := by
  funext j
  exact physicalTransfer_correct point.val j

theorem bandMomentum_continuous : Continuous bandMomentum := by
  unfold bandMomentum
  fun_prop

theorem bandShift_continuous : Continuous bandShift := by
  unfold bandShift physicalTransfer
  fun_prop

theorem bandCoupling_continuous (same : Bool) :
    Continuous (fun point : LightBand => fixedMomentumCoupling same (bandMomentum point)) := by
  apply continuous_iff_continuousAt.mpr
  intro point
  exact (fixedMomentumCoupling_continuousAt same _ (band_small point)).comp bandMomentum_continuous.continuousAt

theorem bandRate_continuous : Continuous (fun point : LightBand => thetaRate (bandMomentum point)) := by
  have radial : Continuous (fun point : LightBand => radialMomentum (bandMomentum point)) :=
    radialMomentum_continuous.comp bandMomentum_continuous
  have root : Continuous (fun point : LightBand => LightInteraction.axialRoot (radialMomentum (bandMomentum point))) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    exact ContinuousAt.comp (f := fun k : LightBand => radialMomentum (bandMomentum k)) (x := point)
      (axialRoot_continuousAt _ (radial_small _ (band_small point))) radial.continuousAt
  change Continuous (fun point : LightBand => lapse*spinScale*radialMomentum (bandMomentum point)*
    Real.sqrt (LightInteraction.axialRoot (radialMomentum (bandMomentum point))))
  exact ((continuous_const.mul radial).mul (Real.continuous_sqrt.comp root))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
