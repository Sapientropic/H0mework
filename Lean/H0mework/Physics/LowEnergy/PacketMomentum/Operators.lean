import H0mework.Physics.LowEnergy.PacketDynamics.CurrentContinuity

/-! Genuine continuum transfers and the actual time histories act jointly continuously on moving packets. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketMomentum
open FullQuantum FullSpace PacketNoise PacketDynamics
noncomputable section

theorem phaseShift_bound (shift : Position) : ‖(phaseShift shift).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro field
  simpa only [one_mul] using! (phaseShift_norm shift field).le

theorem phase_apply_continuous {X : Type*} [TopologicalSpace X] (shift : X → Position)
    (continuousShift : Continuous shift) (curve : X → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun x => phaseShift (shift x) (curve x)) :=
  strong_apply_continuous (fun x => (phaseShift (shift x)).toContinuousLinearMap) (fun _ => 1)
    continuous_const (fun x => phaseShift_bound (shift x))
    (fun field => (phaseShift_continuous field).comp continuousShift) curve continuousCurve

theorem cosine_apply_continuous {X : Type*} [TopologicalSpace X] (shift : X → Position)
    (continuousShift : Continuous shift) (curve : X → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun x => cosineShift (shift x) (curve x)) :=
  strong_apply_continuous (fun x => cosineShift (shift x)) (fun _ => 1)
    continuous_const (fun x => cosineShift_norm (shift x))
    (fun field => (cosineShift_continuous field).comp continuousShift) curve continuousCurve

theorem flow_apply_continuous {X : Type*} [TopologicalSpace X] (time : X → ℝ)
    (continuousTime : Continuous time) (curve : X → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun x => spatialFlow 0 (time x) (curve x)) :=
  strong_apply_continuous (fun x => spatialFlow 0 (time x)) (fun x => 1+|time x| * sourceRate 0)
    (continuous_const.add (continuousTime.abs.mul continuous_const)) (fun x => spatialFlow_norm 0 (time x))
    (fun field => (spatialFlow_stronglyContinuous 0 field).comp continuousTime) curve continuousCurve

theorem adjoint_apply_continuous {X : Type*} [TopologicalSpace X] (time : X → ℝ)
    (continuousTime : Continuous time) (curve : X → FullMatterL2) (continuousCurve : Continuous curve) :
    Continuous (fun x => adjointFlow (time x) (curve x)) :=
  strong_apply_continuous (fun x => adjointFlow (time x)) (fun x => 1+|time x| * sourceRate 0)
    (continuous_const.add (continuousTime.abs.mul continuous_const)) (fun x => adjointFlow_norm (time x))
    (fun field => (adjointFlow_stronglyContinuous field).comp continuousTime) curve continuousCurve

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketMomentum
