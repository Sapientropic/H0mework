import H0mework.Physics.LowEnergyEvolution.Geometry

/-! Full Lorentz curvature of the source-generated moving connection. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineLorentzConnectionVariation Stage9C.Dynamics.Homogeneous Stage9C.Material.SpinPair
open Set Filter
open scoped Topology
noncomputable section

def torsionRate (x : State) : ℝ := -2*contorsion x*clock x*x 1/x 0

theorem Solution.contorsion_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Ioo (-flow.radius) flow.radius) :
    HasDerivAt (fun t => contorsion (flow.curve t)) (torsionRate (flow.curve time)) time := by
  have derivative := (hasDerivAt_const time spinScale).div
    ((flow.coordinate_derivative time inside 0).pow 2)
    (pow_ne_zero _ (ne_of_gt (flow.admissible time inside).1))
  convert! derivative using 1
  change -2*(spinScale/(flow.curve time 0)^2)*clock (flow.curve time)*flow.curve time 1/flow.curve time 0 = _
  change _ = (0 * (flow.curve time 0)^2 - spinScale *
    (2*(flow.curve time 0)^(2-1) * (clock (flow.curve time)*flow.curve time 1))) / ((flow.curve time 0)^2)^2
  field_simp [ne_of_gt (flow.admissible time inside).1]
  ring

private theorem connection_linear (h k : ℝ) (mu row col : LorentzianIndex) :
    (boostConnection h + homogeneousConnection k) mu row col =
      h * boostConnection 1 mu row col + k * homogeneousConnection 1 mu row col := by
  fin_cases mu <;> fin_cases row <;> fin_cases col <;>
    simp [boostConnection, homogeneousConnection, homogeneousContorsion,
      lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient, minkowskiInternalSign,
      pairFirst, pairSecond, Fin.sum_univ_six]

theorem Solution.connection_derivative {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Ioo (-flow.radius) flow.radius)
    (mu nu row col : LorentzianIndex) :
    gravityConnectionDerivative flow.configuration point mu nu row col =
      if mu = 0 then
        (boostConnection (generator (flow.pointState point) 1) +
          homogeneousConnection (torsionRate (flow.pointState point))) nu row col else 0 := by
  have derivative := ((flow.coordinate_derivative _ inside 1).mul_const (boostConnection 1 nu row col)).add
    ((flow.contorsion_derivative _ inside).mul_const (homogeneousConnection 1 nu row col))
  change HasDerivAt (fun time => flow.curve time 1 * boostConnection 1 nu row col +
    contorsion (flow.curve time) * homogeneousConnection 1 nu row col) _ _ at derivative
  have neighborhood : ∀ᶠ p : BasePoint in 𝓝 point, p 0 ∈ Ioo (-flow.radius) flow.radius :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds inside)
  have localValues : (fun p => flow.configuration.gravityConnection p nu row col) =ᶠ[𝓝 point]
      fun p => flow.curve (p 0) 1 * boostConnection 1 nu row col +
        contorsion (flow.curve (p 0)) * homogeneousConnection 1 nu row col := by
    filter_upwards [neighborhood] with p hp
    rw [flow.connection_generated p hp, connection_linear]
    rfl
  unfold gravityConnectionDerivative
  rw [localValues.fderiv_eq, time_fderiv_apply _ _ point derivative, connection_linear]
  rfl

def movingCurvature (h k dh dk : ℝ) : PhysicalBivector :=
  !![-dh,0,0,2*h*k,0,0;
     0,-dh,0,0,2*h*k,0;
     0,0,-dh,0,0,2*h*k;
     dk,0,0,h^2-k^2,0,0;
     0,dk,0,0,h^2-k^2,0;
     0,0,dk,0,0,h^2-k^2]

private theorem curvature_normal_form (h k dh dk : ℝ) (internalPair spacetimePair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
      ((if pairFirst spacetimePair = 0 then
          (boostConnection dh + homogeneousConnection dk) (pairSecond spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) else 0) -
        (if pairSecond spacetimePair = 0 then
          (boostConnection dh + homogeneousConnection dk) (pairFirst spacetimePair)
            (pairFirst internalPair) (pairSecond internalPair) else 0) +
        ∑ middle : LorentzianIndex,
          ((boostConnection h + homogeneousConnection k) (pairFirst spacetimePair) (pairFirst internalPair) middle *
              (boostConnection h + homogeneousConnection k) (pairSecond spacetimePair) middle (pairSecond internalPair) -
            (boostConnection h + homogeneousConnection k) (pairSecond spacetimePair) (pairFirst internalPair) middle *
              (boostConnection h + homogeneousConnection k) (pairFirst spacetimePair) middle (pairSecond internalPair))) =
      movingCurvature h k dh dk internalPair spacetimePair := by
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [movingCurvature, boostConnection, homogeneousConnection, homogeneousContorsion,
      lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient, minkowskiInternalSign,
      pairFirst, pairSecond, Fin.sum_univ_six, Fin.sum_univ_four] <;> ring

theorem Solution.gravity_curvature {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Ioo (-flow.radius) flow.radius) :
    holonomicGravityCurvature flow.configuration point =
      movingCurvature (flow.pointState point 1) (contorsion (flow.pointState point))
        (generator (flow.pointState point) 1) (torsionRate (flow.pointState point)) := by
  funext internalPair spacetimePair
  unfold holonomicGravityCurvature
  dsimp only []
  rw [flow.connection_derivative point inside, flow.connection_derivative point inside,
    flow.connection_generated point inside]
  exact curvature_normal_form _ _ _ _ internalPair spacetimePair

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
