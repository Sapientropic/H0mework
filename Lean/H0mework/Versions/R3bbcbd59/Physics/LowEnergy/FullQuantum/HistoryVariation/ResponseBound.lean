import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Response

/-! The actual finite insertion has one bound for all initial states and all endpoints in its source window. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

theorem insertionIntegrand_bound (window M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 window, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (time r : ℝ)
    (timeIn : time ∈ uIcc 0 window) (rIn : r ∈ uIcc 0 window) (initial : FullMatterL2) :
    ‖insertionIntegrand gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time initial r‖≤(1+|window| *M)^2*M*‖initial‖ := by
  let K := 1+|window| *M
  have Kpos : 0≤K := by dsimp only [K]; positivity
  let v := U epsilon 0 r initial
  have right : ‖v‖≤K*‖initial‖ := family_window_bound gauge direction continuousGauge continuousDirection coupling
    scalar scalarDirection continuousScalar continuousScalarDirection window M nonnegative bounded epsilon near 0 r left_mem_uIcc rIn initial
  have scalarBound (s : ℝ) (hs : s ∈ uIcc 0 window) : ‖scalarDriftMap (scalar s)‖≤M := by
    have controls := (source_majorant_controls direction coupling scalar scalarDirection s M (bounded s hs)).1
    linarith [norm_nonneg (scalarDriftMap (scalarDirection s))]
  have forceBound := (source_majorant_controls direction coupling scalar scalarDirection r M (bounded r rIn)).2
  have forceEstimate : ‖localForce (direction r) coupling (scalarDirection r) v‖≤M*‖v‖ :=
    ((localForce (direction r) coupling (scalarDirection r)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right forceBound (norm_nonneg v))
  calc
    _ ≤ K*‖localForce (direction r) coupling (scalarDirection r) v‖ :=
      fullOperator_window_bound gauge continuousGauge coupling scalar continuousScalar window M nonnegative scalarBound
        r time rIn timeIn _
    _ ≤ K*(M*‖v‖) := mul_le_mul_of_nonneg_left forceEstimate Kpos
    _ ≤ K*(M*(K*‖initial‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left right nonnegative) Kpos
    _ = _ := by dsimp only [K]; ring

theorem insertionResponse_bound (window M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 window, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (time : ℝ) (timeIn : time ∈ uIcc 0 window) (initial : FullMatterL2) :
    ‖insertionResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time initial‖≤|window| *(1+|window| *M)^2*M*‖initial‖ := by
  have generated := window_integral_bound
    (insertionIntegrand gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon time initial) window ((1+|window| *M)^2*M*‖initial‖) (by positivity)
    (fun r hr => insertionIntegrand_bound gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection window M nonnegative bounded epsilon near time r timeIn hr initial)
    0 time left_mem_uIcc timeIn
  exact generated.trans_eq (by ring)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
