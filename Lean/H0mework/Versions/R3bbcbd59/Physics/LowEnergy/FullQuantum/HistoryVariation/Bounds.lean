import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Window

/-! One source-generated compact bound controls all initial data and every nearby actual field history. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen
noncomputable section
attribute [local irreducible] scalarDriftMap fullOperator

theorem source_majorant_controls (direction : ℝ → GaugeProfile) (coupling : ℝ)
    (scalar scalarDirection : ℝ → ScalarProfile) (time M : ℝ)
    (bounded : sourceMajorant direction coupling scalar scalarDirection time≤M) :
    ‖scalarDriftMap (scalar time)‖+‖scalarDriftMap (scalarDirection time)‖≤M ∧
      ‖localForce (direction time) coupling (scalarDirection time)‖≤M := by
  dsimp only [sourceMajorant] at bounded
  constructor <;> linarith [norm_nonneg (scalarDriftMap (scalar time)),
    norm_nonneg (scalarDriftMap (scalarDirection time)),
    norm_nonneg (localForce (direction time) coupling (scalarDirection time))]

theorem scalarFamily_bound (direction : ℝ → GaugeProfile) (coupling : ℝ)
    (scalar scalarDirection : ℝ → ScalarProfile) (epsilon time M : ℝ) (near : |epsilon|≤1)
    (bounded : sourceMajorant direction coupling scalar scalarDirection time≤M) :
    ‖scalarDriftMap (scalarFamily scalar scalarDirection epsilon time)‖≤M := by
  calc
    _ = ‖scalarDriftMap (scalar time)+(epsilon : ℂ) • scalarDriftMap (scalarDirection time)‖ := by
      rw [scalarFamily,map_add,map_smul]
    _ ≤ ‖scalarDriftMap (scalar time)‖+|epsilon| *‖scalarDriftMap (scalarDirection time)‖ := by
      have triangle := norm_add_le (scalarDriftMap (scalar time)) ((epsilon : ℂ) • scalarDriftMap (scalarDirection time))
      simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs] using! triangle
    _ ≤ ‖scalarDriftMap (scalar time)‖+‖scalarDriftMap (scalarDirection time)‖ := by
      nlinarith [norm_nonneg (scalarDriftMap (scalarDirection time))]
    _ ≤ M := (source_majorant_controls direction coupling scalar scalarDirection time M bounded).1

theorem fullOperator_window_bound (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar) (time M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 time, ‖scalarDriftMap (scalar r)‖≤M) (first second : ℝ)
    (firstIn : first ∈ uIcc 0 time) (secondIn : second ∈ uIcc 0 time) (initial : FullMatterL2) :
    ‖fullOperator gauge continuousGauge coupling scalar continuousScalar first second initial‖≤
      (1+|time| *M)*‖initial‖ := by
  have integral : |∫ r in first..second, ‖scalarDriftMap (scalar r)‖|≤|time| *M := by
    have generated := window_integral_bound (fun r => ‖scalarDriftMap (scalar r)‖) time M nonnegative
      (fun r hr => by simpa only [norm_norm] using bounded r hr) first second firstIn secondIn
    simpa only [Real.norm_eq_abs] using generated
  exact (fullOperator_bound gauge continuousGauge coupling scalar continuousScalar first second initial).trans
    (mul_le_mul_of_nonneg_right (by linarith : 1+|∫ r in first..second, ‖scalarDriftMap (scalar r)‖|≤1+|time| *M)
      (norm_nonneg initial))

theorem family_window_bound (gauge direction : ℝ → GaugeProfile)
    (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction) (coupling : ℝ)
    (scalar scalarDirection : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (continuousScalarDirection : Continuous scalarDirection) (time M : ℝ) (nonnegative : 0≤M)
    (bounded : ∀ r ∈ uIcc 0 time, sourceMajorant direction coupling scalar scalarDirection r≤M)
    (epsilon : ℝ) (near : |epsilon|≤1) (first second : ℝ)
    (firstIn : first ∈ uIcc 0 time) (secondIn : second ∈ uIcc 0 time) (initial : FullMatterL2) :
    ‖familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon first second initial‖≤(1+|time| *M)*‖initial‖ :=
  fullOperator_window_bound _ _ _ _ _ time M nonnegative
    (fun r hr => scalarFamily_bound direction coupling scalar scalarDirection epsilon r M near (bounded r hr))
    first second firstIn secondIn initial

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
