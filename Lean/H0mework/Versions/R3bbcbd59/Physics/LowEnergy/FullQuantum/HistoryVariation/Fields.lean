import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Return
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Force

/-! The primitive gauge and final-scalar histories form an actual affine family, with their source-generated tangent force. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing PerturbedGreen SpatialResponse
noncomputable section

def gaugeFamily (gauge direction : ℝ → GaugeProfile) (epsilon : ℝ) (time : ℝ) : GaugeProfile :=
  gauge time+epsilon • direction time

def scalarFamily (scalar direction : ℝ → ScalarProfile) (epsilon : ℝ) (time : ℝ) : ScalarProfile :=
  scalar time+(epsilon : ℂ) • direction time

theorem gaugeFamily_continuous (gauge direction : ℝ → GaugeProfile)
    (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction) (epsilon : ℝ) :
    Continuous (gaugeFamily gauge direction epsilon) := by
  simpa only [gaugeFamily,Pi.add_apply,Pi.smul_apply] using!
    continuousGauge.add ((continuous_const : Continuous (fun _ : ℝ => epsilon)).smul continuousDirection)

theorem scalarFamily_continuous (scalar direction : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousDirection : Continuous direction) (epsilon : ℝ) :
    Continuous (scalarFamily scalar direction epsilon) := by
  simpa only [scalarFamily,Pi.add_apply,Pi.smul_apply] using!
    continuousScalar.add ((continuous_const : Continuous (fun _ : ℝ => (epsilon : ℂ))).smul continuousDirection)

theorem localForce_affine (gauge direction : ℝ → GaugeProfile) (coupling : ℝ)
    (scalar scalarDirection : ℝ → ScalarProfile) (epsilon time : ℝ) :
    localForce (gaugeFamily gauge direction epsilon time) coupling (scalarFamily scalar scalarDirection epsilon time)=
      localForce (gauge time) coupling (scalar time)+(epsilon : ℂ) • localForce (direction time) coupling (scalarDirection time) := by
  simp only [gaugeFamily,scalarFamily,localForce,gaugePotential_add,gaugePotential_real_smul,map_add,map_smul,smul_add]
  module

variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)

def familyOperator (epsilon start time : ℝ) : SpatialOperators :=
  fullOperator (gaugeFamily gauge direction epsilon) (gaugeFamily_continuous gauge direction continuousGauge continuousDirection epsilon)
    coupling (scalarFamily scalar scalarDirection epsilon)
    (scalarFamily_continuous scalar scalarDirection continuousScalar continuousScalarDirection epsilon) start time

theorem familyOperator_starts (epsilon start : ℝ) (initial : FullMatterL2) :
    familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection continuousScalar continuousScalarDirection
      epsilon start start initial=initial := fullOperator_starts _ _ _ _ _ _ _

theorem familyOperator_continuous (epsilon start : ℝ) (initial : FullMatterL2) :
    Continuous (fun t => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection epsilon start t initial) := fullOperator_continuous _ _ _ _ _ _ _

theorem familyOperator_zero (start time : ℝ) (initial : FullMatterL2) :
    familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection continuousScalar continuousScalarDirection
      0 start time initial=fullOperator gauge continuousGauge coupling scalar continuousScalar start time initial := by
  have gzero : gaugeFamily gauge direction 0=gauge := by funext t; simp [gaugeFamily]
  have szero : scalarFamily scalar scalarDirection 0=scalar := by funext t; simp [scalarFamily]
  simp only [familyOperator,gzero,szero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
