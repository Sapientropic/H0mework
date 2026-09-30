import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.IntegralEquation
import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.Mild

/-! The actual constant-history time integral is the original all-field spatial Dirac inverse. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryLaplace
noncomputable section
attribute [local irreducible] fullOperator value fullG

theorem stationary_dirac_equation (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    CoupledEquation 0 energy damping gauge coupling scalar
      (stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)) source := by
  apply (fourier_equation_iff 0 energy damping positive _ _ _ _).mpr
  change stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)=
    freeR 0 energy damping positive
      (Complex.I • inversePrincipal 0 (source-potential scalar
        (stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)))+
        (coupling : ℂ) • gaugePotential gauge
          (stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)))
  have generated := stationary_free_equation gauge coupling scalar energy damping positive (inversePrincipal 0 source)
  convert! generated using 2
  simp only [localForce,add_apply,smul_apply,scalarDriftMap_apply,map_sub,smul_add,smul_sub,smul_neg,smul_smul]
  rw [← mul_assoc Complex.I]
  simp
  module

theorem stationary_diracValue_original (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    stationaryValue gauge coupling scalar energy damping (inversePrincipal 0 source)=
      fullG 0 energy damping positive gauge coupling scalar source :=
  fullG_unique 0 energy damping positive gauge coupling scalar _ source
    (stationary_dirac_equation gauge coupling scalar energy damping positive source)

theorem stationary_diracResponse_original (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) :
    diracResponse (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const
      ‖scalarDriftMap scalar‖ (fun _ _ => le_rfl) energy damping positive=
      fullG 0 energy damping positive gauge coupling scalar := by
  apply ContinuousLinearMap.ext
  intro source
  exact stationary_diracValue_original gauge coupling scalar energy damping positive source

theorem stationary_integral_original (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    (∫ t : ℝ in Ioi 0, MatterSpace.Response.temporalWeight energy damping t •
      fullOperator (fun _ => gauge) continuous_const coupling (fun _ => scalar) continuous_const
        0 t (inversePrincipal 0 source))=
      fullG 0 energy damping positive gauge coupling scalar source := by
  simpa only [stationaryValue,value,integrand] using
    stationary_diracValue_original gauge coupling scalar energy damping positive source

theorem stationaryValue_original (gauge : GaugeProfile) (coupling : ℝ) (scalar : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    stationaryValue gauge coupling scalar energy damping initial=
      fullG 0 energy damping positive gauge coupling scalar (principal 0 initial) := by
  have generated := stationary_diracValue_original gauge coupling scalar energy damping positive (principal 0 initial)
  rw [inversePrincipal_left] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
