import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Triangular
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Native

/-! Original gauge and scalar histories drive a genuine L² Dirac source through the original temporal principal inverse. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

theorem gauge_forward_joint :
    Continuous (fun tv : ℝ × FullMatterL2 => gaugeUnitary gauge continuousGauge coupling 0 tv.1 tv.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun t => (gaugeUnitary gauge continuousGauge coupling 0 t).isometry.lipschitz)
    (gaugeUnitary_continuous gauge continuousGauge coupling 0)

include continuousScalar in
theorem scalarInteraction_joint :
    Continuous (fun tv : ℝ × FullMatterL2 => scalarInteraction gauge continuousGauge coupling scalar tv.1 tv.2) := by
  have inside := ((scalarDriftMap.continuous.comp continuousScalar).comp continuous_fst).clm_apply
    (gauge_forward_joint gauge continuousGauge coupling)
  have composed := (gaugeUnitary_reverse_joint gauge continuousGauge coupling 0).comp
    (continuous_fst.prodMk inside)
  simpa only [scalarInteraction_apply,Function.comp_def] using! composed

def sourceInteraction (source : ℝ → FullMatterL2) (time : ℝ) : FullMatterL2 :=
  gaugeUnitary gauge continuousGauge coupling time 0 (inversePrincipal 0 (source time))

theorem sourceInteraction_continuous (source : ℝ → FullMatterL2) (continuousSource : Continuous source) :
    Continuous (sourceInteraction gauge continuousGauge coupling source) := by
  have composed := (gaugeUnitary_reverse_joint gauge continuousGauge coupling 0).comp
    (continuous_id.prodMk ((inversePrincipal 0).continuous.comp continuousSource))
  simpa only [sourceInteraction,Function.comp_def,id_eq] using! composed

def sourceDevelopment (source : ℝ → FullMatterL2) (start : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  gaugeUnitary gauge continuousGauge coupling 0 time
    (forcedCurve (scalarInteraction gauge continuousGauge coupling scalar)
      (sourceInteraction gauge continuousGauge coupling source) start
      (gaugeUnitary gauge continuousGauge coupling start 0 initial) time)

theorem sourceDevelopment_starts (source : ℝ → FullMatterL2) (start : ℝ) (initial : FullMatterL2) :
    sourceDevelopment gauge continuousGauge coupling scalar source start initial start=initial := by
  rw [sourceDevelopment,forcedCurve_starts,gaugeUnitary_inverse]

theorem sourceDevelopment_interaction (source : ℝ → FullMatterL2) (start time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary gauge continuousGauge coupling time 0
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)=
      forcedCurve (scalarInteraction gauge continuousGauge coupling scalar)
        (sourceInteraction gauge continuousGauge coupling source) start
        (gaugeUnitary gauge continuousGauge coupling start 0 initial) time := by
  rw [sourceDevelopment,gaugeUnitary_inverse]

include continuousScalar in
theorem sourceDevelopment_equation (source : ℝ → FullMatterL2) (continuousSource : Continuous source)
    (start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => gaugeUnitary gauge continuousGauge coupling t 0
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial t))
      (gaugeUnitary gauge continuousGauge coupling time 0
        (scalarDriftMap (scalar time)
          (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)+
          inversePrincipal 0 (source time))) time := by
  simp only [sourceDevelopment_interaction]
  have generated := forcedCurve_equation (scalarInteraction gauge continuousGauge coupling scalar)
    (scalarInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge coupling scalar scalar)
    (sourceInteraction gauge continuousGauge coupling source)
    (sourceInteraction_continuous gauge continuousGauge coupling source continuousSource) start time
    (gaugeUnitary gauge continuousGauge coupling start 0 initial)
  simpa only [sourceDevelopment,scalarInteraction_apply,sourceInteraction,map_add] using! generated

include continuousScalar in
theorem sourceDevelopment_continuous (source : ℝ → FullMatterL2) (continuousSource : Continuous source)
    (start : ℝ) (initial : FullMatterL2) :
    Continuous (sourceDevelopment gauge continuousGauge coupling scalar source start initial) := by
  have transformed : Continuous (fun t => gaugeUnitary gauge continuousGauge coupling t 0
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (sourceDevelopment_equation gauge continuousGauge coupling scalar continuousScalar source continuousSource start t initial).continuousAt)
  have composed := (gauge_forward_joint gauge continuousGauge coupling).comp
    (continuous_id.prodMk transformed)
  simpa only [Function.comp_def,id_eq,gaugeUnitary_inverse] using! composed

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
