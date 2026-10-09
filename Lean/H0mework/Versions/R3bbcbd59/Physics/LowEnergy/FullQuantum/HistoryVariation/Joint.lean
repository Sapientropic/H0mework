import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryVariation.Flow

/-! The same source flow and its inverse are jointly continuous after removal of the original free motion. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryForcing
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

theorem scalarIntegral_continuous :
    Continuous (scalarIntegralOperator gauge continuousGauge coupling scalar continuousScalar 0) :=
  insertionOperator_continuous (scalarInteraction gauge continuousGauge coupling scalar)
    (scalarInteraction_continuous gauge continuousGauge coupling scalar continuousScalar)
    (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
    (scalarInteraction_bound gauge continuousGauge coupling scalar) 0

theorem interaction_joint :
    Continuous (fun tx : ℝ × FullMatterL2 => interaction gauge continuousGauge coupling scalar continuousScalar tx.1 tx.2) := by
  have inside := continuous_snd.add
    (((scalarIntegral_continuous gauge continuousGauge coupling scalar continuousScalar).comp continuous_fst).clm_apply continuous_snd)
  have gaugeJoint : Continuous (fun tx : ℝ × FullMatterL2 => gaugeInteraction gauge continuousGauge coupling tx.1 tx.2) :=
    continuous_prod_of_continuous_lipschitzWith' _ 1
      (fun t => (gaugeInteraction gauge continuousGauge coupling t).isometry.lipschitz)
      (gaugeInteraction_continuous gauge continuousGauge coupling)
  have composed := gaugeJoint.comp (continuous_fst.prodMk inside)
  simpa only [interaction_apply,Function.comp_def] using! composed

theorem inverseInteraction_joint :
    Continuous (fun tx : ℝ × FullMatterL2 => inverseInteraction gauge continuousGauge coupling scalar continuousScalar tx.1 tx.2) := by
  have back := (gaugeUnitary_reverse_joint gauge continuousGauge coupling 0).comp
    (continuous_fst.prodMk spatialFree_joint)
  have result := back.sub
    (((scalarIntegral_continuous gauge continuousGauge coupling scalar continuousScalar).comp continuous_fst).clm_apply back)
  simpa only [inverseInteraction_apply,Function.comp_def] using! result

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryVariation
