import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Grading

/-! The original scalar history becomes a pairwise nilpotent interaction on the same spatial gauge flow. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen PerturbedGreen Triangular
noncomputable section

theorem gaugeUnitary_reverse_continuous (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon finish : ℝ) (initial : FullMatterL2) :
    Continuous (fun t => gaugeUnitary profile continuousProfile epsilon t finish initial) := by
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_iff_dist_tendsto_zero.mpr
  have distances (t : ℝ) :
      dist (gaugeUnitary profile continuousProfile epsilon t finish initial)
          (gaugeUnitary profile continuousProfile epsilon time finish initial)=
        dist initial (gaugeUnitary profile continuousProfile epsilon finish t
          (gaugeUnitary profile continuousProfile epsilon time finish initial)) := by
    have same := (gaugeUnitary profile continuousProfile epsilon finish t).isometry.dist_eq
      (gaugeUnitary profile continuousProfile epsilon t finish initial)
      (gaugeUnitary profile continuousProfile epsilon time finish initial)
    rw [gaugeUnitary_inverse] at same
    exact same.symm
  simp_rw [distances]
  have limit := ((continuous_const : Continuous (fun _ : ℝ => initial)).dist (gaugeUnitary_continuous profile continuousProfile epsilon finish
    (gaugeUnitary profile continuousProfile epsilon time finish initial))).tendsto time
  simpa only [gaugeUnitary_inverse,dist_self] using limit

theorem gaugeUnitary_reverse_joint (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon finish : ℝ) :
    Continuous (fun tv : ℝ × FullMatterL2 => gaugeUnitary profile continuousProfile epsilon tv.1 finish tv.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun t => (gaugeUnitary profile continuousProfile epsilon t finish).isometry.lipschitz)
    (gaugeUnitary_reverse_continuous profile continuousProfile epsilon finish)

def scalarDriftMap : ScalarProfile →L[ℂ] SpatialOperators :=
  (-(ContinuousLinearMap.compL ℂ FullMatterL2 FullMatterL2 FullMatterL2) (inversePrincipal 0)).comp
    (((ContinuousLinearMap.id ℂ FiberOperators).holderL volume ⊤ 2 2).comp (scalarMap.compLpL ⊤ volume))

theorem scalarDriftMap_apply (profile : ScalarProfile) (field : FullMatterL2) :
    scalarDriftMap profile field= -inversePrincipal 0 (potential profile field) := rfl

theorem scalarDrift_six (profile : ScalarProfile) (field : FullMatterL2) :
    six (scalarDriftMap profile field)=scalarDriftMap profile field := by
  rw [scalarDriftMap_apply,map_neg,inversePrincipal_six,six_potential]

theorem scalarDrift_kills_six (profile : ScalarProfile) (field : FullMatterL2) :
    scalarDriftMap profile (six field)=0 := by
  rw [scalarDriftMap_apply,potential_six,map_zero,neg_zero]

def scalarInteraction (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (time : ℝ) : SpatialOperators :=
  (gaugeUnitary gauge continuousGauge epsilon time 0).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((scalarDriftMap (scalar time)).comp
      (gaugeUnitary gauge continuousGauge epsilon 0 time).toContinuousLinearEquiv.toContinuousLinearMap)

theorem scalarInteraction_apply (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (time : ℝ) (field : FullMatterL2) :
    scalarInteraction gauge continuousGauge epsilon scalar time field=
      gaugeUnitary gauge continuousGauge epsilon time 0
        (scalarDriftMap (scalar time) (gaugeUnitary gauge continuousGauge epsilon 0 time field)) := rfl

theorem scalarInteraction_continuous (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar) (field : FullMatterL2) :
    Continuous (fun t => scalarInteraction gauge continuousGauge epsilon scalar t field) := by
  have inside := (scalarDriftMap.continuous.comp continuousScalar).clm_apply
    (gaugeUnitary_continuous gauge continuousGauge epsilon 0 field)
  have composed := (gaugeUnitary_reverse_joint gauge continuousGauge epsilon 0).comp (continuous_id.prodMk inside)
  simpa only [scalarInteraction_apply,Function.comp_def,id_eq] using! composed

theorem scalarInteraction_bound (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (time : ℝ) (field : FullMatterL2) :
    ‖scalarInteraction gauge continuousGauge epsilon scalar time field‖≤
      ‖scalarDriftMap (scalar time)‖*‖field‖ := by
  rw [scalarInteraction_apply,LinearIsometryEquiv.norm_map]
  exact ((scalarDriftMap (scalar time)).le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

theorem scalarInteraction_twice_zero (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (first second : ℝ → ScalarProfile) (s t : ℝ) (field : FullMatterL2) :
    scalarInteraction gauge continuousGauge epsilon first s
      (scalarInteraction gauge continuousGauge epsilon second t field)=0 := by
  have image : six (scalarInteraction gauge continuousGauge epsilon second t field)=
      scalarInteraction gauge continuousGauge epsilon second t field := by
    rw [scalarInteraction_apply,gaugeUnitary_six,scalarDrift_six]
  have kernel (v : FullMatterL2) : scalarInteraction gauge continuousGauge epsilon first s (six v)=0 := by
    rw [scalarInteraction_apply,← gaugeUnitary_six,scalarDrift_kills_six,map_zero]
  rw [← image]
  exact kernel _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
