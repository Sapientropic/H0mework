import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Grading

/-! Every bounded scalar profile is restored exactly on top of every real-amplitude native gauge resolvent. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource ScalarGreen
noncomputable section

def FreeDiracEquation (point : BasePoint) (energy damping : ℝ) (gauge : GaugeProfile) (parameter : ℝ)
    (field source : FullMatterL2) : Prop :=
  FourierEquation point energy damping (gaugePotential gauge) parameter field
    (Complex.I • inversePrincipal point source)

theorem freeDirac_iff (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (field source : FullMatterL2) :
    FreeDiracEquation point energy damping gauge parameter field source ↔
      field=gaugeG point energy damping positive gauge parameter source := by
  constructor
  · intro solved
    have generated := nativeR_unique point energy damping positive gauge parameter field _ solved
    simpa only [gaugeG,ContinuousLinearMap.comp_apply,smul_apply,map_smul] using! generated
  · rintro rfl
    have generated := nativeR_solves point energy damping positive gauge parameter
      (Complex.I • inversePrincipal point source)
    simpa only [FreeDiracEquation,gaugeG,ContinuousLinearMap.comp_apply,smul_apply,map_smul] using! generated

def CoupledEquation (point : BasePoint) (energy damping : ℝ) (gauge : GaugeProfile) (parameter : ℝ)
    (scalar : ScalarProfile) (field source : FullMatterL2) : Prop :=
  FreeDiracEquation point energy damping gauge parameter field (source-potential scalar field)

def fullG (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) : PerturbedGreen.SpatialOperators :=
  gaugeG point energy damping positive gauge parameter-
    gaugeG point energy damping positive gauge parameter*potential scalar*gaugeG point energy damping positive gauge parameter

theorem fullG_solves (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (source : FullMatterL2) :
    CoupledEquation point energy damping gauge parameter scalar
      (fullG point energy damping positive gauge parameter scalar source) source := by
  apply (freeDirac_iff point energy damping positive gauge parameter _ _).mpr
  change gaugeG point energy damping positive gauge parameter source-
    gaugeG point energy damping positive gauge parameter (potential scalar
      (gaugeG point energy damping positive gauge parameter source))=
    gaugeG point energy damping positive gauge parameter (source-potential scalar
      (gaugeG point energy damping positive gauge parameter source-
        gaugeG point energy damping positive gauge parameter (potential scalar
          (gaugeG point energy damping positive gauge parameter source))))
  rw [map_sub (potential scalar),two_scalar_insertions_zero,sub_zero,map_sub]

theorem fullG_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) (field source : FullMatterL2)
    (solves : CoupledEquation point energy damping gauge parameter scalar field source) :
    field=fullG point energy damping positive gauge parameter scalar source := by
  have solved := (freeDirac_iff point energy damping positive gauge parameter field _).mp solves
  have twice := congrArg (fun u : FullMatterL2 => potential scalar u) solved
  rw [map_sub,map_sub,two_scalar_insertions_zero,sub_zero] at twice
  rw [map_sub,twice] at solved
  exact solved

theorem gaugeG_bound (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) :
    ‖gaugeG point energy damping positive gauge parameter‖≤damping⁻¹*‖inversePrincipal point‖ := by
  rw [gaugeG,norm_smul,Complex.norm_I,one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (nativeR_bound point energy damping positive gauge parameter) (norm_nonneg _))

theorem fullG_bound (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (gauge : GaugeProfile) (parameter : ℝ) (scalar : ScalarProfile) :
    ‖fullG point energy damping positive gauge parameter scalar‖≤
      damping⁻¹*‖inversePrincipal point‖+
        (damping⁻¹*‖inversePrincipal point‖)^2*‖potential scalar‖ := by
  let G := gaugeG point energy damping positive gauge parameter
  let M := damping⁻¹*‖inversePrincipal point‖
  have bound : ‖G‖≤M := gaugeG_bound point energy damping positive gauge parameter
  have nonneg : 0≤M := (norm_nonneg _).trans bound
  have product : ‖G*potential scalar*G‖≤M^2*‖potential scalar‖ := by
    calc
      _ ≤ ‖G‖*‖potential scalar‖*‖G‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ M*‖potential scalar‖*M := mul_le_mul
        (mul_le_mul_of_nonneg_right bound (norm_nonneg _)) bound (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact (norm_sub_le G (G*potential scalar*G)).trans (add_le_add bound product)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
