import H0mework.Physics.LowEnergyEvolution.Gauge

/-! Exact time-dilation response of the source coframe Hodge on one coordinate two-form. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open Stage9C.Material.SpinPair LowEnergy.Evolution
open scoped Topology
noncomputable section

def timeDilationCoframe (parameter : ℝ) : LorentzianCoframe :=
  diagonalCoframe (lapse*(1+parameter)) 1

def magneticProbe : GaugeTwoForm := ![0,0,0,1,0,0]

def timeDilationHodgeCoefficient (parameter : ℝ) : ℝ :=
  coframeGaugeSpacetimeHodgeLinear (timeDilationCoframe parameter) magneticProbe 0

theorem timeDilationHodge_value (parameter : ℝ) (nonzero : lapse*(1+parameter) ≠ 0) :
    timeDilationHodgeCoefficient parameter = (lapse*(1+parameter))⁻¹ := by
  unfold timeDilationHodgeCoefficient timeDilationCoframe
  rw [diagonalHodge _ 1 nonzero (by norm_num)]
  simp [magneticProbe]

theorem timeDilationHodge_derivative :
    HasDerivAt timeDilationHodgeCoefficient (-lapse⁻¹) 0 := by
  have nonzero : ∀ᶠ parameter : ℝ in 𝓝 0, lapse*(1+parameter) ≠ 0 := by
    have continuous : ContinuousAt (fun parameter : ℝ => lapse*(1+parameter)) 0 := by fun_prop
    exact continuous.eventually_ne (by simpa using ne_of_gt lapse_pos)
  have equal : timeDilationHodgeCoefficient =ᶠ[𝓝 0] fun parameter => (lapse*(1+parameter))⁻¹ := by
    filter_upwards [nonzero] with parameter h
    exact timeDilationHodge_value parameter h
  have derivative := (((hasDerivAt_id (0:ℝ)).const_add 1).const_mul lapse).inv
    (by simpa using ne_of_gt lapse_pos)
  have normalized : HasDerivAt (fun parameter : ℝ => (lapse*(1+parameter))⁻¹) (-lapse⁻¹) 0 := by
    convert! derivative using 1
    simp only [id_eq, add_zero, mul_one]
    field_simp [ne_of_gt lapse_pos]
  exact normalized.congr_of_eventuallyEq equal

/-- Under the ordinary coordinate pullback `t ↦ (1+ε)t`, the 23 input stays fixed
while the 01 output gains the factor `1+ε`. -/
def coordinatePullbackHodgeCoefficient (parameter : ℝ) : ℝ := (1+parameter)*lapse⁻¹

theorem coordinatePullbackHodge_derivative :
    HasDerivAt coordinatePullbackHodgeCoefficient lapse⁻¹ 0 := by
  convert! ((hasDerivAt_id (0:ℝ)).const_add 1).mul_const lapse⁻¹ using 1
  simp

theorem timeDilationHodge_mismatch :
    HasDerivAt (fun parameter => timeDilationHodgeCoefficient parameter-
      coordinatePullbackHodgeCoefficient parameter) (-2*lapse⁻¹) 0 ∧ -2*lapse⁻¹ ≠ 0 := by
  constructor
  · convert! timeDilationHodge_derivative.sub coordinatePullbackHodge_derivative using 1
    ring
  · exact mul_ne_zero (by norm_num) (inv_ne_zero (ne_of_gt lapse_pos))

end
end SaturationMonoid.PhysicsCore.LowEnergy.ActiveGauge
