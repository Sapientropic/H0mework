import H0mework.Physics.LowEnergy.VertexTensor.Tensor

/-! The exact quadratic anisotropy removes the frame denominator at zero
momentum. The fixed-probe coefficient is continuous on the source light band. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes LightInteraction DrivenInteraction LightSpace Stage9C.Material.SpinPair Filter Topology
noncomputable section

theorem axialRoot_continuousAt (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt axialRoot q := by
  have strictOne : LightModes.momentumRadius<1 := by norm_num [LightModes.momentumRadius]
  have square : |q^2|<(sourceRoot .axialPhase).radius := by
    rw [abs_pow]
    have r := source_radius .axialPhase
    have p := momentumRadius_positive
    nlinarith [abs_nonneg q]
  exact ContinuousAt.comp (f := fun x : ℝ => x^2) (x := q)
    ((sourceRoot .axialPhase).root_continuousAt (q^2) square) (continuous_pow 2).continuousAt

theorem root_table_continuousAt (terms : List Term) (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt (fun x => value terms (axialRoot x) (x^2)) q :=
  (value_continuous terms).continuousAt.comp
    ((axialRoot_continuousAt q small).prodMk (continuous_pow 2).continuousAt)

theorem axialDerivative_continuousAt (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt axialDerivative q := by
  unfold axialDerivative
  exact continuousAt_const.add ((continuous_pow 2).continuousAt.mul
    (root_table_continuousAt (differentiate (sourceRoot .axialPhase).terms) q small))

theorem transverseNormal_continuousAt (same : Bool) (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt (transverseNormal same) q := by
  have original : ContinuousAt currentNormal q :=
    (axialRoot_continuousAt q small).add ((continuous_pow 2).continuousAt.mul
      (root_table_continuousAt responseTerms q small))
  cases same
  · exact original
  · exact original.add (((continuous_pow 2).continuousAt.const_mul 2).mul
      (root_table_continuousAt evenTerms q small))

theorem physicalTransverse_continuousAt (same : Bool) (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt (physicalTransverse same) q := by
  have denom := (axialRoot_continuousAt q small).mul ((axialDerivative_continuousAt q small).pow 2)
  have nonzero : axialRoot q*(axialDerivative q)^2≠0 :=
    mul_ne_zero (axial_root_positive q).ne' (pow_ne_zero 2 (axial_derivative_positive q small).ne')
  have generated := (((transverseNormal_continuousAt same q small).const_mul responseScale).div denom nonzero).const_mul
    ((lapse*spinScale)^2)
  change ContinuousAt (fun x => (lapse*spinScale)^2*transverseCoupling same x) q
  simp_rw [transverse_coupling_normal]
  exact generated

theorem physicalCorrection_continuousAt (same : Bool) (q : ℝ) (small : |q| ≤ LightModes.momentumRadius) :
    ContinuousAt (physicalCorrection same) q := by
  have denom := (axialRoot_continuousAt q small).mul ((axialDerivative_continuousAt q small).pow 2)
  have nonzero : axialRoot q*(axialDerivative q)^2≠0 :=
    mul_ne_zero (axial_root_positive q).ne' (pow_ne_zero 2 (axial_derivative_positive q small).ne')
  exact ((root_table_continuousAt (differenceTerms same) q small).const_mul
    ((lapse*spinScale)^2*responseScale)).div denom nonzero

def fixedMomentumCoupling (same : Bool) (momentum : Fin 3 → ℝ) : ℝ :=
  physicalTransverse same (radialMomentum momentum)+
    ((momentum 0)^2/2)*physicalCorrection same (radialMomentum momentum)

theorem fixedMomentumCoupling_projection (same : Bool) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    fixedMomentumCoupling same momentum=
      fixedProbeCoupling same (radialMomentum momentum) (momentum 0/Rotation.momentumRadius momentum) := by
  have radiusNonzero := (Rotation.momentumRadius_positive momentum nonzero).ne'
  have radial : (radialMomentum momentum)^2=(Rotation.momentumRadius momentum)^2/2 := by
    rw [radialMomentum,div_pow,spinScale_sq]
  rw [fixedMomentumCoupling,fixedProbeCoupling,physical_difference,radial,div_pow]
  field_simp

theorem fixedMomentumCoupling_frame (same : Bool) (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) :
    transportedSpatialTensor same momentum nonzero 1 1=fixedMomentumCoupling same momentum := by
  have read := transportedTensor_probe same momentum nonzero 0
  change transportedSpatialTensor same momentum nonzero (0 : Fin 3).succ (0 : Fin 3).succ=_
  exact read.trans (fixedMomentumCoupling_projection same momentum nonzero).symm

theorem radialMomentum_continuous : Continuous radialMomentum := by
  unfold radialMomentum Rotation.momentumRadius
  fun_prop

theorem fixedMomentumCoupling_continuousAt (same : Bool) (momentum : Fin 3 → ℝ)
    (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    ContinuousAt (fixedMomentumCoupling same) momentum := by
  have first := (physicalTransverse_continuousAt same _ (radial_small momentum small)).comp
    radialMomentum_continuous.continuousAt
  have second := (physicalCorrection_continuousAt same _ (radial_small momentum small)).comp
    radialMomentum_continuous.continuousAt
  have coordinate : ContinuousAt (fun k : Fin 3 → ℝ => (k 0)^2/2) momentum :=
    ((continuous_apply 0).continuousAt.pow 2).div_const 2
  exact first.add (coordinate.mul second)

theorem physicalTransverse_zero (same : Bool) : physicalTransverse same 0=486*Real.sqrt 15/390625 := by
  have atZero := (physicalTransverse_continuousAt same 0 (by simpa using momentumRadius_positive.le)).tendsto
  have limit : Tendsto (physicalTransverse same) (𝓝 0) (𝓝 (486*Real.sqrt 15/390625)) := by
    cases same
    · exact original_time_coupling_limit
    · exact physical_growth_coupling_limit
  exact tendsto_nhds_unique atZero limit

theorem fixedMomentumCoupling_zero (same : Bool) : fixedMomentumCoupling same 0=486*Real.sqrt 15/390625 := by
  have radial : radialMomentum 0=0 := by simp [radialMomentum,Rotation.momentumRadius]
  simp only [fixedMomentumCoupling,Pi.zero_apply,zero_pow (by decide : (2 : ℕ)≠0),zero_div,zero_mul,add_zero,radial,
    physicalTransverse_zero]

theorem fixedMomentumCoupling_positive (same : Bool) (momentum : Fin 3 → ℝ)
    (small : Rotation.momentumRadius momentum≤ spinScale*LightModes.momentumRadius) :
    0<fixedMomentumCoupling same momentum := by
  by_cases nonzero : momentum=0
  · rw [nonzero,fixedMomentumCoupling_zero]
    positivity
  · rw [← fixedMomentumCoupling_frame same momentum nonzero]
    exact transported_A1_positive same momentum nonzero small

end
end SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
