import H0mework.Physics.LowEnergy.PacketDynamics.Symbol

/-! The adjoint of the actual full flow is generated on the same whole spatial carrier and is strongly continuous. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace YangMills.FullPairing
noncomputable section

def adjointMatrices (time : ℝ) (frequency : Position) : FiberOperators :=
  (fullMatrices 0 time frequency).adjoint

theorem adjointMatrices_continuous : Continuous (fun pair : ℝ×Position => adjointMatrices pair.1 pair.2) :=
  ContinuousLinearMap.adjoint.continuous.comp (fullMatrices_continuous 0)

theorem adjointMatrices_bound (time : ℝ) (frequency : Position) :
    ‖adjointMatrices time frequency‖ ≤ 1+|time| * sourceRate 0 := by
  rw [adjointMatrices,ContinuousLinearMap.adjoint.norm_map]
  exact fullMatrices_bound 0 time frequency

def adjointMomentumFlow (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  liftedFamily adjointMatrices adjointMatrices_continuous (sourceRate 0)
    (norm_nonneg _) adjointMatrices_bound time

theorem adjointMomentumFlow_ae (time : ℝ) (field : FullMatterL2) :
    adjointMomentumFlow time field =ᵐ[volume] fun frequency => adjointMatrices time frequency (field frequency) :=
  liftedFamily_ae adjointMatrices adjointMatrices_continuous (sourceRate 0)
    (norm_nonneg _) adjointMatrices_bound time field

theorem adjointMomentumFlow_original (time : ℝ) : adjointMomentumFlow time=(momentumFlow 0 time).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro left right
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [adjointMomentumFlow_ae time left,momentumFlow_ae 0 time right] with frequency first second
  change inner ℂ (adjointMomentumFlow time left frequency) (right frequency)=
    inner ℂ (left frequency) (momentumFlow 0 time right frequency)
  rw [first,second]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

def adjointFlow (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((adjointMomentumFlow time).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem adjointFlow_fourier (time : ℝ) (field : FullMatterL2) :
    fourier (adjointFlow time field)=adjointMomentumFlow time (fourier field) :=
  fourier.apply_symm_apply _

theorem adjointFlow_original (time : ℝ) : adjointFlow time=(spatialFlow 0 time).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro left right
  rw [← fourier.inner_map_map (adjointFlow time left) right,
    ← fourier.inner_map_map left (spatialFlow 0 time right),adjointFlow_fourier,spatialFlow_fourier,
    adjointMomentumFlow_original]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem adjointFlow_stronglyContinuous (field : FullMatterL2) :
    Continuous (fun time => adjointFlow time field) :=
  fourier.symm.continuous.comp
    (liftedFamily_stronglyContinuous adjointMatrices adjointMatrices_continuous (sourceRate 0)
      (norm_nonneg _) adjointMatrices_bound (fourier field))

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
