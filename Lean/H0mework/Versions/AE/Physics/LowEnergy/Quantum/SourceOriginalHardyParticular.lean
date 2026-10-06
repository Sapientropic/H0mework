import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourcePhysicalHardyWeight
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceElectricCompletedSquare
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceWeightedParticular

/-! The original action generates its physical weighted weak solution and actual retarded splice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceOriginalHardyParticular
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeEnergy GaussDiagonalHistory
open SourceKineticTranspose SourceOriginalKineticSquare SourcePhysicalKineticSquare
open SourcePhysicalHardyWeight SourceCornerWeight SourceElectricCompletedSquare
open GaussUnitaryHistory (Index)
open FullYSourceResolventGraphSplice
open scoped InnerProductSpace

theorem kinetic_weighted_cost (f : QuantumTest) :
    ‖embed (inverseHardyAction f)‖≤(2/17 : ℝ)*‖embed (kineticAction f)‖ := by
  have hn : 0 ≤ sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.le
  have he := mul_le_mul_of_nonneg_left (electric_hardy (inverseRootAction f)) hn
  have hc := source_hardy_coefficient f
  have hs := physical_kinetic_square f
  have hp : 0≤4*radialCoefficient^2*
      ‖embed (SourceCoframeVolumeCurrent.dilation (inverseVolumeAction f))‖^2 := by positivity
  have hb : (289/4 : ℝ)*‖embed (inverseHardyAction f)‖^2≤‖embed (kineticAction f)‖^2 := by
    nlinarith [sq_nonneg ‖embed (symmetricScale (inverseVolumeAction f))‖]
  nlinarith [norm_nonneg (embed (inverseHardyAction f)),norm_nonneg (embed (kineticAction f))]

def inverseWeight : diagonal.domain →ₗ[ℂ] H :=
  embed.comp (inverseHardyAction.comp coreEquiv.symm.toLinearMap)

theorem original_core_cost (x : diagonal.domain) :
    ‖inverseWeight x‖≤(2/17 : ℝ)*‖kinetic x‖ := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  change ‖embed (inverseHardyAction (coreEquiv.symm (coreEquiv f)))‖≤
    (2/17 : ℝ)*‖embed (kineticAction (coreEquiv.symm (coreEquiv f)))‖
  rw [coreEquiv.symm_apply_apply]
  exact kinetic_weighted_cost f

def solver : H →L[ℂ] H := SourceWeightedParticular.solver diagonal.domain kinetic inverseWeight

theorem solver_norm : ‖solver‖≤(2/17 : ℝ) :=
  SourceWeightedParticular.solver_bound diagonal.domain kinetic inverseWeight (2/17)
    (by norm_num) original_core_cost

theorem solver_equation (x : diagonal.domain) (f : H) :
    inner ℂ (kinetic x) (solver f)=inner ℂ (inverseWeight x) f :=
  SourceWeightedParticular.solver_equation diagonal.domain kinetic inverseWeight (2/17)
    original_core_cost x f

theorem localized_weak_equation (g : QuantumTest) (x : diagonal.domain) :
    inner ℂ (kinetic x) (solver (embed (forcingAction g)))=
      inner ℂ (x : H) (embed (localizedAction g)) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  have h := solver_equation (coreEquiv f) (embed (forcingAction g))
  change inner ℂ (kinetic (coreEquiv f)) (solver (embed (forcingAction g)))=
    sourcePair (inverseHardyAction (coreEquiv.symm (coreEquiv f))) (forcingAction g) at h
  rw [coreEquiv.symm_apply_apply,weighted_forcing_pair] at h
  exact h

/-- The source-generated weak solution meets the actual outer resolvent with its full residual. -/
theorem actual_localized_retarded_splice (F : Index) (z : ℂ) (hz : z.im≠0)
    (k : diagonal.domain) (g : QuantumTest) :
    inner ℂ (k : H) (finiteResolvent F z (embed (localizedAction g)))=
      inner ℂ (k : H) (solver (embed (forcingAction g))+
        z • finiteResolvent F z (solver (embed (forcingAction g))))+
      inner ℂ (outerResidual F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (solver (embed (forcingAction g))) :=
  actual_weak_splice F z hz k (embed (localizedAction g)) (solver (embed (forcingAction g)))
    (localized_weak_equation g)

end LowEnergy.SourceOriginalHardyParticular
