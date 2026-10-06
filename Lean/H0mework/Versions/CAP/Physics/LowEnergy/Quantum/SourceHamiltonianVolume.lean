import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCoframeVolumeCurrent

/-! The complete original Hamiltonian retains the same source volume current. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceHamiltonianVolume
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussNativeEnergy GaussNativeForm GaussLiveMomentum GaussCoframeForm
open SourceCoframeVolume SourceCoframeVolumeCurrent
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology InnerProductSpace

private theorem real_smul_complex (a : ℝ) (f : FockFiber) : a • f=(a : ℂ) • f := by
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem commutes_apply {A : CoreEnd} (hA : Commute A volumeAction) (f : QuantumTest) :
    A (volumeAction f)=volumeAction (A f) := by
  simpa only [Module.End.mul_apply] using! LinearMap.congr_fun hA.eq f

private theorem vadd {A B : CoreEnd} (hA : Commute A volumeAction)
    (hB : Commute B volumeAction) : Commute (A+B) volumeAction := by
  apply LinearMap.ext
  intro f
  change A (volumeAction f)+B (volumeAction f)=volumeAction (A f+B f)
  rw [map_add, commutes_apply hA f, commutes_apply hB f]

private theorem vsmul {A : CoreEnd} (hA : Commute A volumeAction) (c : ℂ) :
    Commute (c • A) volumeAction := by
  apply LinearMap.ext
  intro f
  change c • A (volumeAction f)=volumeAction (c • A f)
  rw [map_smul, commutes_apply hA f]

private theorem vcomp {A B : CoreEnd} (hA : Commute A volumeAction)
    (hB : Commute B volumeAction) : Commute (A.comp B) volumeAction := by
  apply LinearMap.ext
  intro f
  change A (B (volumeAction f))=volumeAction (A (B f))
  rw [commutes_apply hB f, commutes_apply hA (B f)]

private theorem vsum {ι : Type*} [Fintype ι] {A : ι → CoreEnd}
    (h : ∀ i, Commute (A i) volumeAction) : Commute (∑ i, A i) volumeAction := by
  apply LinearMap.ext
  intro f
  simpa only [Module.End.mul_apply, LinearMap.sum_apply, map_sum] using!
    (Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => commutes_apply (h i) f))

theorem directional_volume (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (volumeAction f) z = volume z • directional v f z := by
  rw [directional_apply, volume_action_real,
    fderiv_fun_smul (volume_smooth.differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  have hd : fderiv ℝ volume z (direction v z)=0 := by
    rw [volume_derivative]
    simp [direction]
  change volume z • fderiv ℝ f z (direction v z)+fderiv ℝ volume z (direction v z) • f z=_
  rw [hd, zero_smul, add_zero]
  rfl

theorem native_momentum_volume (v : Ambient) : Commute (covariantMomentum v) volumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (volumeAction f) z+
      connection v z ((volume z : ℂ) • f z)) =
    (volume z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))
  rw [directional_volume, real_smul_complex, map_smul, ←smul_add, smul_comm]

private theorem paired_volume (A B : CoreEnd) (pair : Paired B A)
    (hA : Commute A volumeAction) : Commute B volumeAction := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have hc := LinearMap.congr_fun hA.eq f
  change sourcePair f (B (volumeAction g))=sourcePair f (volumeAction (B g))
  calc
    _ = sourcePair (A f) (volumeAction g) := pair _ _
    _ = sourcePair (volumeAction (A f)) g := multiply_pair _ _ _ _
    _ = sourcePair (A (volumeAction f)) g := congrArg (fun x => sourcePair x g) hc.symm
    _ = sourcePair (volumeAction f) (B g) := (pair _ _).symm
    _ = _ := (multiply_pair _ _ _ _).symm

theorem native_adjoint_volume (v : Ambient) :
    Commute (GaussMomentumAdjoint.adjoint v) volumeAction :=
  paired_volume _ _ (GaussNativeForm.adjoint_pair v) (native_momentum_volume v)

theorem real_volume (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) :
    Commute (multiply a ha) volumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (a z : ℂ) (volume z : ℂ) (f z)

theorem scalar_kinetic_volume : Commute scalarKinetic volumeAction :=
  vsmul (vsum (fun a => vcomp (native_adjoint_volume (scalarDirection a))
    (vcomp (real_volume _ _) (native_momentum_volume (scalarDirection a))))) (1/2)

theorem gauge_kinetic_volume : Commute gaugeKinetic volumeAction :=
  vsmul (vsum (fun a => vsum (fun i => vsum (fun j =>
    vcomp (native_adjoint_volume (gaugeDirection i a))
      (vcomp (real_volume _ _) (native_momentum_volume (gaugeDirection j a))))))) (1/2)

private theorem zero_gradient (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) : gradientAction i=0 := by
  rcases hi with rfl | rfl | rfl <;>
    apply LinearMap.ext <;> intro f <;> apply DFunLike.ext <;> intro z <;>
    change (volumeGradient z _ : ℂ) • f z=0 <;> simp [volumeGradient]

private theorem coframe_momentum_volume (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (GaussCoframeCore.momentum i) volumeAction := by
  apply LinearMap.ext
  intro f
  simpa only [zero_gradient i hi, LinearMap.zero_apply, smul_zero, add_zero]
    using! SourceCoframeVolume.momentum_volume i f

private theorem coframe_adjoint_volume (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (GaussCoframeCore.adjoint i) volumeAction := by
  apply LinearMap.ext
  intro f
  simpa only [zero_gradient i hi, LinearMap.zero_apply, smul_zero, add_zero]
    using! SourceCoframeVolume.adjoint_volume i f

private theorem quantum_volume
    (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart,
      ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) volumeAction :=
  scalar_volume_commutes _ _

private theorem current_volume (a : Fin 7) : Commute (GaussCoframeSpin.current a) volumeAction :=
  quantum_volume _ _

private theorem mixed_volume (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (hi : i=1 ∨ i=3 ∨ i=4) :
    Commute (mixed i a c smooth) volumeAction := by
  exact vsmul (vadd (vcomp (current_volume a) (vcomp (real_volume _ _) (coframe_momentum_volume i hi)))
    (vcomp (coframe_adjoint_volume i hi) (vcomp (real_volume _ _) (current_volume a)))) (1/2)

private theorem current_action_volume : Commute currentAction volumeAction :=
  vadd (vadd (vadd (mixed_volume 1 5 _ _ (Or.inl rfl))
    (mixed_volume 3 3 _ _ (Or.inr (Or.inl rfl))))
    (mixed_volume 3 4 _ _ (Or.inr (Or.inl rfl))))
    (mixed_volume 4 3 _ _ (Or.inr (Or.inr rfl)))

private theorem spin_volume (a : Fin 7) : Commute (spinSquare a) volumeAction :=
  vsmul (vcomp (current_volume a) (vcomp (real_volume _ _) (current_volume a))) _

private theorem number_volume : Commute number volumeAction := quantum_volume _ _

private theorem number_shift_volume : Commute numberShift volumeAction :=
  vsmul (vadd (vcomp number_volume (real_volume _ _))
    (vcomp (real_volume _ _) number_volume)) (1/2)

private theorem matter_volume : Commute GaussMatterCore.matterAction volumeAction :=
  vsum (fun i => vsum (fun b => quantum_volume (GaussMatterCore.localMatrix i b)
    (GaussMatterCore.local_smooth i b)))

private def rest : CoreEnd := scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
  GaussNativePotential.potential_smooth+currentAction+(∑ a : Fin 7, spinSquare a)+numberShift+
  multiply volumePotential volumePotential_smooth+GaussMatterCore.matterAction

private theorem rest_volume : Commute rest volumeAction :=
  vadd (vadd (vadd (vadd (vadd (vadd (vadd scalar_kinetic_volume gauge_kinetic_volume)
    (real_volume _ _)) current_action_volume) (vsum spin_volume)) number_shift_volume)
    (real_volume _ _)) matter_volume

theorem full_source_volume_current :
    GaussDiagonalHistory.diagonalAction*volumeAction-volumeAction*GaussDiagonalHistory.diagonalAction =
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • SourceCoframeVolumeCurrent.dilation := by
  have hd : GaussDiagonalHistory.diagonalAction=GaussCoframeKinetic.kinetic+rest := by
    unfold GaussDiagonalHistory.diagonalAction nativeAction coframeAction rest
    abel
  rw [hd, add_mul, mul_add, rest_volume.eq]
  have he : (GaussCoframeKinetic.kinetic*volumeAction+volumeAction*rest)-
      (volumeAction*GaussCoframeKinetic.kinetic+volumeAction*rest) =
      GaussCoframeKinetic.kinetic*volumeAction-volumeAction*GaussCoframeKinetic.kinetic := by abel
  exact he.trans coframe_volume_current

theorem kinetic_volume_current :
    SourceKineticTranspose.kineticAction*volumeAction-volumeAction*SourceKineticTranspose.kineticAction =
      (-3*Complex.I*(sourceTime 0 : ℂ)/4) • SourceCoframeVolumeCurrent.dilation := by
  have hR : Commute SourceKineticTranspose.remainderAction volumeAction :=
    vadd (vadd matter_volume (real_volume _ _)) (real_volume _ _)
  have h := full_source_volume_current
  rw [SourceKineticTranspose.action_split, add_mul, mul_add, hR.eq] at h
  simpa only [add_sub_add_right_eq_sub] using h

end LowEnergy.SourceHamiltonianVolume
