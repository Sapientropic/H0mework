import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceOriginalHamiltonianSquare
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourcePhysicalKineticSquare

/-! The full signed Hamiltonian cost returns to the original core and actual retarded source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourcePhysicalHamiltonianSquare
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussMatterCore GaussDiagonalHistory GaussHistoryHilbert
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceDilationRemainder SourceOriginalHamiltonianSquare SourcePhysicalKineticSquare
open SourceOriginalKineticSquare (radialCoefficient)
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceEscapeCurrent SourceMinimalGraphParticular FullYSourceResolventGraphSplice
open GaussUnitaryHistory (Index)
open scoped ContDiff InnerProductSpace

theorem inverse_root_matter : Commute inverseRootAction matterAction := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,matterAction,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply DFunLike.ext
  intro z
  change (inverseRootVolume z : ℂ) • GaussQuantumMultiplier.quantized (localMatrix i b z) (f z)=
    GaussQuantumMultiplier.quantized (localMatrix i b z) ((inverseRootVolume z : ℂ) • f z)
  exact (map_smul _ _ _).symm

theorem inverse_root_real (a : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) :
    Commute inverseRootAction (multiply a smooth) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (inverseRootVolume z : ℂ) (a z : ℂ) (f z)

private theorem physical_return (A : CoreEnd) (commutes : Commute inverseRootAction A)
    (f : QuantumTest) :
    sourcePair (inverseVolumeAction f) (volumeAction (A (inverseVolumeAction f)))=
      sourcePair (inverseRootAction f) (A (inverseRootAction f)) := by
  have hU (a b : QuantumTest) : sourcePair a (volumeAction b)=sourcePair (volumeAction a) b :=
    multiply_pair _ _ _ _
  have hS (a b : QuantumTest) : sourcePair a (inverseRootAction b)=sourcePair (inverseRootAction a) b :=
    multiply_pair _ _ _ _
  rw [hU,volume_inverse,←inverse_root_square]
  have hcomm (g : QuantumTest) : A (inverseRootAction g)=inverseRootAction (A g) :=
    (LinearMap.congr_fun commutes.eq g).symm
  rw [hcomm,hS]

def signedCost (f : QuantumTest) : ℝ :=
  ‖embed (symmetricScale (inverseVolumeAction f))‖^2+
  4*radialCoefficient^2*‖embed (dilation (inverseVolumeAction f))‖^2+
  sourceTime 0*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
  (sourceTime 0/2)*(sourcePair (inverseRootAction f) (matterAction (inverseRootAction f))).re+
  (3*sourceTime 0/2)*(sourcePair (inverseRootAction f) (localAction (inverseRootAction f))).re+
  sourceTime 0*(sourcePair (inverseRootAction f) (spatialAction (inverseRootAction f))).re

theorem physical_hamiltonian_square (f : QuantumTest) :
    ‖embed (diagonalAction f)‖^2=signedCost f := by
  have h := original_hamiltonian_square (inverseVolumeAction f)
  rw [volume_inverse,electric_physical_return,
    physical_return matterAction inverse_root_matter,
    physical_return localAction (inverse_root_real _ _),
    physical_return spatialAction (inverse_root_real _ _)] at h
  exact h

theorem original_core_cost (x : diagonal.domain) :
    ‖diagonal x‖^2=signedCost (coreEquiv.symm x) :=
  physical_hamiltonian_square (coreEquiv.symm x)

theorem source_core_action (F : Index) (z : ℂ) (hz : z.im≠0) (k : diagonal.domain) :
    diagonal (sourceCore F z hz k)=
      (k : H)+z • finiteResolvent F z (k : H)+finiteProjectionDefect F z hz k := by
  have hr := congrArg (fun A : H →L[ℂ] H => A (k : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z (k : H))-
    z • finiteResolvent F z (k : H)=(k : H) at hr
  change diagonal (sourceCore F z hz k)=
    (k : H)+z • finiteResolvent F z (k : H)+
      (diagonal (sourceCore F z hz k)-
        GaussGradedCompression.compression F (finiteResolvent F z (k : H)))
  have hc : GaussGradedCompression.compression F (finiteResolvent F z (k : H))=
      (k : H)+z • finiteResolvent F z (k : H) := sub_eq_iff_eq_add.mp hr
  rw [hc]
  abel

/-- The actual conjugate-frequency core pays the complete signed cost, including its projection defect. -/
theorem actual_retarded_hamiltonian_cost (F : Index) (z : ℂ) (hz : z.im≠0)
    (k : diagonal.domain) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    ‖(k : H)+star z • finiteResolvent F (star z) (k : H)+
      finiteProjectionDefect F (star z) hs k‖^2=
      signedCost (coreEquiv.symm (sourceCore F (star z) hs k)) := by
  dsimp only
  rw [←source_core_action]
  exact original_core_cost _

end LowEnergy.SourcePhysicalHamiltonianSquare
