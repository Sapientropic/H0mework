import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeMatterCovarianceCancellation
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceShiftedBulkTimeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGeometricBulkTimeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussMatterCore GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceScalarOscillatorAbsorption SourceScalarShiftedBulk SourceShiftedBulkTimeBudget
open SourceUnmixedPotentialCancellation SourceNativeMatterCovarianceCancellation SourceMixedCurrentCancellation
open SourceDilationRemainder GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] scalarKinetic gaugeKinetic localAction magneticAction matterAction
  inverseVolumeAction volumeAction scalarBulk diagonalAction geometricAction

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (c z : ℂ) (f z)

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := by
    unfold inverseVolumeAction
    exact real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem scalar_bulk_commute (A : End) (hV : Commute A inverseVolumeAction)
    (hK : Commute A scalarKinetic) (hL : Commute A localAction) : Commute A scalarBulk := by
  unfold scalarBulk
  exact ((hV.mul_right hK).smul_right _).add_right ((hV.mul_right hL).smul_right _)

private theorem gauge_scalar_bulk : Commute gaugeKinetic scalarBulk :=
  scalar_bulk_commute _ (inverse_commute _ gauge_kinetic_volume)
    original_scalar_gauge_commute.symm original_gauge_local_commute

private theorem magnetic_scalar_bulk : Commute magneticAction scalarBulk := by
  apply scalar_bulk_commute
  · unfold magneticAction inverseVolumeAction
    exact real_commute _ _ _ _
  · exact original_scalar_magnetic_commute.symm
  · unfold magneticAction localAction
    exact real_commute _ _ _ _

private theorem matter_scalar_bulk : Commute matterAction scalarBulk := by
  apply scalar_bulk_commute
  · unfold inverseVolumeAction
    exact matter_real _ _
  · exact original_scalar_matter_commute.symm
  · unfold localAction
    exact matter_real _ _

private theorem source_split : diagonalAction=scalarHamiltonian+gaugeKinetic+
    magneticAction+matterAction+geometricAction := by
  have h := original_interaction_decomposition
  simp only [interactionAction,geometricAction,scalarHamiltonian] at h ⊢
  linear_combination (norm := module) h

private theorem hs_inverse : Commute scalarHamiltonian inverseVolumeAction := by
  unfold scalarHamiltonian
  apply Commute.add_left
  · exact inverse_commute _ scalar_kinetic_volume
  · unfold localAction inverseVolumeAction
    exact real_commute _ _ _ _

private theorem hs_gauge : Commute scalarHamiltonian gaugeKinetic := by
  unfold scalarHamiltonian
  exact original_scalar_gauge_commute.add_left original_gauge_local_commute.symm

private theorem deletion {R : Type*} [Ring R] [Algebra ℂ R]
    (Hs K M N G V Bs D : R)
    (hVK : Commute K V) (hHsV : Commute Hs V) (hHsK : Commute Hs K)
    (hKBs : Commute K Bs) (hMBs : Commute M Bs) (hNBs : Commute N Bs)
    (hMV : Commute M V) (hNV : Commute N V) (hNK : K*N-N*K=D) :
    (((Hs+K+M+N+G)-Hs)*Bs-Bs*((Hs+K+M+N+G)-Hs))+
      ((Hs+K+M+N+G)*((36 : ℂ) • (V*K))-((36 : ℂ) • (V*K))*(Hs+K+M+N+G))=
        G*(Bs+(36 : ℂ) • (V*K))-(Bs+(36 : ℂ) • (V*K))*G+
          (36 : ℂ) • (V*(M*K-K*M-D)) := by
  rw [←hNK]
  simp only [add_mul,mul_add,sub_mul,mul_sub,mul_smul_comm,smul_mul_assoc,
    hKBs.eq,hMBs.eq,hNBs.eq]
  simp only [←mul_assoc,hHsV.eq,hVK.eq,hMV.eq,hNV.eq]
  simp only [mul_assoc,hHsK.eq,smul_sub]
  module


/-- After scalar absorption, the original current has only the geometric commutator and the explicit gauge forces. -/
def geometricForceCurrent : End :=
  geometricAction*(scalarBulk+(36 : ℂ) • (inverseVolumeAction*gaugeKinetic))-
    (scalarBulk+(36 : ℂ) • (inverseVolumeAction*gaugeKinetic))*geometricAction+
      (36 : ℂ) • (inverseVolumeAction*(magneticAction*gaugeKinetic-gaugeKinetic*magneticAction-gaugeMatterDivergence))

/-- No scalar, vacuum-offset, mixed kinetic or scalar/matter current survives in this original-core identity. -/
theorem original_remaining_geometric_force : remainingCurrentComplete=geometricForceCurrent := by
  have hMV : Commute magneticAction inverseVolumeAction := by
    unfold magneticAction inverseVolumeAction
    exact real_commute _ _ _ _
  have hNV : Commute matterAction inverseVolumeAction := by
    unfold inverseVolumeAction
    exact matter_real _ _
  rw [remainingCurrentComplete,remainingHamiltonian,source_split]
  exact deletion (R := End) _ _ _ _ _ _ _ _
    (inverse_commute _ gauge_kinetic_volume) hs_inverse hs_gauge
    gauge_scalar_bulk magnetic_scalar_bulk matter_scalar_bulk hMV hNV original_gauge_matter_current

open SourceBulkTwoTime SourceInverseNoetherEnergy SourceFourPoleEnergyClosed
open SourceScalarSignedInverseReturn SourceScalarInverseRetardedBudget Filter MeasureTheory
attribute [local irreducible] coreTime bulkAction sourcePair closedJointCost formPrice

/-- The same original time remainder now retains only full raised-defect, geometry and first-order matter force. -/
theorem original_time_remainder (F : Index) (μ : ℝ) (T : End) (g : diagonal.domain) :
    remainingTimeComplete F μ T g=∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
      ((sourcePair (SourceScalarPositiveBulkWard.raisedDefect F T (coreTime F g t))
        (bulkAction (T (coreTime F g t)))).im-
        (sourcePair (T (coreTime F g t)) (geometricForceCurrent (T (coreTime F g t)))).im/2) := by
  simp only [remainingTimeComplete,remainingRaised,original_remaining_geometric_force]

/-- The complete original cost consumes all exact cancellations on the same cutoff and cofinal F event. -/
theorem actual_original_geometric_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (hgap : 2*sourceTime 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε+
          (4*Real.pi*formPrice sharp*μ⁻¹^2*‖(k : H)‖^2/(μ-2*sourceTime 0))*
            (∫ t : ℝ in Set.Ioi 0,Real.exp (-2*μ*t)*
              ((sourcePair (SourceScalarPositiveBulkWard.raisedDefect F (theta m ell) (coreTime F g t))
                (bulkAction (theta m ell (coreTime F g t)))).im-
                (sourcePair (theta m ell (coreTime F g t))
                  (geometricForceCurrent (theta m ell (coreTime F g t)))).im/2)) := by
  simpa only [original_time_remainder] using!
    actual_original_shifted_time_budget sharp μ hμ hgap g k

end LowEnergy.SourceGeometricBulkTimeBudget
