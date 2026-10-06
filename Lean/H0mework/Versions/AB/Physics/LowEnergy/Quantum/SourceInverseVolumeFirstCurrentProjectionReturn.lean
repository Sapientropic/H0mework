import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentProjectionSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentJointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseFirstCurrentProjectionReturn
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseFirstCurrentProjectionSource SourceInverseFirstCurrentGaugeJets SourceInverseCompressionCurrent
open SourceGaugeCoframeJets SourceGaugeCoframeWard SourceScalarDoubleCurrent SourceJointScaleBudget
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceMixedNativeReturn FullYSourceResolventGraphSplice Filter MeasureTheory
open SourceInverseFirstCurrentForceTail SourceInverseFirstCurrentJointTail SourceScalarForceBudget
open SourceFourPoleEnergyClosed SourceResolventBandLimit
abbrev Op := H →L[ℂ] H
attribute [local irreducible] firstSourceCorrections firstProjectionCross gaugeFilter
  sandwichJet inverseCross inputFlux sourceRead matterHamiltonianCurrent matterInsertion defectAction
  remainingResponse remainingProfile remainingForces doubleResponse oscillatorMass

/-- Only escaped input is removed; the full derivative family of the true Hamiltonian defect stays joined. -/
def defectCorrections (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  gaugeFilter (fun n => sandwichJet F g z
    (bracket (defectAction F) (matterInsertion sharp m ell)) 0 n 0 0)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*finiteResolvent F z

/-- One fixed-source cofinal set pays the entire first-current projection part before all cutoffs/readers/frequencies. -/
theorem actual_correction_pair (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp m ell,∀ z : ℂ,∀ _hz : z.im≠0,∀ k : H,
      inner ℂ k (firstSourceCorrections sharp m ell F g z (g : H))=
        inner ℂ k (defectCorrections sharp m ell F g z (g : H)) := by
  filter_upwards [actual_first_projection_source g] with F h sharp m ell z hz k
  have h0 := congrArg (fun x : H => inner ℂ k x) (h sharp m ell z hz ⟨0,by decide⟩)
  have h1 := congrArg (fun x : H => inner ℂ k x) (h sharp m ell z hz ⟨1,by decide⟩)
  have h2 := congrArg (fun x : H => inner ℂ k x) (h sharp m ell z hz ⟨2,by decide⟩)
  simp only [firstSourceCorrections,defectCorrections,gaugeFilter,sub_apply,add_apply,smul_apply,
    inner_sub_right,inner_add_right,inner_smul_right,h0,h1,h2]

/-- The same whole force, Hardy and double-CF terms survive the input-escape elimination. -/
def defectRemainingResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • defectCorrections sharp m ell F g z+
    finiteResolvent F z*remainingForces sharp m ell F g*finiteResolvent F z-
    finiteResolvent F z*doubleResponse sharp m ell F g*finiteResolvent F z

def defectRemainingProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H) (defectRemainingResponse sharp m ell F g z (g : H))

/-- The actual remaining profile is unchanged after the generated cofinal elimination, with all true defects retained. -/
theorem actual_remaining_profile (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp m ell,∀ z : ℂ,∀ _hz : z.im≠0,∀ k : diagonal.domain,
      remainingProfile sharp m ell F g k z=defectRemainingProfile sharp m ell F g k z := by
  filter_upwards [actual_correction_pair g] with F h sharp m ell z hz k
  have hp := h sharp m ell z hz (k : H)
  simp only [remainingProfile,defectRemainingProfile,remainingResponse,defectRemainingResponse,
    sub_apply,add_apply,smul_apply,inner_sub_right,inner_add_right,inner_smul_right,hp]

/-- The original cost now consumes the true-defect remainder directly, with its original tail quantifiers. -/
theorem actual_joint_defect_tail_iff (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    (∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
    (∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖defectRemainingProfile sharp m ell F g k (line μ w)‖^2)) ≤ ENNReal.ofReal ε) := by
  rw [actual_joint_remaining_tail_iff sharp μ hμ g k]
  constructor <;> intro h ε hε <;> obtain ⟨N,hN⟩ := h ε hε
  · refine ⟨N,fun m hm ell hell => ?_⟩
    filter_upwards [hN m hm ell hell,actual_remaining_profile g] with F hF he
    simpa only [he sharp m ell (line μ _) (by simpa only [line_im] using hμ.ne') k] using hF
  · refine ⟨N,fun m hm ell hell => ?_⟩
    filter_upwards [hN m hm ell hell,actual_remaining_profile g] with F hF he
    simpa only [he sharp m ell (line μ _) (by simpa only [line_im] using hμ.ne') k] using hF
end LowEnergy.SourceInverseFirstCurrentProjectionReturn
