import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedHalfSchur

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedHalfGreenSchur
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalHalfAxis
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedStaticResponse
open ActualDressedSylvester ActualDressedSignal ActualDressedPencil
open ActualEMAction
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceGreen frequencyQuantumCorrection frequencyResponsePencil
  frequencyHalfPolarization dressedStaticPolarization staticQuantumCorrection staticResponsePencil
  halfFeedback halfFeedbackDet halfFeedbackResolvent halfResponseNine

theorem half_static_quantum_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (static : p.val 0=0) (lambda : ℂ) (positive : 0<lambda.re) :
    frequencyQuantumCorrection event transfer p.val lambda=staticQuantumCorrection event transfer lambda := by
  have source : frequencyHalfPolarization event transfer p.val lambda=dressedStaticPolarization event transfer lambda := by
    funext i j
    unfold frequencyHalfPolarization
    exact dressed_static_polarization_actual event transfer p.val static lambda positive i j
  unfold frequencyQuantumCorrection staticQuantumCorrection frequencyInputNormalizer staticInputNormalizer
  rw [static,source]

/-- The actual static Pi, normalized exactly once, enters the full response and nine-row equation. -/
theorem static_half_full_solution_schur (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (static : p.val 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (regular : halfFeedbackDet event transfer p lambda≠0) (forcing a : Fin 289→ℂ) :
    staticResponsePencil event transfer p.val lambda*ᵥa=forcing ↔
      ∃initial : Fin 9→ℂ,a=halfResponseNine event transfer p lambda forcing initial ∧
        halfSchur event transfer p lambda*ᵥinitial=halfSchurSource event transfer p lambda forcing := by
  have same : frequencyResponsePencil event transfer p.val lambda=staticResponsePencil event transfer p.val lambda := by
    unfold frequencyResponsePencil staticResponsePencil
    rw [half_static_quantum_return event transfer p static lambda positive]
  rw [←same]
  exact half_full_solution_schur event transfer p lambda regular forcing a

/-- Exact physical momentum/clock restrictions of this same complete halfline response. -/
theorem physical_half_full_solution_schur (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (classicalRegular : frequencyRay e s n∈regularSource)
    (regular : halfFeedbackDet event ((e^2:ℝ) • n) ⟨frequencyRay e s n,classicalRegular⟩
      (dampedFourierClock (sourceFrequency e s) sigma)≠0) (forcing a : Fin 289→ℂ) :
    (emOriginalJacobi (frequencyRay e s n)-(sigma:ℂ) •
      frequencyHalfPolarization event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma))*ᵥa=forcing ↔
      ∃initial : Fin 9→ℂ,a=halfResponseNine event ((e^2:ℝ) • n) ⟨frequencyRay e s n,classicalRegular⟩
          (dampedFourierClock (sourceFrequency e s) sigma) forcing initial ∧
        halfSchur event ((e^2:ℝ) • n) ⟨frequencyRay e s n,classicalRegular⟩
          (dampedFourierClock (sourceFrequency e s) sigma)*ᵥinitial=
        halfSchurSource event ((e^2:ℝ) • n) ⟨frequencyRay e s n,classicalRegular⟩
          (dampedFourierClock (sourceFrequency e s) sigma) forcing := by
  rw [←damped_source_sheet_response event e s sigma n positive]
  exact half_full_solution_schur event ((e^2:ℝ) • n) ⟨frequencyRay e s n,classicalRegular⟩
    (dampedFourierClock (sourceFrequency e s) sigma) regular forcing a

def halfWindowFeedback (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  1-sourceGreen p*(frequencyInputNormalizer p.val lambda • dressedWindowPolarization event transfer p.val lambda T)

attribute [local irreducible] halfWindowFeedback

theorem half_window_feedback_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (off : sourceClockGrowth p.val<lambda.re) :
    Tendsto (halfWindowFeedback event transfer p lambda) atTop (𝓝 (halfFeedback event transfer p lambda)) := by
  have polarization:=frequency_polarization_window_limit event transfer p.val lambda off
  have correction:=(tendsto_const_nhds (x:=frequencyInputNormalizer p.val lambda)).smul polarization
  have multiplication : Continuous (fun A : Matrix (Fin 289) (Fin 289) ℂ=>sourceGreen p*A) :=
    continuous_const.matrix_mul continuous_id
  have product:=multiplication.tendsto _ |>.comp correction
  have source:=(tendsto_const_nhds (x:=(1:Matrix (Fin 289) (Fin 289) ℂ))).sub product
  unfold halfWindowFeedback halfFeedback frequencyQuantumCorrection
  simpa only [Function.comp_def] using source

/-- The paid actual window limit preserves the source determinant test eventually. -/
theorem half_window_feedback_eventually_regular (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (off : sourceClockGrowth p.val<lambda.re)
    (regular : halfFeedbackDet event transfer p lambda≠0) :
    ∀ᶠT : ℝ in atTop,(halfWindowFeedback event transfer p lambda T).det≠0 := by
  unfold halfFeedbackDet at regular
  have continuous : Continuous (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A.det) := continuous_id.matrix_det
  have determinant : Tendsto (fun T : ℝ=>(halfWindowFeedback event transfer p lambda T).det) atTop
      (𝓝 (halfFeedback event transfer p lambda).det) :=
    (continuous.tendsto _).comp (half_window_feedback_limit event transfer p lambda off)
  exact determinant.eventually_ne regular

/-- The canonical actual window inverses converge to the same source-generated halfline inverse. -/
theorem half_window_feedback_inverse_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : regularSource) (lambda : ℂ) (off : sourceClockGrowth p.val<lambda.re)
    (regular : halfFeedbackDet event transfer p lambda≠0) :
    Tendsto (fun T : ℝ=>(halfWindowFeedback event transfer p lambda T)⁻¹) atTop
      (𝓝 (halfFeedbackResolvent event transfer p lambda)) := by
  unfold halfFeedbackDet at regular
  unfold halfFeedbackResolvent
  have inverse : ContinuousAt (Ring.inverse : ℂ→ℂ) (halfFeedback event transfer p lambda).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ regular
  exact (continuousAt_matrix_inv (halfFeedback event transfer p lambda) inverse).tendsto.comp
    (half_window_feedback_limit event transfer p lambda off)

end LowEnergy.GaussComposite.ActualDressedHalfGreenSchur
