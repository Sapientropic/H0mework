import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedProjectedClock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullNoetherMatrixRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedPhotonFiniteMoments
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn ActualDressedFullCoulomb ActualDressedNoether
open ActualDressedSylvester ActualSourceFullSylvesterMatrix
open ActualSourcePreparedNoetherPi ActualSourcePreparedPhotonPoleRead ActualSourcePreparedProjectedClock
open scoped Matrix BigOperators
attribute [local irreducible] dressedKinematicPoint sourceInverseWeights sourceDirectMoments
  sourceDrivenMoments sourcePreparedPiEntry sourcePreparedModeResponse sourcePreparedPhotonPoleResponse
  sourcePhotonLeftReaderCLM

def sourcePhotonDirectMoments (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon sheet : ℝ) (n : PhysicalMomentum) :
    SourceIndex (dressedKinematicPoint event transfer) → ℂ := fun a =>
  let M : Matrix (Fin 289) (Fin 289) ℂ :=
    fun i j => sourceDirectMoments event transfer i j a
  sourcePhotonLeftReaderCLM branch epsilon sheet n
    (M *ᵥ sourceNativeFrequencyPolarization branch epsilon sheet n)

def sourcePhotonDrivenMoments (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon sheet : ℝ) (n : PhysicalMomentum) :
    Matrix (SourceIndex (dressedKinematicPoint event transfer))
      (SourceIndex (dressedKinematicPoint event transfer)) ℂ := fun a b =>
  let M : Matrix (Fin 289) (Fin 289) ℂ :=
    fun i j => sourceDrivenMoments event transfer i j a b
  sourcePhotonLeftReaderCLM branch epsilon sheet n
    (M *ᵥ sourceNativeFrequencyPolarization branch epsilon sheet n)

/-- All weights come from the original whole-evolution inverse; contact and both
driven legs stay in the original Noether moments before the scalar projection. -/
def sourcePhotonFiniteMomentResponse (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon sheet : ℝ) (n : PhysicalMomentum) (lambda : ℂ) : ℂ :=
  let w := sourceInverseWeights (dressedKinematicPoint event transfer) lambda
  dotProduct w (sourcePhotonDirectMoments event transfer branch epsilon sheet n) +
    dotProduct w (sourcePhotonDrivenMoments event transfer branch epsilon sheet n *ᵥ w)

private theorem full_moment_matrix (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) :
    let q := dressedKinematicPoint event transfer
    let D : SourceIndex q → Matrix (Fin 289) (Fin 289) ℂ :=
      fun a i j => sourceDirectMoments event transfer i j a
    let R : SourceIndex q → SourceIndex q → Matrix (Fin 289) (Fin 289) ℂ :=
      fun a b i j => sourceDrivenMoments event transfer i j a b
    let w := sourceInverseWeights q lambda
    (fun i j => sourceFullNoetherMatrixEntry event transfer lambda i j : Matrix (Fin 289) (Fin 289) ℂ) =
      (∑a, w a • D a) + ∑a, ∑b, (w a * w b) • R a b := by
  dsimp only
  ext i j
  simp only [sourceFullNoetherMatrixEntry, dotProduct, Matrix.mulVec,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply congrArg (fun c : ℂ => _ + c)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The generated preparation response consumes the finite original Noether matrix
and its unchanged whole-evolution weights directly. -/
theorem source_prepared_photon_finite_moments (event : DressedEvent) (transfer : PhysicalMomentum)
    (branch : Fin 2) (epsilon sheet : ℝ) (n : PhysicalMomentum) (lambda : ℂ)
    (positive : 0 < lambda.re) :
    sourcePreparedPhotonPoleResponse event transfer branch epsilon sheet n lambda =
      sourcePhotonFiniteMomentResponse event transfer branch epsilon sheet n lambda := by
  unfold sourcePreparedPhotonPoleResponse
  rw [source_prepared_mode_response_actual event transfer lambda positive]
  have matrix : (fun i j => sourcePreparedPiEntry event transfer lambda i j : Matrix (Fin 289) (Fin 289) ℂ) =
      fun i j => sourceFullNoetherMatrixEntry event transfer lambda i j := by
    ext i j
    exact (source_prepared_pi_actual event transfer lambda positive i j).trans
      (source_full_noether_polarization_matrix event transfer lambda positive i j)
  rw [matrix, full_moment_matrix]
  simp only [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    map_add, map_sum, map_smul, smul_eq_mul]
  unfold sourcePhotonFiniteMomentResponse sourcePhotonDirectMoments sourcePhotonDrivenMoments
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply congrArg (fun c : ℂ => _ + c)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem source_photon_finite_moment_clock_fraction (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (positive : 0 < sigma) :
    (sigma : ℂ) * sourcePhotonFiniteMomentResponse event ((epsilon^2 : ℝ) • n)
        branch epsilon sheet n (sigma : ℂ) =
      (sourceProjectedClockNumerator event epsilon n branch sheet).eval (sigma : ℂ) /
        (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ) := by
  rw [← source_prepared_photon_finite_moments event ((epsilon^2 : ℝ) • n)
    branch epsilon sheet n (sigma : ℂ) (by simpa using positive)]
  exact source_prepared_projected_clock_fraction event epsilon sigma n branch sheet positive

end LowEnergy.GaussComposite.ActualSourcePreparedPhotonFiniteMoments
