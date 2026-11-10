import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMStaticCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroDamping
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualCompositeFieldCurrent Filter Set
open scoped Matrix Topology
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

/-- IR scale and external momenta are fixed; the original static clock remains the polynomial variable. -/
def dampingSlice (eps : ℝ) : Parameters →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 3 => if i=0 then Polynomial.C (eps : ℂ) else if i=1 then Polynomial.X else 0)

theorem damping_slice_eval (eps sigma : ℝ) (P : Parameters) :
    (dampingSlice eps P).eval (sigma : ℂ)=MvPolynomial.eval (irValues eps sigma 0) P := by
  have hom : (Polynomial.evalRingHom (sigma : ℂ)).comp (dampingSlice eps)=
      MvPolynomial.eval (irValues eps sigma 0) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [dampingSlice]
    · intro i
      simp [dampingSlice, irValues]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ => f P) hom

def dampingDeterminant (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  dampingSlice eps (commonDeterminant event n)

def dampingEMNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] := (commonEMTensorNumerator event n).map (dampingSlice eps)

def dampingEMFraction (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (RatFunc ℂ) :=
  fun mu nu => readFraction (dampingEMNumerator event eps n mu nu) (dampingDeterminant event eps n)

def dampingProbeNumerator (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ[X] :=
  dampingSlice eps (commonCurrentNumerator event n pd ps dL dR sL sR)

def dampingProbeFraction (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : RatFunc ℂ :=
  readFraction (dampingProbeNumerator event eps n pd ps dL dR sL sR) (dampingDeterminant event eps n)

/-- An identically singular original pencil returns no packet; otherwise every reduced principal coefficient is retained. -/
def sourceDampingPrincipalData (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    Option (Matrix (Fin 4) (Fin 4) (ℕ × List ℂ) × (ℕ × List ℂ)) := by
  classical
  exact if dampingDeterminant event eps n=0 then none else some
    ((fun mu nu => let R := dampingEMFraction event eps n mu nu
      (poleOrder R 0,List.ofFn (fun k : Fin (poleOrder R 0) => principalCoefficient R 0 k.val))),
      let R := dampingProbeFraction event eps n pd ps dL dR sL sR
      (poleOrder R 0,List.ofFn (fun k : Fin (poleOrder R 0) => principalCoefficient R 0 k.val)))

theorem source_damping_original_chart (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : dampingDeterminant event eps n≠0) :
    ∀ᶠ sigma : ℝ in nhdsWithin 0 (Ioi 0), 0<sigma ∧ correctedDet event eps 0 sigma n≠0 := by
  have inclusion : Ioi (0 : ℝ) ⊆ ({0}ᶜ) := by
    intro sigma positive
    simpa only [mem_compl_iff, mem_singleton_iff] using (ne_of_gt positive)
  have chart := (source_static_punctured_chart _ nonzero).filter_mono (nhdsWithin_mono 0 inclusion)
  filter_upwards [chart, self_mem_nhdsWithin] with sigma regular positive
  refine ⟨positive, actual_common_chart_original event eps sigma 0 n positive ?_⟩
  rw [← damping_slice_eval]
  exact regular

theorem actual_damping_em_fraction (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (chart : (dampingDeterminant event eps n).eval (sigma : ℂ)≠0)
    (mu nu : Fin 4) :
    correctedEMTensor event eps 0 sigma n mu nu=
      (dampingEMFraction event eps n mu nu).num.eval (sigma : ℂ)/
        (dampingEMFraction event eps n mu nu).denom.eval (sigma : ℂ) := by
  have commonRegular : MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n)≠0 := by
    rw [← damping_slice_eval]
    exact chart
  have regular := actual_common_chart_original event eps sigma 0 n positive commonRegular
  have read := congrFun (congrFun (actual_corrected_em_tensor_clear event eps sigma 0 n positive regular) mu) nu
  have raw : correctedEMTensor event eps 0 sigma n mu nu=
      MvPolynomial.eval (irValues eps sigma 0) (commonEMTensorNumerator event n mu nu)/
        MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n) := by
    apply (eq_div_iff commonRegular).mpr
    exact (mul_comm _ _).trans read
  refine raw.trans ?_
  rw [← damping_slice_eval, ← damping_slice_eval]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

theorem actual_damping_probe_fraction (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (positive : 0<sigma) (chart : (dampingDeterminant event eps n).eval (sigma : ℂ)≠0) :
    correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR=
      (dampingProbeFraction event eps n pd ps dL dR sL sR).num.eval (sigma : ℂ)/
        (dampingProbeFraction event eps n pd ps dL dR sL sR).denom.eval (sigma : ℂ) := by
  have commonRegular : MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n)≠0 := by
    rw [← damping_slice_eval]
    exact chart
  have regular := actual_common_chart_original event eps sigma 0 n positive commonRegular
  refine (actual_common_current_read_fraction event eps sigma 0 n pd ps dL dR sL sR positive regular).trans ?_
  rw [← damping_slice_eval, ← damping_slice_eval]
  exact (reduced_read_at_regular _ _ (sigma : ℂ) chart).symm

end LowEnergy.GaussComposite.ActualDressedZeroDamping
