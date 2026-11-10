import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMVisiblePairedEnergyGraph
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency
open LowEnergy.ActualDressedVisiblePole
open scoped BigOperators

abbrev EMChannel := Fin 4 × Fin 4

/-- The product keeps each original observer's multiplicity; it is not the whole-column pole order. -/
def emCommonSpectralPolynomial (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  ∏ c : EMChannel, (zeroClockFrequencyEMFraction event eps n c.1 c.2).denom

def emCommonSpectralRoots (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Multiset ℂ :=
  (emCommonSpectralPolynomial event eps n).roots

theorem source_em_common_spectral_monic (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    (emCommonSpectralPolynomial event eps n).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => RatFunc.monic_denom _)

theorem source_em_common_spectral_nonzero (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    emCommonSpectralPolynomial event eps n ≠ 0 :=
  (source_em_common_spectral_monic event eps n).ne_zero

theorem source_em_complete_spectral_roots (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    emCommonSpectralRoots event eps n = (Finset.univ : Finset EMChannel).val.bind
      (fun c => visibleRoots (zeroClockFrequencyEMFraction event eps n c.1 c.2)) :=
  roots_prod _ _ (source_em_common_spectral_nonzero event eps n)

theorem source_em_complete_spectral_coverage (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) :
    a ∈ emCommonSpectralRoots event eps n ↔
      ∃ mu nu : Fin 4, a ∈ visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu) := by
  rw [source_em_complete_spectral_roots]
  simp only [Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and]
  exact ⟨fun ⟨c,h⟩ => ⟨c.1,c.2,h⟩, fun ⟨mu,nu,h⟩ => ⟨(mu,nu),h⟩⟩

theorem source_em_complete_spectral_multiplicity (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) :
    (emCommonSpectralRoots event eps n).count a =
      ∑ c : EMChannel, poleOrder (zeroClockFrequencyEMFraction event eps n c.1 c.2) a := by
  classical
  rw [source_em_complete_spectral_roots, Multiset.count_bind]
  change ((Finset.univ : Finset EMChannel).val.map
      (fun c => (visibleRoots (zeroClockFrequencyEMFraction event eps n c.1 c.2)).count a)).sum = _
  simp only [visibleRoots, count_roots]
  rfl

/-- Complex splitting closes the entire spectral polynomial, including empty and repeated spectra. -/
theorem source_em_complete_spectral_factorization (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    emCommonSpectralPolynomial event eps n =
      ((emCommonSpectralRoots event eps n).map (fun a => X-C a)).prod :=
  (IsAlgClosed.splits _).eq_prod_roots_of_monic (source_em_common_spectral_monic event eps n)

theorem source_em_complete_spectral_degree (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    (emCommonSpectralRoots event eps n).card = (emCommonSpectralPolynomial event eps n).natDegree :=
  (IsAlgClosed.splits _).natDegree_eq_card_roots.symm

abbrev EMSourcePole (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :=
  {a : ℂ // a ∈ emCommonSpectralRoots event eps n}

abbrev EMSourceVisibleChannel (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) :=
  {c : EMChannel // a.val ∈ visibleRoots (zeroClockFrequencyEMFraction event eps n c.1 c.2)}

theorem source_em_spectral_fibre_nonempty (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) : Nonempty (EMSourceVisibleChannel event eps n a) := by
  obtain ⟨mu,nu,root⟩ := (source_em_complete_spectral_coverage event eps n a.val).mp a.property
  exact ⟨⟨(mu,nu),root⟩⟩

end LowEnergy.GaussComposite.ActualDressedEMSourceSpectrum
