import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.PartitionGeometry
import H0mework.Versions.R9c73a630.Chemistry.LAlanineParametric.Integrand

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellPartition

open SourceGaussianModel ContinuousParameterMap Set MeasureTheory
open scoped BigOperators

noncomputable section

def fullSignedIntegral : ℝ := ∫ p in fullDomain, signedLaplacian 0 4 p
def quarterSignedIntegral (q : Quarter) : ℝ := ∫ p in quarterDomain q, signedLaplacian 0 4 p

theorem full_signed_integrable : IntegrableOn (signedLaplacian 0 4) fullDomain :=
  (signedLaplacian_contDiff 0 4).continuous.continuousOn.integrableOn_compact full_compact

theorem quarter_signed_integrable (q : Quarter) : IntegrableOn (signedLaplacian 0 4) (quarterDomain q) :=
  full_signed_integrable.mono_set (quarter_subset_full q)

/-- Only common boundaries are discarded; every signed quarter remains a separate summand. -/
theorem full_signed_integral_eq_quarters : fullSignedIntegral = ∑ q : Quarter, quarterSignedIntegral q := by
  unfold fullSignedIntegral quarterSignedIntegral
  rw [fullDomain_eq_iUnion_quarters]
  have integrable : IntegrableOn (signedLaplacian 0 4) (⋃ q : Quarter, quarterDomain q) := by
    rw [← fullDomain_eq_iUnion_quarters]
    exact full_signed_integrable
  simpa only [tsum_fintype] using
    integral_iUnion_ae (fun q => (quarter_measurable q).nullMeasurableSet) quarters_ae_disjoint integrable

end
end LAlanine40K2025.BasinRefinement.WholeCellPartition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
