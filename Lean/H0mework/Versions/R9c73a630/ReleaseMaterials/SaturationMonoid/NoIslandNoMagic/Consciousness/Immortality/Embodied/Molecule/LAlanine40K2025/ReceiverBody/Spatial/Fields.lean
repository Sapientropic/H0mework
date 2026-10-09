import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Bridge
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PrecisePair

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb ContinuousGradient
open BasinRefinement.WholeBandBasin.Family.All
open UnifiedOrbitals
open scoped BigOperators
noncomputable section

def centreAt (body : ReceiverBody.Runtime.ActuationResult) (a : Fin 13) : Point :=
  fun k => (body.frame.position a k : ℝ)

def aoAttractionAt (body : ReceiverBody.Runtime.ActuationResult) (i j : Basis) : ℝ :=
  ∑ a : Fin 13, -Nuclear.nuclearCharge a *
    ∫ x : Point, ao i x * ao j x * kernel (x-centreAt body a)

def nuclearRepulsionAt (body : ReceiverBody.Runtime.ActuationResult) (a b : Fin 13) : ℝ :=
  Nuclear.nuclearCharge a*Nuclear.nuclearCharge b*kernel (centreAt body a-centreAt body b)

def nuclearAttractionAt (body : ReceiverBody.Runtime.ActuationResult) (a : Fin 13) : ℝ :=
  ∫ x : Point, -Nuclear.nuclearCharge a*(sourceDensity x*kernel (x-centreAt body a))

theorem centres_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) (a : Fin 13) : centreAt body a=Nuclear.PreciseTarget.centre a := by
  funext k
  change (body.frame.position a k : ℝ)=(UnifiedOrbitals.Attraction.Precise.nucleus a k : ℝ)
  rw [source.position]

theorem ao_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) (i j : Basis) :
    aoAttractionAt body i j=UnifiedOrbitals.Attraction.Precise.aoIntegral i j := by
  unfold aoAttractionAt UnifiedOrbitals.Attraction.Precise.aoIntegral
  simp only [centres_from_static source]
  rfl

theorem repulsion_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) (a b : Fin 13) :
    nuclearRepulsionAt body a b=Nuclear.PreciseTarget.nuclearRepulsion a b := by
  unfold nuclearRepulsionAt Nuclear.PreciseTarget.nuclearRepulsion
  rw [centres_from_static source,centres_from_static source]

theorem attraction_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) (a : Fin 13) :
    nuclearAttractionAt body a=Nuclear.PreciseTarget.nuclearAttraction a := by
  unfold nuclearAttractionAt Nuclear.PreciseTarget.nuclearAttraction
  rw [centres_from_static source]

theorem total_attraction_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) :
    (∑ a : Fin 13, nuclearAttractionAt body a)=
      ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ)*aoAttractionAt body i j := by
  simp only [attraction_from_static source,ao_from_static source]
  exact Nuclear.PreciseTarget.nuclear_total_original_ao

structure FieldClosure (body : ReceiverBody.Runtime.ActuationResult) : Prop where
  centres : ∀ a, centreAt body a=Nuclear.PreciseTarget.centre a
  ao : ∀ i j, aoAttractionAt body i j=UnifiedOrbitals.Attraction.Precise.aoIntegral i j
  pairs : ∀ a b, nuclearRepulsionAt body a b=Nuclear.PreciseTarget.nuclearRepulsion a b
  attraction : ∀ a, nuclearAttractionAt body a=Nuclear.PreciseTarget.nuclearAttraction a
  totalAttraction : (∑ a : Fin 13, nuclearAttractionAt body a)=
    ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℝ)*aoAttractionAt body i j

theorem fields_from_static {body : ReceiverBody.Runtime.ActuationResult}
    (source : StaticClosure body) : FieldClosure body :=
  ⟨centres_from_static source,ao_from_static source,repulsion_from_static source,attraction_from_static source,total_attraction_from_static source⟩

theorem actualFields : FieldClosure current := fields_from_static sourceStaticClosure

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial
