import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Calculus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.Ownership
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.SpatialContinuation.MovingBasis

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement SourceGaussianModel SourceFiniteData
open SpatialContinuation
noncomputable section
abbrev Phase := SpatialContinuation.Phase
variable (current : Material)

def centre (i : Basis) (p : Primitive i) (phase : Phase) (t : ℝ) : Point :=
  fun k => position current phase t (owner i p,k)

def primitiveJet (i : Basis) (p : Primitive i) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  centredValue (primitive i p) jet (centre current i p phase t) x

def primitiveRate (i : Basis) (p : Primitive i) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  -(∑ k : Fin 3, velocity current phase t (owner i p,k)*primitiveJet current i p (raise jet k) phase t x)

def orbitalJet (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  ∑ p : Primitive i, primitiveJet current i p jet phase t x

def orbitalRate (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) : ℝ :=
  ∑ p : Primitive i, primitiveRate current i p jet phase t x

theorem centre_is_actual (i : Basis) (p : Primitive i) (phase : Phase) (t : ℝ) (k : Fin 3) :
    centre current i p phase t k=position current phase t (owner i p,k) := rfl

theorem centre_equation (i : Basis) (p : Primitive i) (phase : Phase) (t : ℝ) (k : Fin 3) :
    HasDerivAt (fun time => centre current i p phase time k) (velocity current phase t (owner i p,k)) t :=
  position_equation current phase t (owner i p,k)

theorem primitive_equation (i : Basis) (p : Primitive i) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => primitiveJet current i p jet phase time x) (primitiveRate current i p jet phase t x) t :=
  centred_value_derivative (primitive i p) jet (centre current i p phase) _ t x
    (centre_equation current i p phase t)

theorem orbital_equation (i : Basis) (jet : MultiIndex) (phase : Phase) (t : ℝ) (x : Point) :
    HasDerivAt (fun time => orbitalJet current i jet phase time x) (orbitalRate current i jet phase t x) t :=
  HasDerivAt.fun_sum (fun p _ => primitive_equation current i p jet phase t x)

theorem static_primitive (valid : Admissible current) (i : Basis) (p : Primitive i) (jet : MultiIndex) (x : Point) :
    centredValue (primitive i p) jet (nucleus current (owner i p)) x=
      value (SpatialActuation.termAt current.lab (primitive i p)) jet x := by
  rw [primitive_translation]
  unfold centredValue
  congr 1
  funext k
  simp only [nucleus,lab_position current valid,primitive_centre,Rat.cast_add,Pi.sub_apply,translationPoint]
  ring

theorem primitive_source (valid : Admissible current) (i : Basis) (p : Primitive i) (jet : MultiIndex) (x : Point) :
    primitiveJet current i p jet .enter 0 x=value (SpatialActuation.termAt current.lab (primitive i p)) jet x := by
  have point : centre current i p .enter 0=nucleus current (owner i p) := by
    funext k
    exact source_position current valid (owner i p,k)
  rw [primitiveJet,point,static_primitive current valid]

theorem primitive_target (valid : Admissible current) (i : Basis) (p : Primitive i) (jet : MultiIndex) (x : Point) :
    primitiveJet current i p jet .leave duration x=value (SpatialActuation.termAt (nextMaterial current).lab (primitive i p)) jet x := by
  have point : centre current i p .leave duration=nucleus (nextMaterial current) (owner i p) := by
    funext k
    exact target_position current valid (owner i p,k)
  rw [primitiveJet,point,static_primitive (nextMaterial current) (next_admissible current valid)]

theorem orbital_source (valid : Admissible current) (i : Basis) (jet : MultiIndex) (x : Point) :
    orbitalJet current i jet .enter 0 x=aoJet current i jet x := by
  simp only [orbitalJet,primitive_source current valid,aoJet,SpatialActuation.termsAt,orbital,List.map_map]
  exact Fin.sum_univ_fun_getElem (sourceTerms i) (fun term => value (SpatialActuation.termAt current.lab term) jet x)

theorem orbital_target (valid : Admissible current) (i : Basis) (jet : MultiIndex) (x : Point) :
    orbitalJet current i jet .leave duration x=aoJet (nextMaterial current) i jet x := by
  simp only [orbitalJet,primitive_target current valid,aoJet,SpatialActuation.termsAt,orbital,List.map_map]
  exact Fin.sum_univ_fun_getElem (sourceTerms i) (fun term => value (SpatialActuation.termAt (nextMaterial current).lab term) jet x)

theorem orbital_junctions (i : Basis) (jet : MultiIndex) (x : Point) :
    orbitalJet current i jet .enter duration x=orbitalJet current i jet .drive 0 x ∧
    orbitalJet current i jet .drive duration x=orbitalJet current i jet .leave 0 x := by
  unfold orbitalJet primitiveJet centre
  rw [(position_junctions current).1,(position_junctions current).2]
  exact ⟨rfl,rfl⟩

theorem primitive_continuous (i : Basis) (p : Primitive i) (jet : MultiIndex) (phase : Phase) (x : Point) :
    Continuous (fun t => primitiveJet current i p jet phase t x) :=
  continuous_iff_continuousAt.mpr fun t => (primitive_equation current i p jet phase t x).continuousAt

theorem orbital_continuous (i : Basis) (jet : MultiIndex) (phase : Phase) (x : Point) :
    Continuous (fun t => orbitalJet current i jet phase t x) :=
  continuous_iff_continuousAt.mpr fun t => (orbital_equation current i jet phase t x).continuousAt

theorem orbital_rate_continuous (i : Basis) (jet : MultiIndex) (phase : Phase) (x : Point) :
    Continuous (fun t => orbitalRate current i jet phase t x) := by
  unfold orbitalRate primitiveRate
  apply continuous_finsetSum
  intro p _
  apply Continuous.neg
  apply continuous_finsetSum
  intro k _
  exact (velocity_differentiable current phase (owner i p,k)).continuous.mul
    (primitive_continuous current i p (raise jet k) phase x)

theorem orbital_integral (i : Basis) (jet : MultiIndex) (phase : Phase) (x : Point) :
    orbitalJet current i jet phase duration x-orbitalJet current i jet phase 0 x=
      ∫ t in (0 : ℝ)..duration, orbitalRate current i jet phase t x :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => orbital_equation current i jet phase t x)
    ((orbital_rate_continuous current i jet phase x).intervalIntegrable _ _)).symm

theorem orbital_update (valid : Admissible current) (i : Basis) (jet : MultiIndex) (x : Point) :
    aoJet (nextMaterial current) i jet x-aoJet current i jet x=
      (∫ t in (0 : ℝ)..duration, orbitalRate current i jet .enter t x)+
      (∫ t in (0 : ℝ)..duration, orbitalRate current i jet .drive t x)+
      (∫ t in (0 : ℝ)..duration, orbitalRate current i jet .leave t x) := by
  rw [← orbital_integral,← orbital_integral,← orbital_integral,
    orbital_source current valid,orbital_target current valid,
    (orbital_junctions current i jet x).1,(orbital_junctions current i jet x).2]
  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
