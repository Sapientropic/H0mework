import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

/-- Antisymmetrization uses the same actual normalized orbitals at both electron positions. -/
def fermionPair (i j : Basis) (z : Point × Point) : ℝ :=
  (normalizedOrbital i z.1*normalizedOrbital j z.2-
    normalizedOrbital j z.1*normalizedOrbital i z.2) / Real.sqrt 2

theorem fermion_pair_exchange (i j : Basis) (z : Point × Point) :
    fermionPair i j z.swap = -fermionPair i j z := by
  simp only [fermionPair,Prod.swap]
  ring

theorem fermion_pair_same (i : Basis) (z : Point × Point) : fermionPair i i z = 0 := by
  simp [fermionPair]

private theorem square_expansion (i j : Basis) (z : Point × Point) :
    (fermionPair i j z)^2 = (1/2 : ℝ)*
      ((normalizedOrbital i z.1*normalizedOrbital i z.1)*(normalizedOrbital j z.2*normalizedOrbital j z.2)+
       (normalizedOrbital j z.1*normalizedOrbital j z.1)*(normalizedOrbital i z.2*normalizedOrbital i z.2)-
       2*((normalizedOrbital i z.1*normalizedOrbital j z.1)*(normalizedOrbital i z.2*normalizedOrbital j z.2))) := by
  simp only [fermionPair,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem fermion_pair_square_integrable (i j : Basis) : Integrable (fun z : Point × Point => (fermionPair i j z)^2) := by
  simp_rw [square_expansion]
  exact ((((normalized_pair_integrable i i).mul_prod (normalized_pair_integrable j j)).add
    ((normalized_pair_integrable j j).mul_prod (normalized_pair_integrable i i))).sub
    (((normalized_pair_integrable i j).mul_prod (normalized_pair_integrable i j)).const_mul 2)).const_mul (1/2)

theorem fermion_pair_normalized (positive : actualGram.PosDef) (i j : Basis) (different : i ≠ j) :
    (∫ z : Point × Point, (fermionPair i j z)^2) = 1 := by
  have aa := (normalized_pair_integrable i i).mul_prod (normalized_pair_integrable j j)
  have bb := (normalized_pair_integrable j j).mul_prod (normalized_pair_integrable i i)
  have ab := (normalized_pair_integrable i j).mul_prod (normalized_pair_integrable i j)
  simp_rw [square_expansion]
  rw [Measure.volume_eq_prod]
  have subtract := integral_sub (aa.add bb) (ab.const_mul 2)
  have addition := integral_add aa bb
  simp only [Pi.add_apply] at subtract addition
  rw [integral_const_mul,subtract,addition,integral_const_mul]
  have tensor (a b c d : Basis) : (∫ z : Point × Point,
      (normalizedOrbital a z.1*normalizedOrbital b z.1)*
        (normalizedOrbital c z.2*normalizedOrbital d z.2) ∂volume.prod volume) =
      (if a=b then 1 else 0)*(if c=d then 1 else 0) := by
    rw [integral_prod_mul (fun x => normalizedOrbital a x*normalizedOrbital b x)
      (fun x => normalizedOrbital c x*normalizedOrbital d x)]
    rw [normalized_pair positive,normalized_pair positive]
  rw [tensor,tensor,tensor]
  norm_num [different]

def fermionPairCoulomb (i j : Basis) : ℝ := ∫ z : Point × Point,
  (fermionPair i j z)^2*kernel (z.2-z.1)

theorem fermion_pair_coulomb_integrable (i j : Basis) : Integrable (fun z : Point × Point =>
    (fermionPair i j z)^2*kernel (z.2-z.1)) := by
  have each := (((normalized_quartet_integrable i i j j).add
    (normalized_quartet_integrable j j i i)).sub ((normalized_quartet_integrable i j i j).const_mul 2)).const_mul (1/2)
  convert! each using 1
  funext z
  rw [square_expansion]
  simp only [Pi.sub_apply,Pi.add_apply]
  ring

theorem fermion_pair_coulomb_direct_exchange (i j : Basis) :
    fermionPairCoulomb i j = (1/2 : ℝ)*
      (normalizedRepulsion i i j j+normalizedRepulsion j j i i-2*normalizedRepulsion i j i j) := by
  have expression (z : Point × Point) : (fermionPair i j z)^2*kernel (z.2-z.1) =
      (1/2 : ℝ)*((normalizedOrbital i z.1*normalizedOrbital i z.1*(normalizedOrbital j z.2*normalizedOrbital j z.2)*kernel (z.2-z.1))+
      (normalizedOrbital j z.1*normalizedOrbital j z.1*(normalizedOrbital i z.2*normalizedOrbital i z.2)*kernel (z.2-z.1))-
      2*(normalizedOrbital i z.1*normalizedOrbital j z.1*(normalizedOrbital i z.2*normalizedOrbital j z.2)*kernel (z.2-z.1))) := by
    rw [square_expansion]
    ring
  simp only [fermionPairCoulomb,expression]
  have subtract := integral_sub ((normalized_quartet_integrable i i j j).add
    (normalized_quartet_integrable j j i i)) ((normalized_quartet_integrable i j i j).const_mul 2)
  have addition := integral_add (normalized_quartet_integrable i i j j) (normalized_quartet_integrable j j i i)
  simp only [Pi.add_apply] at subtract addition
  rw [integral_const_mul,subtract,addition,integral_const_mul]
  rfl

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
