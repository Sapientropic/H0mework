import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Coulomb

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open MeasureTheory CPS1ElectronicSource
open scoped BigOperators
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ContinuousGradient

theorem multicentre_real_product_integrable (left right : CPS1ElectronicSource.Point) (i j : Nat) (jetI jetJ : MultiIndex) :
    Integrable (fun x : CPS1ElectronicSource.Point => primitiveReal left i jetI x * primitiveReal right j jetJ x)
      (volume : Measure CPS1ElectronicSource.Point) :=
  (primitive_real_integrable right j jetJ).bdd_mul
    (primitive_real_continuous left i jetI).aestronglyMeasurable
    (Filter.Eventually.of_forall (primitive_real_bound left i jetI))

theorem multicentre_real_product_bound (left right : CPS1ElectronicSource.Point) (i j : Nat) (jetI jetJ : MultiIndex) (x : CPS1ElectronicSource.Point) :
    ‖primitiveReal left i jetI x * primitiveReal right j jetJ x‖ ≤
      primitiveEnvelope i jetI * primitiveEnvelope j jetJ := by
  rw [norm_mul]
  exact mul_le_mul (primitive_real_bound left i jetI x) (primitive_real_bound right j jetJ x)
    (norm_nonneg _) ((norm_nonneg _).trans (primitive_real_bound left i jetI x))

theorem multicentre_kinetic_integrable (left right : CPS1ElectronicSource.Point) (i j : Nat) (jetI jetJ : MultiIndex) :
    Integrable (fun x : CPS1ElectronicSource.Point => star (orbitalValue left i jetI x) * orbitalValue right j jetJ x)
      (volume : Measure CPS1ElectronicSource.Point) := by
  have actual := (multicentre_real_product_integrable left right i j jetI jetJ).ofReal (𝕜 := ℂ)
  convert! actual using 1
  funext x
  simp [orbitalValue,primitiveReal]

theorem multicentre_nuclear_integrable (left right : CPS1ElectronicSource.Point) (i j : Nat) (nuclear : CPS1ElectronicSource.Point)
    (jetI jetJ : MultiIndex) :
    Integrable (fun x : CPS1ElectronicSource.Point => (SourceCoulomb.kernel (x-nuclear) : ℂ) *
      star (orbitalValue left i jetI x) * orbitalValue right j jetJ x) (volume : Measure CPS1ElectronicSource.Point) := by
  have actual := (SourceCoulomb.integrable_mul_shifted_kernel _
    (multicentre_real_product_integrable left right i j jetI jetJ)
    (primitiveEnvelope i jetI * primitiveEnvelope j jetJ)
    (multicentre_real_product_bound left right i j jetI jetJ) nuclear).ofReal (𝕜 := ℂ)
  convert! actual using 1
  funext x
  simp [orbitalValue,primitiveReal,mul_comm,mul_assoc]

theorem multicentre_pair_integrable (first second third fourth : CPS1ElectronicSource.Point) (i j k l : Nat)
    (jetI jetJ jetK jetL : MultiIndex) :
    Integrable (fun z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point => (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
      star (orbitalValue first i jetI z.1) * orbitalValue second j jetJ z.1 *
      star (orbitalValue third k jetK z.2) * orbitalValue fourth l jetL z.2)
      ((volume : Measure CPS1ElectronicSource.Point).prod volume) := by
  have actual := (SourceCoulomb.pair_integrable _ _
    (multicentre_real_product_integrable first second i j jetI jetJ)
    (multicentre_real_product_integrable third fourth k l jetK jetL)
    (primitiveEnvelope k jetK * primitiveEnvelope l jetL)
    (multicentre_real_product_bound third fourth k l jetK jetL)).ofReal (𝕜 := ℂ)
  convert! actual using 1
  funext z
  rw [coulomb_kernel_sub_comm z.1 z.2]
  simp [orbitalValue,primitiveReal,mul_comm,mul_assoc]

def primitiveKineticIntegral (left right : CPS1ElectronicSource.Point) (i j : Nat) (jetI jetJ : MultiIndex) : ℂ :=
  ∫ x : CPS1ElectronicSource.Point, star (orbitalValue left i jetI x) * orbitalValue right j jetJ x

def primitiveNuclearIntegral (left right : CPS1ElectronicSource.Point) (i j : Nat) (nuclear : CPS1ElectronicSource.Point)
    (jetI jetJ : MultiIndex) : ℂ :=
  ∫ x : CPS1ElectronicSource.Point, (SourceCoulomb.kernel (x-nuclear) : ℂ) *
    star (orbitalValue left i jetI x) * orbitalValue right j jetJ x

def primitivePairIntegral (first second third fourth : CPS1ElectronicSource.Point) (i j k l : Nat)
    (jetI jetJ jetK jetL : MultiIndex) : ℂ :=
  ∫ z : CPS1ElectronicSource.Point × CPS1ElectronicSource.Point, (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
    star (orbitalValue first i jetI z.1) * orbitalValue second j jetJ z.1 *
    star (orbitalValue third k jetK z.2) * orbitalValue fourth l jetL z.2
    ∂(volume : Measure CPS1ElectronicSource.Point).prod volume

end
end CPS1MolecularFrame
