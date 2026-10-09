import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.ERIIntegral

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
open BasinRefinement SourceGaussianModel NuclearBasis
open MeasureTheory
noncomputable section

def primitiveERIRate (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point) : ℝ :=
  -(∑ h : Quartet, ∑ k : Fin 3, speeds h k * primitiveERI terms (raiseSlot jets h k) centres)

theorem eri_rate_integrable (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point) :
    Integrable (eriRate terms jets centres speeds) :=
  (integrable_finsetSum _ (fun h _ => integrable_finsetSum _ (fun k _ =>
    (eri_integrand_integrable terms positive (raiseSlot jets h k) centres).const_mul (speeds h k)))).neg

theorem integrated_eri_rate (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
    (jets : Quartet → MultiIndex) (centres speeds : Quartet → Point) :
    (∫ z : Point × Point, eriRate terms jets centres speeds z) = primitiveERIRate terms jets centres speeds := by
  unfold eriRate
  rw [integral_neg,integral_finsetSum _ (fun h _ => integrable_finsetSum _ (fun k _ =>
    (eri_integrand_integrable terms positive (raiseSlot jets h k) centres).const_mul (speeds h k)))]
  unfold primitiveERIRate
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_finsetSum _ (fun k _ =>
    (eri_integrand_integrable terms positive (raiseSlot jets h k) centres).const_mul (speeds h k))]
  simp only [integral_const_mul,primitiveERI]

variable (terms : Quartet → Term) (positive : ∀ h, 0 < (terms h).exponent)
  (jets : Quartet → MultiIndex) (centres speeds : ℝ → Quartet → Point) (regular : Continuous speeds)
  (motion : ∀ t h k, HasDerivAt (fun s => centres s h k) (speeds t h k) t)

include positive regular motion

theorem primitive_eri_equation (t : ℝ) :
    HasDerivAt (fun s => primitiveERI terms jets (centres s))
      (primitiveERIRate terms jets (centres t) (speeds t)) t := by
  have generated := (primitive_eri_derivative terms positive jets centres speeds regular motion t).2
  rw [integrated_eri_rate terms positive] at generated
  exact generated

theorem primitive_eri_rate_continuous :
    Continuous (fun t => primitiveERIRate terms jets (centres t) (speeds t)) := by
  have family (h : Quartet) (k : Fin 3) : Continuous (fun t => primitiveERI terms (raiseSlot jets h k) (centres t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (primitive_eri_equation terms positive (raiseSlot jets h k) centres speeds regular motion t).continuousAt
  exact (continuous_finsetSum _ (fun h _ => continuous_finsetSum _ (fun k _ =>
    ((continuous_apply k).comp ((continuous_apply h).comp regular)).mul (family h k)))).neg

theorem primitive_eri_integral (a b : ℝ) :
    primitiveERI terms jets (centres b) - primitiveERI terms jets (centres a) =
      ∫ t in a..b, primitiveERIRate terms jets (centres t) (speeds t) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_eri_equation terms positive jets centres speeds regular motion t)
    ((primitive_eri_rate_continuous terms positive jets centres speeds regular motion).intervalIntegrable _ _)).symm

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb
