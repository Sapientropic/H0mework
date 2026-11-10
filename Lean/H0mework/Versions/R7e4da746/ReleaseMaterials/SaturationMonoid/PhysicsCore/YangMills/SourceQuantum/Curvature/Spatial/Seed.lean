import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Curvature.Affine.Polynomial
import Mathlib.Topology.ContinuousMap.CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BoundedContinuousFunction ContDiff

namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
noncomputable section
open Variation Flat.Quantum FullPairing StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite P286CoordinateIndex

abbrev Polynomial := FreeAlgebra ℂ (Fin 6)

def atPoint (p : BasePoint) : Polynomial →ₐ[ℂ] History.Polynomial :=
  FreeAlgebra.lift ℂ (fun r => FreeAlgebra.ι ℂ (p, r))

def first (η : Variation.Input) (r : Fin 6) : BasePoint →ᵇ Variation.Operator :=
  CompactlySupportedContinuousMap.toBoundedContinuousFunction
    { toFun := fun p => Variation.first η (p,r)
      continuous_toFun := Affine.coordinateOperator.toContinuousLinearMap.continuous.comp
        ((continuous_apply r).comp
          (p286GaugeConnectionLinearCurvatureVariation_continuous actual actual_smooth η))
      hasCompactSupport' := by
        rw [hasCompactSupport_iff_eventuallyEq]
        filter_upwards [compactP286GaugeConnectionVariation_eventually_jet_zero η] with p hp
        change Affine.coordinateOperator
          (p286GaugeConnectionLinearCurvatureVariation actual η p r) = 0
        rw [p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero actual η p hp.1 hp.2]
        exact Affine.coordinateOperator.map_zero }

def second (η : Variation.Input) (r : Fin 6) : BasePoint →ᵇ Variation.Operator :=
  CompactlySupportedContinuousMap.toBoundedContinuousFunction
    { toFun := fun p => Variation.second η (p,r)
      continuous_toFun := Affine.coordinateOperator.toContinuousLinearMap.continuous.comp
        ((continuous_apply r).comp
          (p286GaugeConnectionQuadraticCurvatureVariation_continuous η))
      hasCompactSupport' := by
        rw [hasCompactSupport_iff_eventuallyEq]
        filter_upwards [hasCompactSupport_iff_eventuallyEq.mp η.compactSupport] with p hp
        change Affine.coordinateOperator
          (p286GaugeConnectionQuadraticCurvatureVariation η p r) = 0
        rw [p286GaugeConnectionQuadraticCurvatureVariation_eq_zero η p hp]
        exact Affine.coordinateOperator.map_zero }

def generator (η : Variation.Input) (t : ℝ) (r : Fin 6) : BasePoint →ᵇ Variation.Operator :=
  BoundedContinuousFunction.const _ (NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ (0,r))) +
    t • first η r + t^2 • second η r

theorem original_generator (p : BasePoint) (r : Fin 6) :
    NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ (p,r)) =
      NativeSource.GaugeWords.seed (FreeAlgebra.ι ℂ (0,r)) := by
  simp only [NativeSource.GaugeWords.seed, quantumEvaluate_generator, History.field,
    actual_gaugeCurvature]

theorem generator_readback (η : Variation.Input) (t : ℝ) (p : BasePoint) (r : Fin 6) :
    generator η t r p = Variation.value η t (FreeAlgebra.ι ℂ (p,r)) := by
  rw [Variation.generator_expansion, original_generator]
  rfl

def seed (η : Variation.Input) (t : ℝ) : Polynomial →ₐ[ℂ] (BasePoint →ᵇ Variation.Operator) :=
  FreeAlgebra.lift ℂ (generator η t)

theorem seed_readback (η : Variation.Input) (t : ℝ) (P : Polynomial) (p : BasePoint) :
    seed η t P p = Variation.value η t (atPoint p P) := by
  induction P using FreeAlgebra.induction with
  | grade0 c =>
    simp [seed, atPoint, AlgHom.commutes]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  | grade1 r => simpa only [seed, atPoint, FreeAlgebra.lift_ι_apply] using generator_readback η t p r
  | mul P Q hP hQ => simp only [map_mul, BoundedContinuousFunction.mul_apply, hP, hQ]
  | add P Q hP hQ => simp only [map_add, BoundedContinuousFunction.add_apply, hP, hQ]

theorem seed_original (η : Variation.Input) (P : Polynomial) (p : BasePoint) :
    seed η 0 P p = NativeSource.GaugeWords.seed (atPoint p P) := by
  rw [seed_readback, Variation.value_original]

end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature.Spatial
