import H0mework.Chemistry.LAlanineBandCache.SaturationCell2

/-! Original cell2 Gaussian calculation material and its paid exponential/reduction consumers.
The other groups, AO rows and density-matrix fields have independent source obligations. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSaturation.Source

open SourceExponential SourceSignedEvaluator SourceGaussianModel SourceRectangle WholeBandSource
open WholeBandCache
noncomputable section

/-- Values of the actual registered calculation, retaining each call and group address. -/
structure Cell2SaturationMaterial where
  calls : Fin 64 → FullBandCall
  groups : SaturatedGroup → Group
  boxes : Fin 64 → Rectangle
  terms : SaturatedGroup → SourceGaussianModel.Term
  relativeCoordinates : Fin 64 → SaturatedGroup → Fin 3 → Pair
  exponents : SaturatedGroup → ℚ
  radialIntervals : Fin 64 → SaturatedGroup → Pair
  reductions : Fin 64 → SaturatedGroup → Nat × Nat
  exponentialIntervals : Fin 64 → SaturatedGroup → Pair
  actualGaussians : SaturatedGroup → Point → ℝ

def material : Cell2SaturationMaterial where
  calls := cell2Call
  groups := groupAt
  boxes := fun i => callBox (cell2Call i)
  terms := fun g => groupTerm (groupAt g)
  relativeCoordinates := fun i g => relative (groupTerm (groupAt g)) (callBox (cell2Call i))
  exponents := fun g => (groupTerm (groupAt g)).exponent
  radialIntervals := fun i g => radialPair (groupTerm (groupAt g)) (callBox (cell2Call i))
  reductions := fun i g => callReductions (cell2Call i) (groupAt g)
  exponentialIntervals := fun _ _ => (0,1/scale)
  actualGaussians := fun g x => Real.exp (radialArgument (groupTerm (groupAt g)) x)

/-- The shared interval is the output of the original evaluator at the retained source inputs. -/
theorem material_original_evaluator (i : Fin 64) (g : SaturatedGroup) :
    material.exponentialIntervals i g = exponential (material.radialIntervals i g)
      (material.reductions i g).1 (material.reductions i g).2 :=
  (cell2_exponential_saturated i g).symm

theorem material_actual_gaussian (i : Fin 64) (g : SaturatedGroup) (x : Point)
    (inside : InRectangle (material.boxes i) x) :
    Holds (material.exponentialIntervals i g) (material.actualGaussians g x) :=
  cell2_actual_exponential i g x inside

/-- The original cache constructor consumes the paid exponential and reduction fields.
The relative, radial and polynomial laws stay with the caller's actual rectangle cache. -/
theorem original_groupComputed (i : Fin 64) (g : SaturatedGroup) (cache : Material)
    (relative : List.ofFn (cachedRelative cache (groupAt g)) =
      List.ofFn (SourceSignedEvaluator.relative (groupTerm (groupAt g)) (material.boxes i)))
    (radial : cachedRadial cache (groupAt g) = material.radialIntervals i g)
    (stored : cachedExp cache (groupAt g) = material.exponentialIntervals i g)
    (polynomial :
      List.ofFn (fun a => List.ofFn (fun p => List.ofFn (cachedPoly cache (groupAt g) a p))) =
      List.ofFn (fun a : Fin 3 => List.ofFn (fun p : Fin 3 => List.ofFn (fun d : Fin 3 =>
        jetHorner (groupExponent (groupAt g)) p.val d.val (cachedRelative cache (groupAt g) a))))) :
    GroupComputed (material.boxes i) (callReductions (material.calls i)) cache (material.groups g) where
  relative := relative
  radial := radial
  exponential := by
    dsimp only [material]
    rw [radial, stored]
    exact material_original_evaluator i g
  polynomial := polynomial
  reductions := by
    dsimp only [material]
    rw [radial]
    exact (cell2_input_bounds i g).1

theorem source_calls_injective : Function.Injective material.calls := by
  intro a b same
  apply Fin.ext
  have values := congrArg Fin.val same
  change 128+a.val = 128+b.val at values
  omega

theorem source_groups_injective : Function.Injective material.groups := by decide +kernel

/-- Every field is paid by the original source parameters or the certified evaluator. -/
structure Cell2SaturationClosure : Prop where
  inputBounds : type_of% cell2_input_bounds
  originalEvaluator : type_of% material_original_evaluator
  actualGaussian : type_of% material_actual_gaussian
  cacheKernel : type_of% original_groupComputed
  calls : type_of% source_calls_injective
  groups : type_of% source_groups_injective

theorem sourceGeneratedCell2SaturationClosure : Cell2SaturationClosure :=
  ⟨cell2_input_bounds, material_original_evaluator, material_actual_gaussian,
    original_groupComputed, source_calls_injective, source_groups_injective⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandSaturation.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
