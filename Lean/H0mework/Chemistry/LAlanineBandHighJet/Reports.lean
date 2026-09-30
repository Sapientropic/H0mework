import H0mework.Chemistry.LAlanineBandTaylor.Source
import H0mework.Chemistry.LAlanineBandSource.Data

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap

/-- Report admission is paid after the original field has been generated. -/
def PairWithin (inner outer : Pair) : Prop := outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2
instance (inner outer : Pair) : Decidable (PairWithin inner outer) := by unfold PairWithin; infer_instance

theorem pairWithin_holds {inner outer : Pair} (included : PairWithin inner outer)
    (x : ℝ) (h : Holds inner x) : Holds outer x :=
  ⟨(Rat.cast_le.mpr included.1).trans h.1,h.2.trans (Rat.cast_le.mpr included.2)⟩

structure FieldWithin (inner outer : FieldBox) : Prop where
  gradient : ∀ a, PairWithin (inner.gradient a) (outer.gradient a)
  hessian : ∀ a b, PairWithin (inner.hessian a b) (outer.hessian a b)

theorem fieldWithin_holds {inner outer : FieldBox} (included : FieldWithin inner outer)
    (x : Point) (h : FieldHolds inner x) : FieldHolds outer x :=
  ⟨fun a => pairWithin_holds (included.gradient a) _ (h.1 a),
   fun a b => pairWithin_holds (included.hessian a b) _ (h.2 a b)⟩

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
