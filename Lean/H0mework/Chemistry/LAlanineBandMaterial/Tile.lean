import H0mework.Chemistry.LAlanineBandMaterial.Evaluation
import H0mework.Chemistry.LAlanineBandHighJet.Bounds
import H0mework.Chemistry.LAlanineBandHighJet.Reports
import H0mework.Chemistry.LAlanineBandHighJet.TilesProducer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceIntegerGrid WholeBandSource
noncomputable section

structure TileEvaluation where
  center : Evaluation 0
  hull : Evaluation 1

def tileField (t : HighJet.Tile) (e : TileEvaluation) (f : FullBandCall) : IntervalParameterMap.FieldBox :=
  Taylor.fieldEnclosure (HighJet.center t) (callBox f)
    (HighJet.densityBounds 0 e.center.density) (HighJet.densityBounds 1 e.hull.density)

structure TileEvaluationSound (t : HighJet.Tile) (e : TileEvaluation) : Prop where
  center : EvaluationSound e.center
  hull : EvaluationSound e.hull
  centerBox : ∀ a, e.center.box a = (HighJet.center t a,HighJet.center t a)
  hullBox : e.hull.box = HighJet.tileBox t
  reports : ∀ i, HighJet.FieldWithin (tileField t e (HighJet.tileCall t i)) (recordedCallField (HighJet.tileCall t i))

theorem tileEvaluation_actual (t : HighJet.Tile) (e : TileEvaluation) (sound : TileEvaluationSound t e)
    (i : HighJet.Slot) (x : Point) (inside : InRectangle (callBox (HighJet.tileCall t i)) x) :
    IntervalParameterMap.FieldHolds (recordedCallField (HighJet.tileCall t i)) x := by
  have centerInside : InRectangle e.center.box (Taylor.centerPoint (HighJet.center t)) := by
    intro a
    rw [sound.centerBox]
    exact ⟨le_rfl,le_rfl⟩
  have ha : Taylor.CenterBounds (HighJet.center t) (HighJet.densityBounds 0 e.center.density) :=
    HighJet.centerBounds _ _ (fun j => evaluation_actual_density e.center sound.center j _ centerInside)
  have hb : Taylor.FourthBounds (HighJet.tileBox t) (HighJet.densityBounds 1 e.hull.density) := by
    rw [← sound.hullBox]
    exact HighJet.fourthBounds _ _ (evaluation_actual_density e.hull sound.hull)
  have subset : ∀ y, InRectangle (callBox (HighJet.tileCall t i)) y → InRectangle (HighJet.tileBox t) y := by
    intro y hy
    simpa only [HighJet.tileOf_tileCall] using HighJet.call_inside_hull (HighJet.tileCall t i) y hy
  exact HighJet.fieldWithin_holds (sound.reports i) x
    (Taylor.fieldEnclosure_contains _ _ _ _ _ ha hb (HighJet.center_inside t) subset x inside)

end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
