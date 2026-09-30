import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeVisit.Generation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeVisit
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

def anchor (rank : Ordinal.{0}) : MotherArenaHigher.Base rank :=
  (MotherArenaHigher.baseReadEquiv rank).symm (fun _ _ => 0)

/-- The root's original generator consumes only a material origin tag and
depth. It returns the whole chronological visit, not a current-label proxy. -/
def formVisit (root : SourceNativeLivingRootClosure N V) (material : MotherArenaHigher.Material rank) : Option (Visit root) :=
  generate root (if MotherArenaHigher.read rank material (anchor rank) 0 = 0 then false else true)
    (Nat.floor (MotherArenaHigher.read rank material (anchor rank) 1))

theorem every_visit_material (root : SourceNativeLivingRootClosure N V) (visit : Visit root) :
    ∃ material : MotherArenaHigher.Material rank, formVisit root material = some visit := by
  obtain ⟨cofinal, steps, generated⟩ := every_visit root visit
  let reader : MotherArenaHigher.Base rank → Nat → ℝ := fun _ tag =>
    if tag = 0 then (if cofinal then 1 else 0) else steps
  obtain ⟨material, readback⟩ := MotherArenaHigher.read_surjective rank reader
  refine ⟨material, ?_⟩
  unfold formVisit
  rw [readback]
  cases cofinal <;>
    simpa only [reader, Bool.false_eq_true, if_false, ite_true,
      show ¬ (1 : Nat) = 0 from by decide, Nat.floor_natCast, one_ne_zero] using generated

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeVisit
