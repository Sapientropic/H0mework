import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Members

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
open MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
    (coordinates : Coordinates (rank := rank) N) (old : TheoryState N) (encode : Encoding (rank := rank) old)
    {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode)

theorem version_graph (version : old.inventory.Version) :
    bit material 6 (versionEquiv coordinates old encode hm version).val ↔ version = old.inventory.version := by
  rw [reader_bit coordinates old encode hm]
  change encode.version old.inventory.version = encode.version version ↔ version = old.inventory.version
  exact ⟨fun same => (encode.version.injective same).symm, fun same => congrArg encode.version same.symm⟩

theorem denotes_graph (support : N.Support) (expression : old.ExpressionAt support) (claim : N.Claim) :
    r3 material 7 (coordinates.support support)
      (expressionEquiv coordinates old encode hm support expression).val (coordinates.claim claim) ↔
        claim = old.denotes expression := by
  rw [r3, reader_bit coordinates old encode hm]
  simp only [graph, MotherArenaHigher.unpair_pair]
  constructor
  · rintro ⟨other, exp, same, expEq, claimEq⟩
    have same := coordinates.support.injective same
    cases same
    have same := ((Function.Embedding.sigmaMk (β := old.ExpressionAt) support).trans encode.expression).injective expEq
    cases same
    exact (coordinates.claim.injective claimEq).symm
  · intro same
    cases same
    exact ⟨support, expression, rfl, rfl, rfl⟩

include hm in
theorem checked : DataCheck coordinates material where
  version := by
    refine ⟨versionEquiv coordinates old encode hm old.inventory.version,
      (version_graph coordinates old encode hm _).mpr rfl, ?_⟩
    intro version selected
    obtain ⟨version, rfl⟩ := (versionEquiv coordinates old encode hm).surjective version
    exact congrArg (versionEquiv coordinates old encode hm) ((version_graph coordinates old encode hm version).mp selected)
  denotes := by
    intro support expression
    obtain ⟨expression, rfl⟩ := (expressionEquiv coordinates old encode hm support).surjective expression
    exact ⟨old.denotes expression, (denotes_graph coordinates old encode hm support expression _).mpr rfl,
      fun claim selected => (denotes_graph coordinates old encode hm support expression claim).mp selected⟩

theorem version_value :
    Classical.choose (checked coordinates old encode hm).version =
      versionEquiv coordinates old encode hm old.inventory.version := by
  obtain ⟨version, same⟩ := (versionEquiv coordinates old encode hm).surjective
    (Classical.choose (checked coordinates old encode hm).version)
  have selected := (Classical.choose_spec (checked coordinates old encode hm).version).1
  rw [← same] at selected
  exact same.symm.trans (congrArg (versionEquiv coordinates old encode hm)
    ((version_graph coordinates old encode hm version).mp selected))

theorem denotes_value (support : N.Support) (expression : old.ExpressionAt support) :
    denotes coordinates material (checked coordinates old encode hm)
      (expressionEquiv coordinates old encode hm support expression) = old.denotes expression :=
  (denotes_graph coordinates old encode hm support expression _).mp
    (Classical.choose_spec ((checked coordinates old encode hm).denotes support
      (expressionEquiv coordinates old encode hm support expression))).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory.Encoding
