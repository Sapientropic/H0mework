import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Network
import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Presentation

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetworkOrigin

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "M" => MotherArenaHigher.Material rank

namespace Factory
open MotherArenaNetwork

/-- Coverage data for the original factory, retaining every dependent witness.
This record is never an input to `formNetwork`. -/
structure Realizes (m : M) (N : WorldRelationNetwork.{0}) where
  support : N.Support ≃ Support m
  anchor : N.Anchor ≃ Anchor m
  incidence : N.Incidence ≃ Incidence m
  lineage : N.Lineage ≃ Lineage m
  responsibility : N.Responsibility ≃ Responsibility m
  claim : N.Claim ≃ Claim m
  openAt : ∀ s r, N.OpenAt s r ≃ OpenAt m (support s) (responsibility r)
  holdsAt : ∀ s c, N.HoldsAt s c ≃ HoldsAt m (support s) (claim c)
  obstructionAt : ∀ s, N.ObstructionAt s ≃ ObstructionAt m (support s)
  semanticChangeAt : ∀ s c d,
    N.SemanticChangeAt s c d ≃ SemanticChangeAt m (support s) (claim c) (claim d)
  dispositionAt : ∀ s k, N.DispositionAt s k ≃ DispositionAt m (support s) k
  anchor_graph : ∀ s a, r2 m 13 (support s).val a.val ↔ a = anchor (N.anchorAt s)
  incidence_graph : ∀ s a, r2 m 14 (support s).val a.val ↔ a = incidence (N.incidenceAt s)
  lineage_graph : ∀ s a, r2 m 15 (support s).val a.val ↔ a = lineage (N.lineageAt s)
  openClaim_graph : ∀ s r w c,
    r4 m 16 (support s).val (responsibility r).val (openAt s r w).val c.val ↔
      c = claim (N.openClaimAt w)
  obstructionClaim_graph : ∀ s w c,
    r3 m 17 (support s).val (obstructionAt s w).val c.val ↔
      c = claim (N.obstructionClaim w)
  budget_eq : ∀ s r w,
    budget m (support s) (responsibility r) (openAt s r w) = N.openProgressBudgetAt w

theorem Realizes.check {m : M} {N : WorldRelationNetwork.{0}} (r : Realizes m N) : Check m where
  anchor := by
    intro s
    obtain ⟨s, rfl⟩ := r.support.surjective s
    exact ⟨r.anchor (N.anchorAt s), (r.anchor_graph s _).mpr rfl,
      fun a h => (r.anchor_graph s a).mp h⟩
  incidence := by
    intro s
    obtain ⟨s, rfl⟩ := r.support.surjective s
    exact ⟨r.incidence (N.incidenceAt s), (r.incidence_graph s _).mpr rfl,
      fun a h => (r.incidence_graph s a).mp h⟩
  lineage := by
    intro s
    obtain ⟨s, rfl⟩ := r.support.surjective s
    exact ⟨r.lineage (N.lineageAt s), (r.lineage_graph s _).mpr rfl,
      fun a h => (r.lineage_graph s a).mp h⟩
  openClaim := by
    intro s a w
    obtain ⟨s, rfl⟩ := r.support.surjective s
    obtain ⟨a, rfl⟩ := r.responsibility.surjective a
    obtain ⟨w, rfl⟩ := (r.openAt s a).surjective w
    exact ⟨r.claim (N.openClaimAt w), (r.openClaim_graph s a w _).mpr rfl,
      fun c h => (r.openClaim_graph s a w c).mp h⟩
  obstructionClaim := by
    intro s w
    obtain ⟨s, rfl⟩ := r.support.surjective s
    obtain ⟨w, rfl⟩ := (r.obstructionAt s).surjective w
    exact ⟨r.claim (N.obstructionClaim w), (r.obstructionClaim_graph s w _).mpr rfl,
      fun c h => (r.obstructionClaim_graph s w c).mp h⟩

end Factory

abbrev Presentation (N G : WorldRelationNetwork.{0}) := MotherNetworkOrigin.Presentation N G

theorem Factory.Realizes.formed {m : M} {N : WorldRelationNetwork.{0}}
    (r : Factory.Realizes m N) :
    ∃ G, MotherArenaNetwork.formNetwork m = some G ∧ Nonempty (Presentation N G) := by
  refine ⟨_, MotherArenaNetwork.formNetwork_success m r.check, ⟨?_⟩⟩
  exact {
    support := r.support, anchor := r.anchor, incidence := r.incidence,
    lineage := r.lineage, responsibility := r.responsibility, claim := r.claim,
    openAt := r.openAt, holdsAt := r.holdsAt, obstructionAt := r.obstructionAt,
    semanticChangeAt := r.semanticChangeAt, dispositionAt := r.dispositionAt,
    anchor_commutes := fun s =>
      (r.anchor_graph s _).mp (Classical.choose_spec (r.check.anchor (r.support s))).1,
    incidence_commutes := fun s =>
      (r.incidence_graph s _).mp (Classical.choose_spec (r.check.incidence (r.support s))).1,
    lineage_commutes := fun s =>
      (r.lineage_graph s _).mp (Classical.choose_spec (r.check.lineage (r.support s))).1,
    openClaim_commutes := fun s a w => (r.openClaim_graph s a w _).mp
      (Classical.choose_spec (r.check.openClaim _ _ _)).1,
    obstructionClaim_commutes := fun s w => (r.obstructionClaim_graph s w _).mp
      (Classical.choose_spec (r.check.obstructionClaim _ _)).1,
    budget_commutes := r.budget_eq }

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetworkOrigin
