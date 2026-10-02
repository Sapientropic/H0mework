import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaCompiler.TargetCoverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
open MotherArenaNetwork MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure LedgerCoordinates (N : WorldRelationNetwork.{0}) where
  support : N.Support ↪ B
  entry : ∀ s, OpenResponsibilityAt N s ↪ B
  transfer : ∀ s, N.DispositionAt s .transfer ↪ B
  settlement : ∀ s, N.DispositionAt s .supportSettlement ↪ B

private def canonicalLedgerCoordinates (material : M) (h : MotherArenaNetwork.Check material) :
    LedgerCoordinates (rank := rank) (MotherArenaSource.network material h) where
  support := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  entry := fun _ => {
    toFun := fun entry => (MotherArenaHigher.pair rank) (entry.1.val, entry.2.val)
    inj' := by
      rintro ⟨r, w⟩ ⟨r', w'⟩ same
      have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
      have responsibilityEq : r = r' := Subtype.ext (congrArg Prod.fst pairEq)
      cases responsibilityEq
      have witnessEq : w = w' := Subtype.ext (congrArg Prod.snd pairEq)
      cases witnessEq
      rfl }
  transfer := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  settlement := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def ledgerCoordinatesOfFormation (material : M) (value : SourceValue)
    (formed : MotherArenaSource.formSource material = some value) : LedgerCoordinates (rank := rank) value.1 := by
  unfold MotherArenaSource.formSource MotherArenaSource.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · have same := Option.some.inj formed
            exact Eq.mp (congrArg (fun source : SourceValue => LedgerCoordinates (rank := rank) source.1) same)
              (canonicalLedgerCoordinates _ hn)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

theorem target_source_formed (material : M) (value : SourceValue)
    (coordinates : Coordinates (rank := rank) value.2.2) (targets : TargetSection value.2.2)
    (formed : formTargets material = some ⟨value, coordinates, targets⟩) :
    MotherArenaSource.formSource ((MotherArenaHigher.split rank) material).1 = some value := by
  unfold formTargets at formed
  dsimp only at formed
  split at formed
  · cases formed
  · rename_i source sourceCoordinates sourceFormed
    obtain ⟨generatedTargets, selected, same⟩ := Option.map_eq_some_iff.mp formed
    have sourceEq := congrArg Sigma.fst same
    have sourceMapped := congrArg (Option.map Sigma.fst) sourceFormed
    rw [coordinated_source_original] at sourceMapped
    exact sourceMapped.trans (congrArg some sourceEq)

def ledgerCoordinatesOfTargets (material : M) (value : SourceValue)
    (coordinates : Coordinates (rank := rank) value.2.2) (targets : TargetSection value.2.2)
    (formed : formTargets material = some ⟨value, coordinates, targets⟩) : LedgerCoordinates (rank := rank) value.1 :=
  ledgerCoordinatesOfFormation ((MotherArenaHigher.split rank) material).1 value
    (target_source_formed material value coordinates targets formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaCompiler
