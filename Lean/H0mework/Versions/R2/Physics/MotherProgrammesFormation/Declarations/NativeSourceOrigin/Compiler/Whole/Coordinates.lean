import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.TargetCoverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure LedgerCoordinates (N : WorldRelationNetwork.{0}) where
  support : N.Support ↪ B
  entry : ∀ s, OpenResponsibilityAt N s ↪ B
  transfer : ∀ s, N.DispositionAt s .transfer ↪ B
  settlement : ∀ s, N.DispositionAt s .supportSettlement ↪ B

private def canonicalLedgerCoordinates (material : M) (h : MotherNetworkFactory.Check material) :
    LedgerCoordinates (MotherNativeSourceOrigin.network material h) where
  support := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  entry := fun _ => {
    toFun := fun entry => MotherHigherLawFamily.pair (entry.1.val, entry.2.val)
    inj' := by
      rintro ⟨r, w⟩ ⟨r', w'⟩ same
      have pairEq := MotherHigherLawFamily.pair_injective same
      have responsibilityEq : r = r' := Subtype.ext (congrArg Prod.fst pairEq)
      cases responsibilityEq
      have witnessEq : w = w' := Subtype.ext (congrArg Prod.snd pairEq)
      cases witnessEq
      rfl }
  transfer := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  settlement := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def ledgerCoordinatesOfFormation (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) : LedgerCoordinates value.1 := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · have same := Option.some.inj formed
            exact Eq.mp (congrArg (fun source : SourceValue => LedgerCoordinates source.1) same)
              (canonicalLedgerCoordinates _ hn)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

theorem target_source_formed (material : M) (value : SourceValue)
    (coordinates : Coordinates value.2.2) (targets : TargetSection value.2.2)
    (formed : formTargets material = some ⟨value, coordinates, targets⟩) :
    MotherNativeSourceOrigin.formSource (MotherHigherLawValue.split material).1 = some value := by
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
    (coordinates : Coordinates value.2.2) (targets : TargetSection value.2.2)
    (formed : formTargets material = some ⟨value, coordinates, targets⟩) : LedgerCoordinates value.1 :=
  ledgerCoordinatesOfFormation (MotherHigherLawValue.split material).1 value
    (target_source_formed material value coordinates targets formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
