import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Whole.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} (coordinates : LedgerCoordinates N)

/-- Branch tags retain the actual carried/maintained/transferred distinction;
transfer keeps its full source-owned receipt, even at an unchanged entry. -/
def rowKey {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t} :
    LedgerEntryEvolutionAt N a b → Nat × B
  | .carried .. => (0, coordinates.entry s a)
  | .maintained .. => (1, coordinates.entry s a)
  | .transferred receipt .. => (2, coordinates.transfer s receipt)

theorem rowKey_injective {s t : N.Support} {a : OpenResponsibilityAt N s} {b : OpenResponsibilityAt N t} :
    Function.Injective (rowKey coordinates (a := a) (b := b)) := by
  intro left right same
  cases left <;> cases right <;> simp_all [rowKey]

abbrev Destination (s t : N.Support) (a : OpenResponsibilityAt N s) :=
  Σ b : OpenResponsibilityAt N t, LedgerEntryEvolutionAt N a b

abbrev Origin (s t : N.Support) (b : OpenResponsibilityAt N t) :=
  Σ a : OpenResponsibilityAt N s, LedgerEntryEvolutionAt N a b

def destinationKey {s t : N.Support} {a : OpenResponsibilityAt N s} (output : Destination s t a) : Nat × B :=
  let key := rowKey coordinates output.2
  (key.1, MotherHigherLawFamily.pair (coordinates.entry t output.1, key.2))

theorem destinationKey_injective {s t : N.Support} {a : OpenResponsibilityAt N s} :
    Function.Injective (destinationKey coordinates (a := a) (t := t)) := by
  rintro ⟨b, row⟩ ⟨b', row'⟩ same
  have pairEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd same)
  have entryEq := (coordinates.entry t).injective (congrArg Prod.fst pairEq)
  cases entryEq
  have firstEq := congrArg (fun key : Nat × B => key.1) same
  have secondEq := congrArg (fun key : B × B => key.2) pairEq
  change (rowKey coordinates row).1 = (rowKey coordinates row').1 at firstEq
  change (rowKey coordinates row).2 = (rowKey coordinates row').2 at secondEq
  have rowEq : row = row' := rowKey_injective coordinates (Prod.ext firstEq secondEq)
  cases rowEq
  rfl

def originKey {s t : N.Support} {b : OpenResponsibilityAt N t} (output : Origin s t b) : Nat × B :=
  let key := rowKey coordinates output.2
  (key.1, MotherHigherLawFamily.pair (coordinates.entry s output.1, key.2))

theorem originKey_injective {s t : N.Support} {b : OpenResponsibilityAt N t} :
    Function.Injective (originKey coordinates (b := b) (s := s)) := by
  rintro ⟨a, row⟩ ⟨a', row'⟩ same
  have pairEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd same)
  have entryEq := (coordinates.entry s).injective (congrArg Prod.fst pairEq)
  cases entryEq
  have firstEq := congrArg (fun key : Nat × B => key.1) same
  have secondEq := congrArg (fun key : B × B => key.2) pairEq
  change (rowKey coordinates row).1 = (rowKey coordinates row').1 at firstEq
  change (rowKey coordinates row).2 = (rowKey coordinates row').2 at secondEq
  have rowEq : row = row' := rowKey_injective coordinates (Prod.ext firstEq secondEq)
  cases rowEq
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullCompiler
