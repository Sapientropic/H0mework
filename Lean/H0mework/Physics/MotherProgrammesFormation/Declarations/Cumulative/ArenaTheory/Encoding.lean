import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank
variable {N : WorldRelationNetwork.{0}}

abbrev ExpressionTotal (old : TheoryState N) := Σ support, old.ExpressionAt support
abbrev RealizationTotal (old : TheoryState N) :=
  Σ support, Σ obstruction : N.ObstructionAt support, old.inventory.RealizationAt obstruction
abbrev WithoutTotal (old : TheoryState N) :=
  Σ law : old.inventory.Law, Σ support, Σ obstruction : N.ObstructionAt support,
    old.inventory.RealizationWithoutAt law obstruction
abbrev TheoremTotal (old : TheoryState N) :=
  Σ support, Σ expression : old.ExpressionAt support, old.TheoremAt expression
abbrev Total (old : TheoryState N) := old.inventory.Version ⊕ old.inventory.Law ⊕
  ExpressionTotal old ⊕ RealizationTotal old ⊕ WithoutTotal old ⊕ TheoremTotal old

structure Encoding (old : TheoryState N) where
  version : old.inventory.Version ↪ B
  law : old.inventory.Law ↪ B
  expression : ExpressionTotal old ↪ B
  realization : RealizationTotal old ↪ B
  without : WithoutTotal old ↪ B
  theoremMember : TheoremTotal old ↪ B

namespace Encoding
variable (coordinates : Coordinates (rank := rank) N) (old : TheoryState N) (encode : Encoding (rank := rank) old)

def graph (tag : Nat) (code : B) : Prop :=
  let first := MotherArenaHigher.unpair rank code
  let second := MotherArenaHigher.unpair rank first.2
  let third := MotherArenaHigher.unpair rank second.2
  match tag with
  | 0 => ∃ version, encode.version version = code
  | 1 => ∃ law, encode.law law = code
  | 2 => ∃ support expression, coordinates.support support = first.1 ∧ encode.expression ⟨support, expression⟩ = first.2
  | 3 => ∃ support obstruction value, coordinates.support support = first.1 ∧
      coordinates.obstruction support obstruction = second.1 ∧ encode.realization ⟨support, obstruction, value⟩ = second.2
  | 4 => ∃ law support obstruction value, encode.law law = first.1 ∧ coordinates.support support = second.1 ∧
      coordinates.obstruction support obstruction = third.1 ∧ encode.without ⟨law, support, obstruction, value⟩ = third.2
  | 5 => ∃ support expression value, coordinates.support support = first.1 ∧
      encode.expression ⟨support, expression⟩ = second.1 ∧ encode.theoremMember ⟨support, expression, value⟩ = second.2
  | 6 => encode.version old.inventory.version = code
  | 7 => ∃ support expression, coordinates.support support = first.1 ∧
      encode.expression ⟨support, expression⟩ = second.1 ∧ coordinates.claim (old.denotes expression) = second.2
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph coordinates old encode tag code then 0 else 1

theorem reader_bit {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode) (tag : Nat) (code : B) :
    bit material tag code ↔ graph coordinates old encode tag code := by
  by_cases seen : graph coordinates old encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def versionEquiv {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode) : old.inventory.Version ≃ Version material :=
  MotherArenaNetworkOrigin.imageEquiv encode.version (bit material 0)
    (fun code => reader_bit coordinates old encode hm 0 code)

def lawEquiv {material : MotherArenaHigher.Material rank}
    (hm : MotherArenaHigher.read rank material = reader coordinates old encode) : old.inventory.Law ≃ Law material :=
  MotherArenaNetworkOrigin.imageEquiv encode.law (bit material 1)
    (fun code => reader_bit coordinates old encode hm 1 code)

end Encoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
