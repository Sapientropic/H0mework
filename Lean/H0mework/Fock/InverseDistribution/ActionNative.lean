import H0mework.Fock.InverseDistribution.StreamNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionAction

def refineEntry (letter : Option Nat) (previous : Option (Nat × ℚ) × ℚ) : Option (Nat × ℚ) × ℚ :=
  match previous.1 with
  | none => previous
  | some (state, weight) =>
      let next := SourceNativeInverseDistribution.splitEntry (SourceCopyWordAffine.compile [letter]) state weight
      (next.1, previous.2 + next.2)

def refine {Key : Type*} (bound : Nat) (letter : Option Nat)
    (previous : SourceInverseDistributionStream.State Key bound) : SourceInverseDistributionStream.State Key bound :=
  fun key => ((previous key).1, fun actor => refineEntry letter ((previous key).2 actor))

def generate {Key : Type*} [DecidableEq Key] (read : Nat → Key) (word : List (Option Nat)) (bound : Nat) :
    SourceInverseDistributionStream.State Key bound :=
  word.foldr (fun letter previous => refine bound letter previous)
    (SourceInverseDistributionStream.generate read (1, 0) bound)

end SourceInverseDistributionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
