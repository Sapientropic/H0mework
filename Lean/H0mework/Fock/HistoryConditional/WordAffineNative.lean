import H0mework.Fock.HistoryConditional.CopyWordNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyWordAffine

def compile (word : List (Option Nat)) : Nat × Nat :=
  word.foldr (fun letter suffix => match letter with
    | none => (suffix.1, suffix.1 + suffix.2)
    | some materialIndex => (suffix.1 * (materialIndex + 1), suffix.2)) (1, 0)

def execute (program : Nat × Nat) (state : Nat) : Nat := program.1 * (state + 1) + program.2 - 1

end SourceCopyWordAffine
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
