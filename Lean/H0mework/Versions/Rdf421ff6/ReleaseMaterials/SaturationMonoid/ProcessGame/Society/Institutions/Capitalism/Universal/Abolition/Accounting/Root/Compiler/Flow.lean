import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.First

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

/-- Internal compilation data. The domain computes every edge from an actual
source input; the compiler enumerates its rows rather than accepting coverage. -/
structure Flow (N : WorldRelationNetwork) where
  Current : Type
  initial : Current
  support : Current → N.Support
  next : Current → Current
  writes : Current → Bool
  evolution : (current : Current) →
    LedgerWriteEvolutionAt N ⟨support current⟩ ⟨support (next current)⟩
  finite : (current : Current) → Finite (OpenResponsibilityAt N (support current))
  injective : (current : Current) →
    Function.Injective (fun entry => ((evolution current).origin entry).1) ∧
    Function.Injective (fun entry => ((evolution current).destination entry).1)
  open_fibres : (support : N.Support) → (responsibility : N.Responsibility) →
    Subsingleton (N.OpenAt support responsibility)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
