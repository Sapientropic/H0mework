import H0mework.Versions.R2.Foundation.Responsibility.DebtPositiveRoot
import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- Internal event code. The domain computes these maps from its actual row;
whole-ledger transport has no finite inventory or submitted coverage field. -/
structure Code (N : WorldRelationNetwork) where
  Current : Type
  Fibre : Type
  emission : Fibre
  initial : Current
  supportAt : Current → Fibre → N.Support
  anchor_coherent : ∀ current origin,N.anchorAt (supportAt current emission) = N.anchorAt (supportAt current origin)
  incidence_coherent : ∀ current origin,N.incidenceAt (supportAt current emission) = N.incidenceAt (supportAt current origin)
  lineage_coherent : ∀ current origin,N.lineageAt (supportAt current emission) = N.lineageAt (supportAt current origin)
  next : Current → Current
  writes : Current → Bool
  evolution : (current : Current) → (origin : Fibre) →
    LedgerWriteEvolutionAt N ⟨supportAt current origin⟩ ⟨supportAt (next current) origin⟩
  inverse_origin : ∀ current origin entry, ((evolution current origin).destination ((evolution current origin).origin entry).1).1 = entry
  inverse_destination : ∀ current origin entry, ((evolution current origin).origin ((evolution current origin).destination entry).1).1 = entry

def Code.support {N : WorldRelationNetwork} (code : Code N) (current : code.Current) : N.Support :=
  code.supportAt current code.emission

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
