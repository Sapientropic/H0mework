import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Stock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Request" => Source.Program.Request Party Good Port Technology Instrument
local notation "Current" => RawCurrent Party Good Technology Instrument

omit [DecidableEq Instrument] in
instance (law : Law) (current : Current) (request : Request) : Decidable (Permitted law current request) := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  unfold Permitted RawLaw.SignerMatches RawLaw.ClaimGuard
  cases operation with
  | use bearer bundle tag => cases tag <;> infer_instance
  | _ => infer_instance

structure RawRefusal (law : Law) (current : Current) (word : Word) where
  original : ExecutionItem Party Good Port Technology Instrument
  occurs : original ∈ (law.execute current 0 word).items
  refused : ¬ Permitted law original.before original.request

inductive AuthorityDecision (law : Law) (current : Current) (word : Word)
  | authorized (all : Every law current 0 word (Permitted law))
  | refused (original : RawRefusal law current word)

def inspectAuthority (law : Law) (current : Current) (word : Word) : AuthorityDecision law current word :=
  let permits (item : ExecutionItem Party Good Port Technology Instrument) :=
    Permitted law item.before item.request
  match Abolition.Material.inspectList permits (law.execute current 0 word).items with
  | .failure item original denied => .refused ⟨item, original, denied⟩
  | .clear authorized => .authorized authorized

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
