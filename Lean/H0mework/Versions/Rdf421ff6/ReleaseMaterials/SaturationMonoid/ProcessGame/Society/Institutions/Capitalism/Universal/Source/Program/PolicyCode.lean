import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Data

/-! Execution and policy explanation share this source code.  Unknown
callbacks keep their original behavior and remain explicitly opaque. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

structure SettlementPolicyCode (Party : Type u) where
  issuer : Party
  recipient : Party
  tranche : ℚ

def SettlementPolicyCode.eval {Party Good Port Technology Instrument : Type u}
    [DecidableEq Party] (code : SettlementPolicyCode Party)
    (request : Request Party Good Port Technology Instrument) : Bool :=
  match request.operation with
  | .produce operator => decide (operator = code.issuer ∧ request.signer = operator)
  | .issue _ issuer recipient quantity =>
      decide (issuer = code.issuer ∧ recipient = code.recipient ∧ quantity = code.tranche)
  | .assign _ issuer _ _ _ => decide (issuer = code.issuer)
  | .settle _ debtor creditor _ =>
      decide (debtor = code.issuer ∧ creditor = code.recipient ∧ request.signer = creditor)
  | .use bearer _ .necessity => decide (bearer = code.recipient ∧ request.signer = bearer)
  | .present => true
  | _ => false

inductive RawPolicy (Party Good Port Technology Instrument : Type u)
  | unrestricted
  | settlement (code : SettlementPolicyCode Party)
  | opaque (run : RawCurrent Party Good Technology Instrument →
      Request Party Good Port Technology Instrument → Bool)

def RawPolicy.eval {Party Good Port Technology Instrument : Type u} [DecidableEq Party] :
    RawPolicy Party Good Port Technology Instrument →
      RawCurrent Party Good Technology Instrument → Request Party Good Port Technology Instrument → Bool
  | .unrestricted, _, _ => true
  | .settlement code, _, request => code.eval request
  | .opaque run, current, request => run current request

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
