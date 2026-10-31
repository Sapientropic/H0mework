import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Budget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open Source.Program

variable {Party Good Port Technology Instrument : Type}

/-- The original source fee opcode and its positive external-use amount.
This declaration lives below the root adapters so their actual compiler can
consume the same code without importing its own eventual installation. -/
structure FeeCode where
  request : Request Party Good Port Technology Instrument
  scope : Review.FeeScope request

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
