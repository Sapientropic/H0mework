import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication.Comparison

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access

open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication

def candidate (n : Nat) : List Input := [personalCopy, consume n]

def Ready (n : Nat) (current : Current) : Prop :=
  ∀ item ∈ (law n).rawItems current (candidate n), (law n).Valid item.before item.request

instance (n : Nat) (current : Current) : Decidable (Ready n current) := by unfold Ready; infer_instance

inductive Response (n : Nat) (current : Current) where
  | admitted (valid : Ready n current)
  | refused (invalid : ¬ Ready n current)

def respond (n : Nat) (current : Current) : Response n current :=
  if valid : Ready n current then .admitted valid else .refused valid

def Response.word {n : Nat} {current : Current} : Response n current → List Input
  | .admitted _ => candidate n
  | .refused _ => []

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Access
