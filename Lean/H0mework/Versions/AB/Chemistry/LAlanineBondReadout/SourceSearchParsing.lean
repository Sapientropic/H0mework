import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.SourceReification

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.SearchParsing

open Lean Elab Term Inertia.SourceParsing LAlanine40K2025.Interface

def verifySearch (value : Json) : TermElabM Unit := do
  let seeds ← decode (Array Json) (← field value "seed_rows")
  let candidates ← decode (Array Json) (← field value "candidate_rows")
  unless seeds.size == 675 && candidates.size == (← decode Nat (← field value "candidate_count")) do
    throwError "Bond finite search census"
  let mut admitted := 0
  let mut hits := Array.replicate candidates.size 0
  let ctors := (← getConstInfoInduct ``ASUHeavyPair).ctors
  let addresses ← ctors.toArray.mapM SourceReification.registeredAddress
  for i in [:seeds.size] do
    let seed := seeds[i]!
    unless (← decode Nat (← field seed "seed_id")) == i &&
        addresses.contains (← decode (Array String) (← field seed "seed_address")) do
      throwError "Bond registered seed address"
    let selected ← field seed "candidate_id"
    let disposition ← decode String (← field seed "disposition")
    if selected == Json.null then
      unless disposition == "notAdmittedByRegisteredSearch" do throwError "Bond unadmitted disposition"
    else
      let selected ← decode Nat selected
      unless selected < candidates.size && disposition == "admittedCandidate" do throwError "Bond candidate reference"
      admitted := admitted + 1
      hits := hits.set! selected (hits[selected]! + 1)
  unless admitted == (← decode Nat (← field value "admitted_seed_count")) &&
      seeds.size - admitted == (← decode Nat (← field value "not_admitted_seed_count")) do
    throwError "Bond seed accounting"
  for i in [:candidates.size] do
    let candidate := candidates[i]!
    unless (← decode Nat (← field candidate "candidate_id")) == i &&
        (← decode Nat (← field candidate "seed_hit_count")) == hits[i]! do
      throwError "Bond candidate source incidence"

def verifyPairs (calculation : Json) (nuclei : Array Json) : TermElabM Unit := do
  let rows ← decode (Array Json) (← field calculation "pair_rows")
  let candidates ← decode (Array Json) (← field (← field calculation "finite_search_disposition") "candidate_rows")
  unless rows.size == 15 do throwError "Bond registered pair census"
  let mut positive : Array Json := #[]
  for row in rows do
    let address ← decode (Array String) (← field row "address")
    let indices ← decode (Array Nat) (← field row "nuclear_indices")
    unless address.size == 2 && indices.size == 2 do throwError "Bond two-nucleus incidence"
    let mut labels : Array String := #[]
    for index in indices do
      unless index < nuclei.size do throwError "Bond unknown nuclear index"
      labels := labels.push (← decode String (← field nuclei[index]! "label"))
    unless labels.qsort (· < ·) == address do throwError "Bond unordered same-nucleus address"
    let bcps ← decode (Array Json) (← field row "bcps")
    unless bcps.size == (← decode Nat (← field row "bcp_count")) do throwError "Bond BCP fibre count"
    if !bcps.isEmpty then positive := positive.push (← field row "address")
    for bcp in bcps do
      let selected ← decode Nat (← field bcp "candidate_id")
      unless selected < candidates.size do throwError "Bond unregistered BCP candidate"
      let candidate := candidates[selected]!
      unless (← decode (Array Nat) (← field candidate "signature")) == #[2, 0, 1] &&
          (← field candidate "endpoint_labels") == (← field row "address") do throwError "Bond candidate topology incidence"
      for key in ["endpoint_labels", "endpoint_traces", "seed_hit_count"] do
        unless (← field candidate key) == (← field bcp key) do throwError "Bond candidate read differs: {key}"
  unless positive == (← decode (Array Json) (← field calculation "positive_bcp_addresses")) &&
      positive.size == (← decode Nat (← field calculation "positive_bcp_count")) do throwError "Bond positive rows readout"

end LAlanine40K2025.BondReadout.SearchParsing
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
