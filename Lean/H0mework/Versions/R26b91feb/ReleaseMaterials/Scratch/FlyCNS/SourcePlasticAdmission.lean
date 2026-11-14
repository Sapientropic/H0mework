import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.Admission
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourcePlastic

/-! Source-byte admission of the complete original-row mushroom-body wiring.
Class/type interpretation is independently checked against the official
annotation table. This parser pays the byte/address/domain inventory and
generates a neural/plastic source before its first root emission. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace PlasticAdmission

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Admission

structure WiringBytes where
  roleKC : ByteArray
  roleDAN : ByteArray
  roleMBON : ByteArray
  domains : ByteArray
  siteEdges : ByteArray
  siteDomains : ByteArray
  danEdges : ByteArray
  danDomains : ByteArray

structure Vectors where
  private mk ::
  original : WiringBytes
  roleKC : NpyVector original.roleKC
  roleDAN : NpyVector original.roleDAN
  roleMBON : NpyVector original.roleMBON
  domains : NpyVector original.domains
  siteEdges : NpyVector original.siteEdges
  siteDomains : NpyVector original.siteDomains
  danEdges : NpyVector original.danEdges
  danDomains : NpyVector original.danDomains

def parseVectors (bytes : WiringBytes) : Except String Vectors := do
  let roleKC ← parseNpyVector bytes.roleKC "|u1" 1
  let roleDAN ← parseNpyVector bytes.roleDAN "|u1" 1
  let roleMBON ← parseNpyVector bytes.roleMBON "|u1" 1
  let domains ← parseNpyVector bytes.domains "<i4" 4
  let siteEdges ← parseNpyVector bytes.siteEdges "<i8" 8
  let siteDomains ← parseNpyVector bytes.siteDomains "<i4" 4
  let danEdges ← parseNpyVector bytes.danEdges "<i8" 8
  let danDomains ← parseNpyVector bytes.danDomains "<i4" 4
  return ⟨bytes, roleKC, roleDAN, roleMBON, domains, siteEdges, siteDomains, danEdges, danDomains⟩

def lowerBound {bytes : ByteArray} (vector : NpyVector bytes) (needle : Nat) :
    Nat → Nat → Nat → Nat
  | 0, low, _high => low
  | fuel + 1, low, high =>
    if low < high then
      let middle := (low + high) / 2
      if vector.word middle < needle then lowerBound vector needle fuel (middle + 1) high
      else lowerBound vector needle fuel low middle
    else low

def findAddress {bytes : ByteArray} (vector : NpyVector bytes) (count needle : Nat) :
    Option { index : Fin count // vector.word index.val = needle } :=
  let index := lowerBound vector needle 64 0 count
  if bounded : index < count then
    if exact : vector.word index = needle then some ⟨⟨index, bounded⟩, exact⟩ else none
  else none

def addressAt {bytes : ByteArray} (vector : NpyVector bytes) (count needle : Nat) :
    Option (Fin count) := (findAddress vector count needle).map Subtype.val

theorem addressAt_sound {bytes : ByteArray} (vector : NpyVector bytes)
    (count needle : Nat) (index : Fin count)
    (found : addressAt vector count needle = some index) : vector.word index.val = needle := by
  unfold addressAt at found
  cases result : findAddress vector count needle with
  | none => simp [result] at found
  | some matched =>
    simp only [result, Option.map_some, Option.some.injEq] at found
    cases found
    exact matched.property

def ShapeAt (vectors : Vectors) (neurons sites domains danInputs : Nat) : Prop :=
  vectors.roleKC.count = neurons ∧ vectors.roleDAN.count = neurons ∧
  vectors.roleMBON.count = neurons ∧ vectors.domains.count = domains ∧
  vectors.siteEdges.count = sites ∧ vectors.siteDomains.count = sites ∧
  vectors.danEdges.count = danInputs ∧ vectors.danDomains.count = danInputs

def BoundsAt (vectors : Vectors) (neurons edges sites domains danInputs : Nat) : Prop :=
  (∀ neuron : Fin neurons, vectors.roleKC.word neuron.val ≤ 1 ∧
    vectors.roleDAN.word neuron.val ≤ 1 ∧ vectors.roleMBON.word neuron.val ≤ 1) ∧
  (∀ domain : Fin domains, vectors.domains.word domain.val < neurons ∧
    addressAt vectors.domains domains (vectors.domains.word domain.val) = some domain) ∧
  (∀ site : Fin sites, vectors.siteEdges.word site.val < edges ∧
    vectors.siteDomains.word site.val < domains ∧
    addressAt vectors.siteEdges sites (vectors.siteEdges.word site.val) = some site) ∧
  (∀ input : Fin danInputs, vectors.danEdges.word input.val < edges ∧
    vectors.danDomains.word input.val < domains ∧
    addressAt vectors.danEdges danInputs (vectors.danEdges.word input.val) = some input)

instance (vectors : Vectors) (neurons sites domains danInputs : Nat) :
    Decidable (ShapeAt vectors neurons sites domains danInputs) := by
  unfold ShapeAt
  infer_instance

instance (vectors : Vectors) (neurons edges sites domains danInputs : Nat) :
    Decidable (BoundsAt vectors neurons edges sites domains danInputs) := by
  unfold BoundsAt
  infer_instance

structure Candidate (neurons edges sites domains danInputs : Nat) where
  private mk ::
  vectors : Vectors
  shape : ShapeAt vectors neurons sites domains danInputs
  bounds : BoundsAt vectors neurons edges sites domains danInputs

variable {neurons edges sites domains danInputs : Nat}

def Candidate.kc (data : Candidate neurons edges sites domains danInputs) (neuron : Fin neurons) : Bool :=
  decide (data.vectors.roleKC.word neuron.val = 1)

def Candidate.dan (data : Candidate neurons edges sites domains danInputs) (neuron : Fin neurons) : Bool :=
  decide (data.vectors.roleDAN.word neuron.val = 1)

def Candidate.mbon (data : Candidate neurons edges sites domains danInputs) (neuron : Fin neurons) : Bool :=
  decide (data.vectors.roleMBON.word neuron.val = 1)

def Candidate.domainNeuron (data : Candidate neurons edges sites domains danInputs) (domain : Fin domains) :
    Fin neurons := ⟨data.vectors.domains.word domain.val, (data.bounds.2.1 domain).1⟩

def Candidate.domainAt (data : Candidate neurons edges sites domains danInputs) (neuron : Fin neurons) :
    Option (Fin domains) := addressAt data.vectors.domains domains neuron.val

def Candidate.siteEdge (data : Candidate neurons edges sites domains danInputs) (site : Fin sites) : Fin edges :=
  ⟨data.vectors.siteEdges.word site.val, (data.bounds.2.2.1 site).1⟩

def Candidate.siteDomain (data : Candidate neurons edges sites domains danInputs) (site : Fin sites) : Fin domains :=
  ⟨data.vectors.siteDomains.word site.val, (data.bounds.2.2.1 site).2.1⟩

def Candidate.siteAt (data : Candidate neurons edges sites domains danInputs) (edge : Fin edges) :
    Option (Fin sites) := addressAt data.vectors.siteEdges sites edge.val

def Candidate.danEdge (data : Candidate neurons edges sites domains danInputs) (input : Fin danInputs) : Fin edges :=
  ⟨data.vectors.danEdges.word input.val, (data.bounds.2.2.2 input).1⟩

def Candidate.danDomain (data : Candidate neurons edges sites domains danInputs) (input : Fin danInputs) : Fin domains :=
  ⟨data.vectors.danDomains.word input.val, (data.bounds.2.2.2 input).2.1⟩

def Candidate.danAt (data : Candidate neurons edges sites domains danInputs) (edge : Fin edges) :
    Option (Fin danInputs) := addressAt data.vectors.danEdges danInputs edge.val

theorem Candidate.domain_inverse (data : Candidate neurons edges sites domains danInputs) (domain : Fin domains) :
    data.domainAt (data.domainNeuron domain) = some domain := (data.bounds.2.1 domain).2

theorem Candidate.domain_sound (data : Candidate neurons edges sites domains danInputs)
    {neuron : Fin neurons} {domain : Fin domains} (found : data.domainAt neuron = some domain) :
    data.domainNeuron domain = neuron := by
  apply Fin.ext
  exact addressAt_sound data.vectors.domains domains neuron.val domain found

theorem Candidate.site_inverse (data : Candidate neurons edges sites domains danInputs) (site : Fin sites) :
    data.siteAt (data.siteEdge site) = some site := (data.bounds.2.2.1 site).2.2

theorem Candidate.site_sound (data : Candidate neurons edges sites domains danInputs)
    {edge : Fin edges} {site : Fin sites} (found : data.siteAt edge = some site) :
    data.siteEdge site = edge := by
  apply Fin.ext
  exact addressAt_sound data.vectors.siteEdges sites edge.val site found

theorem Candidate.dan_inverse (data : Candidate neurons edges sites domains danInputs) (input : Fin danInputs) :
    data.danAt (data.danEdge input) = some input := (data.bounds.2.2.2 input).2.2

theorem Candidate.dan_sound (data : Candidate neurons edges sites domains danInputs)
    {edge : Fin edges} {input : Fin danInputs} (found : data.danAt edge = some input) :
    data.danEdge input = edge := by
  apply Fin.ext
  exact addressAt_sound data.vectors.danEdges danInputs edge.val input found

theorem Candidate.dan_injective (data : Candidate neurons edges sites domains danInputs) :
    Function.Injective data.danEdge := by
  intro left right same
  have equality := congrArg data.danAt same
  rw [data.dan_inverse left, data.dan_inverse right] at equality
  exact Option.some.inj equality

def SiteInventoryAt (graph : RawGraph neurons edges)
    (data : Candidate neurons edges sites domains danInputs) (edge : Fin edges) : Prop :=
  match data.domainAt (graph.post edge) with
  | none => True
  | some domain =>
      (∃ input, data.danDomain input = domain ∧ 0 < graph.contacts (data.danEdge input)) →
        (data.siteAt edge).isSome = true

instance (graph : RawGraph neurons edges) (data : Candidate neurons edges sites domains danInputs)
    (edge : Fin edges) : Decidable (SiteInventoryAt graph data edge) := by
  unfold SiteInventoryAt
  split <;> infer_instance

def WiringLaws (graph : RawGraph neurons edges)
    (data : Candidate neurons edges sites domains danInputs) : Prop :=
  (∀ domain : Fin domains, data.mbon (data.domainNeuron domain) = true) ∧
  (∀ neuron : Fin neurons, data.mbon neuron = true → (data.domainAt neuron).isSome = true) ∧
  (∀ input : Fin danInputs, data.dan (graph.pre (data.danEdge input)) = true ∧
    graph.post (data.danEdge input) = data.domainNeuron (data.danDomain input)) ∧
  (∀ site : Fin sites, data.kc (graph.pre (data.siteEdge site)) = true ∧
    graph.transmitterSign (graph.pre (data.siteEdge site)) = 1 ∧
    graph.post (data.siteEdge site) = data.domainNeuron (data.siteDomain site) ∧
    ∃ input, data.danDomain input = data.siteDomain site ∧ 0 < graph.contacts (data.danEdge input)) ∧
  (∀ edge : Fin edges, data.dan (graph.pre edge) = true → data.mbon (graph.post edge) = true →
    (data.danAt edge).isSome = true) ∧
  (∀ edge : Fin edges, data.kc (graph.pre edge) = true → graph.transmitterSign (graph.pre edge) = 1 →
    SiteInventoryAt graph data edge)

instance (graph : RawGraph neurons edges) (data : Candidate neurons edges sites domains danInputs) :
    Decidable (WiringLaws graph data) := by
  unfold WiringLaws
  infer_instance

structure AdmittedWiring (graph : RawGraph neurons edges) (sites domains danInputs : Nat) where
  private mk ::
  candidate : Candidate neurons edges sites domains danInputs
  laws : WiringLaws graph candidate

def admitWiringBytes (graph : RawGraph neurons edges) (sites domains danInputs : Nat)
    (bytes : WiringBytes) : Except String (AdmittedWiring graph sites domains danInputs) := do
  let vectors ← parseVectors bytes
  if shape : ShapeAt vectors neurons sites domains danInputs then
    if bounds : BoundsAt vectors neurons edges sites domains danInputs then
      let candidate : Candidate neurons edges sites domains danInputs := ⟨vectors, shape, bounds⟩
      if laws : WiringLaws graph candidate then return ⟨candidate, laws⟩
      else throw "source wiring omits or misidentifies an original anatomical row"
    else throw "source wiring address/role/inverse is invalid"
  else throw "source wiring vector dimensions differ"

def AdmittedWiring.rawWiring {graph : RawGraph neurons edges}
    (admitted : AdmittedWiring graph sites domains danInputs) (sourceRow : Fin edges → Nat) :
    Plastic.RawWiring graph sites domains danInputs where
  sourceRow := sourceRow
  isKC := admitted.candidate.kc
  isDAN := admitted.candidate.dan
  isMBON := admitted.candidate.mbon
  domainNeuron := admitted.candidate.domainNeuron
  domainAt := admitted.candidate.domainAt
  domain_inverse := admitted.candidate.domain_inverse
  domain_sound := admitted.candidate.domain_sound
  domain_isMBON := admitted.laws.1
  domain_inventory := by
    intro neuron isMBON
    have someDomain := admitted.laws.2.1 neuron isMBON
    cases found : admitted.candidate.domainAt neuron with
    | none => simp [found] at someDomain
    | some domain => exact ⟨domain, admitted.candidate.domain_sound found⟩
  siteEdge := admitted.candidate.siteEdge
  siteDomain := admitted.candidate.siteDomain
  siteAt := admitted.candidate.siteAt
  site_inverse := admitted.candidate.site_inverse
  site_sound := admitted.candidate.site_sound
  site_isKC := fun site => (admitted.laws.2.2.2.1 site).1
  site_positive := fun site => (admitted.laws.2.2.2.1 site).2.1
  site_endpoint := fun site => (admitted.laws.2.2.2.1 site).2.2.1
  danEdge := admitted.candidate.danEdge
  danDomain := admitted.candidate.danDomain
  dan_injective := admitted.candidate.dan_injective
  dan_isDAN := fun input => (admitted.laws.2.2.1 input).1
  dan_endpoint := fun input => (admitted.laws.2.2.1 input).2
  dan_inventory := by
    intro edge isDAN isMBON
    have someInput := admitted.laws.2.2.2.2.1 edge isDAN isMBON
    cases found : admitted.candidate.danAt edge with
    | none => simp [found] at someInput
    | some input => exact ⟨input, admitted.candidate.dan_sound found⟩
  site_hasDAN := fun site => (admitted.laws.2.2.2.1 site).2.2.2
  site_inventory := by
    intro edge isKC positive hasDAN
    obtain ⟨input, endpoint, contacts⟩ := hasDAN
    have sameDomain : admitted.candidate.domainAt (graph.post edge) =
        some (admitted.candidate.danDomain input) := by
      rw [← endpoint, (admitted.laws.2.2.1 input).2]
      exact admitted.candidate.domain_inverse _
    have inventory := admitted.laws.2.2.2.2.2 edge isKC positive
    unfold SiteInventoryAt at inventory
    rw [sameDomain] at inventory
    have someSite := inventory ⟨input, rfl, contacts⟩
    cases found : admitted.candidate.siteAt edge with
    | none => simp [found] at someSite
    | some site => exact ⟨site, admitted.candidate.site_sound found⟩

def sourceSites : Nat := 61210
def sourceDomains : Nat := 97
def sourceDanInputs : Nat := 3123

structure SourceWiringAdmission where
  private mk ::
  base : MaleCNSAdmission
  wiring : AdmittedWiring base.graph.rawGraph sourceSites sourceDomains sourceDanInputs
  graphManifest : ByteArray

def loadSourceWiringAdmission : IO SourceWiringAdmission := do
  let base ← loadMaleCNSFullGraph
  let graphManifest ← readFrozenFile "graph/manifest.json"
    "2566977e6d32f0664eeb1be65cd33cd0cf6e9a2053a041d3c08a89f0025c20e2" 2361
  let roleKC ← readFrozenFile "graph/mushroom-body/role_kc.npy"
    "e049b03d297a0f1f3263d2c875cca49161fec9509123c676fc25680a710d4400" 165250
  let roleDAN ← readFrozenFile "graph/mushroom-body/role_dan.npy"
    "fcf6e07be558864bcdeae76371bc90ed4084e11b333bb5f6c4ac05f13e94ad74" 165250
  let roleMBON ← readFrozenFile "graph/mushroom-body/role_mbon.npy"
    "9fbf4d71c08e7fbe14c2e6c33a5254d871d1fa9bb4f6c90f4cf2af258385dcc5" 165250
  let domains ← readFrozenFile "graph/mushroom-body/domain_neurons.npy"
    "07776718fbcb7b5f80d35b407f57c280afef3c786fdfdc5d39c8d7073cae9404" 516
  let siteEdges ← readFrozenFile "graph/mushroom-body/site_edges.npy"
    "252908f1568834a3f3eef9cdfe43a336e76a959cf98790da67ddfb6cdac76852" 489808
  let siteDomains ← readFrozenFile "graph/mushroom-body/site_domains.npy"
    "b490068dfbd1d973557f78d49004c3b1e4998267f618904f03c6b1eb64c24b1a" 244968
  let danEdges ← readFrozenFile "graph/mushroom-body/dan_edges.npy"
    "5393e13575cba2a796728daa8c334716ba4420ee54d4d0c20edf4e32c66992cf" 25112
  let danDomains ← readFrozenFile "graph/mushroom-body/dan_domains.npy"
    "72447abafb0b9b8b015f25bf09e30a890eb8ddeb7a1519b38dfbe101898e3795" 12620
  match admitWiringBytes base.graph.rawGraph sourceSites sourceDomains sourceDanInputs
      ⟨roleKC, roleDAN, roleMBON, domains, siteEdges, siteDomains, danEdges, danDomains⟩ with
  | .ok wiring => return ⟨base, wiring, graphManifest⟩
  | .error reason => throw (IO.userError reason)

def officialSource (admitted : SourceWiringAdmission) :
    Plastic.Source (neurons := neuronCount) (edges := edgeCount)
      sourceSites sourceDomains sourceDanInputs where
  graph := admitted.base.graph.rawGraph
  wiring := admitted.wiring.rawWiring admitted.base.graph.originalSourceRow
  rules := fun _ => {}
  initial := Plastic.initialJointState neuronCount edgeCount sourceSites sourceDomains 7
  pulses := (List.range 5000).map (registeredPulse sugarStimulus)
  instanceId := "male-cns-v1.0-KC-MBON-legacy275-seed7"

def namedPlasticFacade (admitted : SourceWiringAdmission) :=
  Plastic.runtimeFacade (officialSource admitted)

def namedPlasticSeed (admitted : SourceWiringAdmission) := (namedPlasticFacade admitted).seed

def loadMaleCNSPlasticSeed : IO (Σ admitted : SourceWiringAdmission,
    LivingRuntimeState (namedPlasticFacade admitted).process) := do
  let admitted ← loadSourceWiringAdmission
  return ⟨admitted, namedPlasticSeed admitted⟩

theorem named_plastic_source_has_original_graph (admitted : SourceWiringAdmission) :
    (officialSource admitted).graph = admitted.base.graph.rawGraph := rfl

theorem named_plastic_source_has_original_rows (admitted : SourceWiringAdmission) (edge : Fin edgeCount) :
    (officialSource admitted).wiring.sourceRow edge = admitted.base.graph.originalSourceRow edge := rfl

theorem named_seed_next_is_actual_plastic_update (admitted : SourceWiringAdmission) :
    (namedPlasticSeed admitted).tick.next.state.current =
      Plastic.step (officialSource admitted) (officialSource admitted).initial := rfl

set_option linter.defProp false in
def named_seed_plastic_weight_and_next (admitted : SourceWiringAdmission) (site : Fin sourceSites) :=
  Plastic.original_weight_and_next_factorizes (officialSource admitted) (namedPlasticSeed admitted) site

set_option linter.defProp false in
def named_seed_joint_face_factorizes (admitted : SourceWiringAdmission) (face : Plastic.PlasticFace) :=
  (namedPlasticFacade admitted).readoutAt_factorizes (namedPlasticSeed admitted) face

end PlasticAdmission
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
