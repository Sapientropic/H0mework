import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Dictionary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.PrimaryFacts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1AtomicSource.Graph
open CPS1ResourceExecution
open CPS1LocalChemicalExecution.PeptideMaterial

abbrev TerminalLeave := Primary.TerminalLeave
abbrev TemplateAtom := Primary.Atom
abbrev TemplateBond := Primary.Bond
abbrev Template := Primary.Template

structure Address where
  residue : Nat
  atom : String
  deriving DecidableEq,Repr

structure Atom where
  address : Address
  source : TemplateAtom
  deriving DecidableEq

inductive BondOrigin | component | peptide deriving DecidableEq

structure Bond where
  left : Address
  right : Address
  order : String
  aromatic : Bool
  stereo : String
  origin : BondOrigin
  deriving DecidableEq

structure Molecule where
  atoms : List Atom
  bonds : List Bond
  invalidPeptideEdges : List Nat
  deriving DecidableEq

/-- A remaining edge connects residue i to i+1. Removing it restores the two
source terminal groups; no terminal hydrogen name is chosen by this mechanism. -/
def survives (edges : List Nat) (residue : Nat) (atom : TemplateAtom) : Bool :=
  match atom.terminalLeave with
  | .none => true
  | .amino => !(0 < residue && residue-1 ∈ edges)
  | .carboxyl => !(residue ∈ edges)

def residueAtoms (template : AA → Template) (edges : List Nat) (row : AA × Nat) : List Atom :=
  ((template row.1).atoms.filter (survives edges row.2)).map (fun atom => ⟨⟨row.2,atom.name⟩,atom⟩)

def componentBonds (template : AA → Template) (edges : List Nat) (row : AA × Nat) : List Bond :=
  let present := ((template row.1).atoms.filter (survives edges row.2)).map Primary.Atom.name
  ((template row.1).bonds.filter (fun bond => bond.left ∈ present && bond.right ∈ present)).map
    (fun bond => ⟨⟨row.2,bond.left⟩,⟨row.2,bond.right⟩,bond.order,bond.aromatic,bond.stereo,.component⟩)

def peptideBond (edge : Nat) : Bond :=
  ⟨⟨edge,"C"⟩,⟨edge+1,"N"⟩,"SING",false,"N",.peptide⟩

def build (template : AA → Template) (word : List AA) (remaining : List Nat) : Molecule :=
  let edges := remaining.filter (fun edge => edge+1 < word.length)
  ⟨word.zipIdx.flatMap (residueAtoms template edges),
    word.zipIdx.flatMap (componentBonds template edges) ++ edges.map peptideBond,
    remaining.filter (fun edge => ¬ edge+1 < word.length)⟩

def atoms (graph : Molecule) (element : Element) : Nat :=
  (graph.atoms.map (fun atom => if atom.source.element = element then 1 else 0)).sum

def charge (graph : Molecule) : Int := (graph.atoms.map (fun atom => atom.source.charge)).sum

def addressPresent (graph : Molecule) (address : Address) : Bool :=
  graph.atoms.any (fun atom => atom.address = address)

def dangling (graph : Molecule) : List Bond :=
  graph.bonds.filter (fun bond => !(addressPresent graph bond.left && addressPresent graph bond.right))

theorem empty_graph (template : AA → Template) (remaining : List Nat) :
    (build template [] remaining).atoms = [] ∧ (build template [] remaining).bonds = [] ∧
      (build template [] remaining).invalidPeptideEdges = remaining := by
  simp [build]

theorem source_atom_payload (template : AA → Template) (edges : List Nat) (row : AA × Nat)
    (atom : Atom) (present : atom ∈ residueAtoms template edges row) :
    atom.source ∈ (template row.1).atoms ∧ atom.address = ⟨row.2,atom.source.name⟩ := by
  rcases List.mem_map.mp present with ⟨source,member,same⟩
  subst atom
  exact ⟨(List.mem_filter.mp member).1,rfl⟩

theorem source_component_bond (template : AA → Template) (edges : List Nat) (row : AA × Nat)
    (bond : Bond) (present : bond ∈ componentBonds template edges row) :
    ∃ original ∈ (template row.1).bonds,
      bond.left = ⟨row.2,original.left⟩ ∧ bond.right = ⟨row.2,original.right⟩ ∧
      bond.order = original.order ∧ bond.aromatic = original.aromatic ∧ bond.stereo = original.stereo ∧
      bond.origin = .component := by
  rcases List.mem_map.mp present with ⟨original,member,same⟩
  subst bond
  exact ⟨original,(List.mem_filter.mp member).1,rfl,rfl,rfl,rfl,rfl,rfl⟩

def fromChain (frame : CPS1Recycling.Frame) (chain : CPS1LocalChemicalExecution.Chain frame) : Molecule :=
  build Primary.template (CPS1LocalChemicalExecution.Actual.cps1 frame).word chain.bonds

def requiredProtons (word : List AA) : Nat := (word.map Primary.additionalProtons).sum

theorem source_proline_edge :
    !(addressPresent (build Primary.template [.A,.P] [0]) ⟨0,"OXT"⟩) ∧
    !(addressPresent (build Primary.template [.A,.P] [0]) ⟨0,"HXT"⟩) ∧
    !(addressPresent (build Primary.template [.A,.P] [0]) ⟨1,"H"⟩) ∧
    addressPresent (build Primary.template [.A,.P] [0]) ⟨1,"N"⟩ := by decide +kernel

theorem source_proline_cut :
    addressPresent (build Primary.template [.A,.P] []) ⟨0,"OXT"⟩ ∧
    addressPresent (build Primary.template [.A,.P] []) ⟨0,"HXT"⟩ ∧
    addressPresent (build Primary.template [.A,.P] []) ⟨1,"H"⟩ ∧
    dangling (build Primary.template [.A,.P] []) = [] := by decide +kernel

theorem source_singleton :
    (build Primary.template [.P] []).atoms.length = Primary.PRO.atoms.length ∧
    dangling (build Primary.template [.P] []) = [] := by decide +kernel

theorem address_present_iff (graph : Molecule) (address : Address) :
    addressPresent graph address = true ↔ ∃ atom ∈ graph.atoms, atom.address = address := by
  simp only [addressPresent,List.any_eq_true,decide_eq_true_eq]

theorem residue_name_present (template : AA → Template) (edges : List Nat) (row : AA × Nat)
    (name : String) (present : name ∈ ((template row.1).atoms.filter (survives edges row.2)).map Primary.Atom.name) :
    ∃ atom ∈ residueAtoms template edges row, atom.address = ⟨row.2,name⟩ := by
  rcases List.mem_map.mp present with ⟨source,member,same⟩
  exact ⟨⟨⟨row.2,source.name⟩,source⟩,List.mem_map.mpr ⟨source,member,rfl⟩,by rw [same]⟩

theorem component_endpoints_present (template : AA → Template) (word : List AA) (remaining : List Nat)
    (row : AA × Nat) (inWord : row ∈ word.zipIdx) (bond : Bond)
    (present : bond ∈ componentBonds template (remaining.filter (fun edge => edge+1 < word.length)) row) :
    addressPresent (build template word remaining) bond.left = true ∧
      addressPresent (build template word remaining) bond.right = true := by
  rcases List.mem_map.mp present with ⟨source,member,same⟩
  subst bond
  have endpoints := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true,decide_eq_true_eq] at endpoints
  constructor
  · rcases residue_name_present template _ row source.left endpoints.1 with ⟨atom,member,eq⟩
    exact (address_present_iff _ _).mpr ⟨atom,List.mem_flatMap.mpr ⟨row,inWord,member⟩,eq⟩
  · rcases residue_name_present template _ row source.right endpoints.2 with ⟨atom,member,eq⟩
    exact (address_present_iff _ _).mpr ⟨atom,List.mem_flatMap.mpr ⟨row,inWord,member⟩,eq⟩

theorem backbone_present (word : List AA) (remaining : List Nat) (residue : Nat)
    (inWord : residue < word.length) (name : String) (backbone : name = "C" ∨ name = "N") :
    addressPresent (build Primary.template word remaining) ⟨residue,name⟩ = true := by
  let aa := word[residue]
  have row : (aa,residue) ∈ word.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_getElem inWord
  have core := Primary.original_backbone aa
  have selected : ((Primary.template aa).atoms.any (fun atom => atom.name = name && atom.terminalLeave = .none)) = true := by
    rcases backbone with rfl | rfl
    · exact core.1
    · exact core.2
  rcases List.any_eq_true.mp selected with ⟨source,member,properties⟩
  simp only [Bool.and_eq_true,decide_eq_true_eq] at properties
  apply (address_present_iff _ _).mpr
  refine ⟨⟨⟨residue,source.name⟩,source⟩,List.mem_flatMap.mpr ⟨(aa,residue),row,?_⟩,?_⟩
  · apply List.mem_map.mpr
    refine ⟨source,List.mem_filter.mpr ⟨member,?_⟩,rfl⟩
    simp only [survives,properties.2]
  · simp only [properties.1]

theorem no_dangling (word : List AA) (remaining : List Nat) :
    dangling (build Primary.template word remaining) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro bond member
  have source := (List.mem_filter.mp member).1
  have absent := (List.mem_filter.mp member).2
  have endpoints : addressPresent (build Primary.template word remaining) bond.left = true ∧
      addressPresent (build Primary.template word remaining) bond.right = true := by
    rcases List.mem_append.mp source with component | peptide
    · rcases List.mem_flatMap.mp component with ⟨row,inWord,componentMember⟩
      exact component_endpoints_present Primary.template word remaining row inWord bond componentMember
    · rcases List.mem_map.mp peptide with ⟨edge,valid,same⟩
      subst bond
      have bound : edge+1 < word.length := of_decide_eq_true (List.mem_filter.mp valid).2
      exact ⟨backbone_present word remaining edge (by omega) "C" (Or.inl rfl),
        backbone_present word remaining (edge+1) bound "N" (Or.inr rfl)⟩
  simp only [endpoints.1,endpoints.2,Bool.and_self,Bool.not_true] at absent
  exact Bool.false_ne_true absent

end CPS1AtomicSource.Graph
