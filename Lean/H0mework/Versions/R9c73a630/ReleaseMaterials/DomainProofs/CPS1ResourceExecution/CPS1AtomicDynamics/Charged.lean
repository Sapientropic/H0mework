import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Material

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics.Charged
open CPS1LocalChemicalExecution CPS1AtomicSource

/-- Nuclear charge in elementary-charge units; isotope inertia enters a later raw row. -/
def atomicNumber : PeptideMaterial.Element → Nat
  | .H => 1 | .C => 6 | .N => 7 | .O => 8
  | .P => 15 | .K => 19 | .Mg => 12 | .S => 16

def electrons (atom : Primary.Atom) : Nat :=
  ((atomicNumber atom.element : Int) - atom.charge).toNat

inductive Address
  | nucleus (slot : Nat)
  | electron (slot orbital : Nat)
  deriving DecidableEq, Repr

structure Particle where
  address : Address
  source : Graph.Atom
  charge : Int
  deriving DecidableEq

/-- Slots are the source graph's actual ordered atoms. Electron indices carry that
same atom occurrence and retain its original residue/name payload. -/
def atomParticles (row : Graph.Atom × Nat) : List Particle :=
  ⟨.nucleus row.2,row.1,(atomicNumber row.1.source.element : Int)⟩ ::
    (List.range (electrons row.1.source)).map (fun orbital =>
      ⟨.electron row.2 orbital,row.1,-1⟩)

def particles (graph : Graph.Molecule) : List Particle :=
  graph.atoms.zipIdx.flatMap atomParticles

def charge (particles : List Particle) : Int := (particles.map Particle.charge).sum

theorem original_electron_count (aa : CPS1ResourceExecution.AA) :
    ∀ atom ∈ (Primary.template aa).atoms,
      atom.charge ≤ (atomicNumber atom.element : Int) := by
  cases aa <;> decide

theorem atom_charge (row : Graph.Atom × Nat)
    (valid : row.1.source.charge ≤ (atomicNumber row.1.source.element : Int)) :
    charge (atomParticles row) = row.1.source.charge := by
  have nonnegative : 0 ≤ (atomicNumber row.1.source.element : Int) - row.1.source.charge := by omega
  have restored := Int.toNat_of_nonneg nonnegative
  simp only [charge,atomParticles,List.map_cons,List.map_map,List.sum_cons]
  simp only [Function.comp_def]
  have repeated : (List.range (electrons row.1.source)).map (fun _ => (-1 : Int)) =
      List.replicate (electrons row.1.source) (-1 : Int) := by
    simp
  rw [repeated,List.sum_replicate]
  simp only [nsmul_eq_mul,mul_neg,mul_one,electrons]
  omega

theorem charge_flatMap {A : Type} (f : A → List Particle) (rows : List A) :
    charge (rows.flatMap f) = (rows.map (fun row => charge (f row))).sum := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons,charge,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at *
    rw [ih]

theorem particles_charge (graph : Graph.Molecule)
    (valid : ∀ atom ∈ graph.atoms, atom.source.charge ≤ (atomicNumber atom.source.element : Int)) :
    charge (particles graph) = Graph.charge graph := by
  have rows : ∀ row ∈ graph.atoms.zipIdx,
      row.1.source.charge ≤ (atomicNumber row.1.source.element : Int) := by
    intro row member
    exact valid _ (List.fst_mem_of_mem_zipIdx member)
  unfold particles Graph.charge
  rw [charge_flatMap]
  have pointwise : graph.atoms.zipIdx.map (fun row => charge (atomParticles row)) =
      graph.atoms.zipIdx.map (fun row => row.1.source.charge) := by
    apply List.map_congr_left
    intro row member
    exact atom_charge row (rows row member)
  rw [pointwise]
  change (graph.atoms.zipIdx.map ((fun atom : Graph.Atom => atom.source.charge) ∘ Prod.fst)).sum = _
  rw [← List.map_map]
  rw [List.zipIdx_map_fst]

theorem graph_atom_valid (word : List CPS1ResourceExecution.AA) (edges : List Nat)
    (atom : Graph.Atom) (member : atom ∈ (Graph.build Primary.template word edges).atoms) :
    atom.source.charge ≤ (atomicNumber atom.source.element : Int) := by
  rcases List.mem_flatMap.mp member with ⟨row,_,present⟩
  exact original_electron_count row.1 _ (Graph.source_atom_payload _ _ row atom present).1

theorem generated_charge (word : List CPS1ResourceExecution.AA) (edges : List Nat) :
    charge (particles (Graph.build Primary.template word edges)) =
      (Graph.requiredProtons word : Int) := by
  rw [particles_charge _ (graph_atom_valid word edges)]
  exact CPS1AtomicSource.Material.build_charge word edges

end CPS1AtomicDynamics.Charged
