import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Contract
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Charge

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution.SourceCharge
noncomputable section
open CPS1AtomicDynamics

def isElectron (particle : Charged.Particle) : Bool :=
  match particle.address with | .electron _ _ => true | .nucleus _ => false

def electronCount (particles : List Charged.Particle) : Nat := (particles.filter isElectron).length

def nuclearCharge (particles : List Charged.Particle) : Int :=
  ((particles.filter (fun particle => !isElectron particle)).map Charged.Particle.charge).sum

theorem charge_split (particles : List Charged.Particle)
    (electronic : ∀ particle ∈ particles, isElectron particle = true → particle.charge = -1) :
    Charged.charge particles = nuclearCharge particles - (electronCount particles : Int) := by
  induction particles with
  | nil => rfl
  | cons particle rest previous =>
    have kept : ∀ member ∈ rest, isElectron member = true → member.charge = -1 :=
      fun member present => electronic member (List.mem_cons_of_mem _ present)
    by_cases electron : isElectron particle = true
    · have paid := electronic particle (List.mem_cons_self) electron
      simp only [Charged.charge,List.map_cons,List.sum_cons,nuclearCharge,electronCount,
        List.filter_cons,electron,Bool.not_true,Bool.false_eq_true,if_false,if_true,List.length_cons]
      have following := previous kept
      simp only [Charged.charge,nuclearCharge,electronCount] at following
      rw [following,paid]
      push_cast
      ring
    · have nucleus : isElectron particle = false := Bool.eq_false_iff.mpr electron
      simp only [Charged.charge,List.map_cons,List.sum_cons,nuclearCharge,electronCount,
        List.filter_cons,nucleus,Bool.not_false,Bool.false_eq_true,if_false,if_true]
      have following := previous kept
      simp only [Charged.charge,nuclearCharge,electronCount] at following
      rw [following]
      ring

theorem source_electron_charge (row : CPS1AtomicSource.Graph.Atom × Nat)
    (particle : Charged.Particle) (present : particle ∈ Charged.atomParticles row)
    (electron : isElectron particle = true) : particle.charge = -1 := by
  simp only [Charged.atomParticles,List.mem_cons,List.mem_map] at present
  rcases present with nucleus | ⟨index,_,rfl⟩
  · cases nucleus
    cases electron
  · rfl

theorem graph_electron_charge (graph : CPS1AtomicSource.Graph.Molecule)
    (particle : Charged.Particle) (present : particle ∈ Charged.particles graph)
    (electron : isElectron particle = true) : particle.charge = -1 := by
  rcases List.mem_flatMap.mp present with ⟨row,_,member⟩
  exact source_electron_charge row particle member electron

theorem same_current_charge (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame) :
    nuclearCharge (CPS1EnzymeBath.Joint.particles frame joint) -
      (electronCount (CPS1EnzymeBath.Joint.particles frame joint) : Int) =
      Charged.charge (CPS1EnzymeBath.Joint.particles frame joint) :=
  (charge_split _ (graph_electron_charge _)).symm

end
end CPS1ElectronicEvolution.SourceCharge
