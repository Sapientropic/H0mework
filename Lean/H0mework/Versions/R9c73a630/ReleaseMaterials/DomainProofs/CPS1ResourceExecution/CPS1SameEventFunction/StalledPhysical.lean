import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedAtomic

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

theorem fire_two_cut {S R : Type} [DecidableEq S] (reactants products : R → List S)
    (reaction : R) (stock : List S) (carrier missing : S)
    (required : reactants reaction = [carrier,missing]) (present : carrier ∈ stock) (absent : missing ∉ stock) :
    Inventory.fire reactants products reaction stock = .error missing := by
  have absentAfter : missing ∉ stock.erase carrier := fun held => absent (List.mem_of_mem_erase held)
  simp only [Inventory.fire,required,Inventory.consume,if_pos present,if_neg absentAfter]

def bathCP (f : CPS1Recycling.Frame) := CPS1EnzymeBath.componentSpecies f .carbamoylPhosphate
def electronicCP (f : CPS1Recycling.Frame) : CPS1ElectronicSource.Species f := .retained (bathCP f)
def nuclearCP (f : CPS1Recycling.Frame) : CPS1QuantumNuclear.Species f := .retained (electronicCP f)
def followingCP (f : CPS1Recycling.Frame) : CPS1Following.Species f := .retained (nuclearCP f)
def molecularCP (f : CPS1Recycling.Frame) : CPS1MolecularFrame.Species f := .retained (followingCP f)
def deformedCP (f : CPS1Recycling.Frame) : CPS1Deformation.Species f := .retained (molecularCP f)

def electronicAttach : CPS1ElectronicSource.Source.RawAction := .old (.attach .carbamoylPhosphate)
def nuclearAttach : CPS1QuantumNuclear.Source.RawAction := .old electronicAttach
def followingAttach : CPS1Following.Source.RawAction := .old nuclearAttach
def molecularAttach : CPS1MolecularFrame.Source.RawAction := .old followingAttach
def deformedAttach : CPS1Deformation.Source.RawAction := .old molecularAttach

theorem bath_partner_cut (cursor : CPS1EnzymeBath.Source.Cursor frame)
    (joint : CPS1EnzymeBath.Joint.State frame) (tail : CPS1EnzymeBath.Stock frame)
    (head : cursor.stock = .joint joint :: tail) (captured : cursor.captureRemaining = []) (pending : cursor.pending = [])
    (absent : bathCP frame ∉ cursor.stock) :
    (CPS1EnzymeBath.Source.advance frame cursor CPS1EnzymeBath.Source.generatedPartnerProgram []).stock = cursor.stock ∧
    (CPS1EnzymeBath.Source.advance frame cursor CPS1EnzymeBath.Source.generatedPartnerProgram []).pending = [.attach .carbamoylPhosphate] ∧
    (CPS1EnzymeBath.Source.advance frame cursor CPS1EnzymeBath.Source.generatedPartnerProgram []).cut = some (bathCP frame) := by
  have held : CPS1EnzymeBath.Source.heldJoint frame cursor.stock = some joint := by rw [head]; rfl
  have present : CPS1EnzymeBath.Species.joint joint ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have first := fire_two_cut (CPS1EnzymeBath.Reaction.reactants frame) (CPS1EnzymeBath.Reaction.products frame)
    (.attach joint .carbamoylPhosphate) cursor.stock (.joint joint) (bathCP frame) rfl present absent
  unfold CPS1EnzymeBath.Source.advance CPS1EnzymeBath.Source.generatedPartnerProgram
  simp only [List.map_nil,List.flatMap_cons,List.flatMap_nil,CPS1EnzymeBath.Source.RawAction.material,
    List.nil_append,List.append_nil,captured,pending,held]
  dsimp only [CPS1EnzymeBath.Source.program,CPS1EnzymeBath.Source.RawAction.reaction]
  rw [CPS1EnzymeBath.execute,Inventory.execute_cons,first]
  exact ⟨rfl,rfl,rfl⟩

theorem electronic_program_cp_cut (stock : CPS1ElectronicSource.Stock frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1ElectronicSource.Source.RawAction) (held : CPS1ElectronicSource.Source.heldCarrier frame stock = some (.joint joint))
    (present : (.retained (.joint joint) : CPS1ElectronicSource.Species frame) ∈ stock) (absent : electronicCP frame ∉ stock) :
    CPS1ElectronicSource.execute frame (CPS1ElectronicSource.Source.program frame (CPS1ElectronicSource.Source.heldCarrier frame stock) (electronicAttach :: rest)) stock =
      ⟨[],CPS1ElectronicSource.Source.program frame (CPS1ElectronicSource.Source.heldCarrier frame stock) (electronicAttach :: rest),stock,some (electronicCP frame)⟩ := by
  have required : CPS1ElectronicSource.Reaction.reactants frame (CPS1ElectronicSource.Reaction.jointAttach joint .carbamoylPhosphate) = [(.retained (.joint joint) : CPS1ElectronicSource.Species frame),electronicCP frame] := by
    simp only [CPS1ElectronicSource.Reaction.reactants]
    rfl
  have first := fire_two_cut (CPS1ElectronicSource.Reaction.reactants frame) (CPS1ElectronicSource.Reaction.products frame)
    (CPS1ElectronicSource.Reaction.jointAttach joint .carbamoylPhosphate) stock (.retained (.joint joint) : CPS1ElectronicSource.Species frame) (electronicCP frame) required present absent
  rw [held]
  dsimp only [CPS1ElectronicSource.Source.program,electronicAttach,deformedAttach,molecularAttach,followingAttach,nuclearAttach,electronicAttach,CPS1ElectronicSource.Source.RawAction.reaction]
  rw [CPS1ElectronicSource.execute,Inventory.execute_cons,first]

theorem electronic_advance_cp_cut (cursor : CPS1ElectronicSource.Source.Cursor frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (tail : CPS1ElectronicSource.Stock frame) (rest : List CPS1ElectronicSource.Source.RawAction)
    (head : cursor.stock = (.retained (.joint joint) : CPS1ElectronicSource.Species frame) :: tail)
    (pending : cursor.pending = electronicAttach :: rest) (absent : electronicCP frame ∉ cursor.stock) :
    (CPS1ElectronicSource.Source.advance frame cursor [] []).stock = cursor.stock ∧
    (CPS1ElectronicSource.Source.advance frame cursor [] []).pending = cursor.pending ∧
    (CPS1ElectronicSource.Source.advance frame cursor [] []).cut = some (electronicCP frame) := by
  have held : CPS1ElectronicSource.Source.heldCarrier frame cursor.stock = some (.joint joint) := by rw [head]; rfl
  have present : (.retained (.joint joint) : CPS1ElectronicSource.Species frame) ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have cut := electronic_program_cp_cut cursor.stock joint rest held present absent
  unfold CPS1ElectronicSource.Source.advance
  simp only [List.map_nil,List.flatMap_nil,List.append_nil,List.nil_append]
  rw [pending,cut]
  exact ⟨rfl,rfl,rfl⟩

theorem nuclear_program_cp_cut (stock : CPS1QuantumNuclear.Stock frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1QuantumNuclear.Source.RawAction) (held : CPS1QuantumNuclear.Source.heldCarrier frame stock = some (.joint joint))
    (present : (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) ∈ stock) (absent : nuclearCP frame ∉ stock) :
    CPS1QuantumNuclear.execute frame (CPS1QuantumNuclear.Source.program frame (CPS1QuantumNuclear.Source.heldCarrier frame stock) (nuclearAttach :: rest)) stock =
      ⟨[],CPS1QuantumNuclear.Source.program frame (CPS1QuantumNuclear.Source.heldCarrier frame stock) (nuclearAttach :: rest),stock,some (nuclearCP frame)⟩ := by
  have required : CPS1QuantumNuclear.Reaction.reactants frame (.retained (.jointAttach joint .carbamoylPhosphate)) = [(.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame),nuclearCP frame] := by
    simp only [CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,List.map_cons,List.map_nil]
    rfl
  have first := fire_two_cut (CPS1QuantumNuclear.Reaction.reactants frame) (CPS1QuantumNuclear.Reaction.products frame)
    (.retained (.jointAttach joint .carbamoylPhosphate)) stock (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) (nuclearCP frame) required present absent
  rw [held]
  dsimp only [CPS1QuantumNuclear.Source.program,nuclearAttach,deformedAttach,molecularAttach,followingAttach,nuclearAttach,electronicAttach,CPS1QuantumNuclear.Source.RawAction.reaction,CPS1ElectronicSource.Source.RawAction.reaction]
  rw [CPS1QuantumNuclear.execute,Inventory.execute_cons,first]

theorem nuclear_advance_cp_cut (cursor : CPS1QuantumNuclear.Source.Cursor frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (tail : CPS1QuantumNuclear.Stock frame) (rest : List CPS1QuantumNuclear.Source.RawAction)
    (head : cursor.stock = (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) :: tail)
    (pending : cursor.pending = nuclearAttach :: rest) (absent : nuclearCP frame ∉ cursor.stock) :
    (CPS1QuantumNuclear.Source.advance frame cursor [] []).stock = cursor.stock ∧
    (CPS1QuantumNuclear.Source.advance frame cursor [] []).pending = cursor.pending ∧
    (CPS1QuantumNuclear.Source.advance frame cursor [] []).cut = some (nuclearCP frame) := by
  have held : CPS1QuantumNuclear.Source.heldCarrier frame cursor.stock = some (.joint joint) := by rw [head]; rfl
  have present : (.retained (.retained (.joint joint)) : CPS1QuantumNuclear.Species frame) ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have cut := nuclear_program_cp_cut cursor.stock joint rest held present absent
  unfold CPS1QuantumNuclear.Source.advance
  simp only [List.map_nil,List.flatMap_nil,List.append_nil,List.nil_append]
  rw [pending,cut]
  exact ⟨rfl,rfl,rfl⟩

theorem following_program_cp_cut (stock : CPS1Following.Stock frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1Following.Source.RawAction) (held : CPS1Following.Source.heldCarrier frame stock = some (.reference (.joint joint)))
    (present : (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) ∈ stock) (absent : followingCP frame ∉ stock) :
    CPS1Following.execute frame (CPS1Following.Source.program frame (CPS1Following.Source.heldCarrier frame stock) (followingAttach :: rest)) stock =
      ⟨[],CPS1Following.Source.program frame (CPS1Following.Source.heldCarrier frame stock) (followingAttach :: rest),stock,some (followingCP frame)⟩ := by
  have required : CPS1Following.Reaction.reactants frame (.retained (.retained (.jointAttach joint .carbamoylPhosphate))) = [(.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame),followingCP frame] := by
    simp only [CPS1Following.Reaction.reactants,CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,List.map_cons,List.map_nil]
    rfl
  have first := fire_two_cut (CPS1Following.Reaction.reactants frame) (CPS1Following.Reaction.products frame)
    (.retained (.retained (.jointAttach joint .carbamoylPhosphate))) stock (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) (followingCP frame) required present absent
  rw [held]
  dsimp only [CPS1Following.Source.program,followingAttach,deformedAttach,molecularAttach,followingAttach,nuclearAttach,electronicAttach,CPS1Following.Source.RawAction.reaction,CPS1QuantumNuclear.Source.RawAction.reaction,CPS1ElectronicSource.Source.RawAction.reaction]
  rw [CPS1Following.execute,Inventory.execute_cons,first]

theorem following_advance_cp_cut (cursor : CPS1Following.Source.Cursor frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (tail : CPS1Following.Stock frame) (rest : List CPS1Following.Source.RawAction)
    (head : cursor.stock = (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) :: tail)
    (pending : cursor.pending = followingAttach :: rest) (absent : followingCP frame ∉ cursor.stock) :
    (CPS1Following.Source.advance frame cursor [] []).stock = cursor.stock ∧
    (CPS1Following.Source.advance frame cursor [] []).pending = cursor.pending ∧
    (CPS1Following.Source.advance frame cursor [] []).cut = some (followingCP frame) := by
  have held : CPS1Following.Source.heldCarrier frame cursor.stock = some (.reference (.joint joint)) := by rw [head]; rfl
  have present : (.retained (.retained (.retained (.joint joint))) : CPS1Following.Species frame) ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have cut := following_program_cp_cut cursor.stock joint rest held present absent
  unfold CPS1Following.Source.advance
  simp only [List.map_nil,List.flatMap_nil,List.append_nil,List.nil_append]
  rw [pending,cut]
  exact ⟨rfl,rfl,rfl⟩

theorem molecular_program_cp_cut (stock : CPS1MolecularFrame.Stock frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1MolecularFrame.Source.RawAction) (held : CPS1MolecularFrame.Source.heldCarrier frame stock = some (.following (.reference (.joint joint))))
    (present : (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) ∈ stock) (absent : molecularCP frame ∉ stock) :
    CPS1MolecularFrame.execute frame (CPS1MolecularFrame.Source.program frame (CPS1MolecularFrame.Source.heldCarrier frame stock) (molecularAttach :: rest)) stock =
      ⟨[],CPS1MolecularFrame.Source.program frame (CPS1MolecularFrame.Source.heldCarrier frame stock) (molecularAttach :: rest),stock,some (molecularCP frame)⟩ := by
  have required : CPS1MolecularFrame.Reaction.reactants frame (.retained (.retained (.retained (.jointAttach joint .carbamoylPhosphate)))) = [(.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame),molecularCP frame] := by
    simp only [CPS1MolecularFrame.Reaction.reactants,CPS1Following.Reaction.reactants,CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,List.map_cons,List.map_nil]
    rfl
  have first := fire_two_cut (CPS1MolecularFrame.Reaction.reactants frame) (CPS1MolecularFrame.Reaction.products frame)
    (.retained (.retained (.retained (.jointAttach joint .carbamoylPhosphate)))) stock (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) (molecularCP frame) required present absent
  rw [held]
  dsimp only [CPS1MolecularFrame.Source.program,molecularAttach,deformedAttach,molecularAttach,followingAttach,nuclearAttach,electronicAttach,CPS1MolecularFrame.Source.RawAction.reaction,CPS1Following.Source.RawAction.reaction,CPS1QuantumNuclear.Source.RawAction.reaction,CPS1ElectronicSource.Source.RawAction.reaction]
  rw [CPS1MolecularFrame.execute,Inventory.execute_cons,first]

theorem molecular_advance_cp_cut (cursor : CPS1MolecularFrame.Source.Cursor frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (tail : CPS1MolecularFrame.Stock frame) (rest : List CPS1MolecularFrame.Source.RawAction)
    (head : cursor.stock = (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) :: tail)
    (pending : cursor.pending = molecularAttach :: rest) (absent : molecularCP frame ∉ cursor.stock) :
    (CPS1MolecularFrame.Source.advance frame cursor [] []).stock = cursor.stock ∧
    (CPS1MolecularFrame.Source.advance frame cursor [] []).pending = cursor.pending ∧
    (CPS1MolecularFrame.Source.advance frame cursor [] []).cut = some (molecularCP frame) := by
  have held : CPS1MolecularFrame.Source.heldCarrier frame cursor.stock = some (.following (.reference (.joint joint))) := by rw [head]; rfl
  have present : (.retained (.retained (.retained (.retained (.joint joint)))) : CPS1MolecularFrame.Species frame) ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have cut := molecular_program_cp_cut cursor.stock joint rest held present absent
  unfold CPS1MolecularFrame.Source.advance
  simp only [List.map_nil,List.flatMap_nil,List.append_nil,List.nil_append]
  rw [pending,cut]
  exact ⟨rfl,rfl,rfl⟩

theorem deformed_program_cp_cut (stock : CPS1Deformation.Stock frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (rest : List CPS1Deformation.Source.RawAction) (held : CPS1Deformation.Source.heldCarrier frame stock = some (.molecular (.following (.reference (.joint joint)))))
    (present : (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame) ∈ stock) (absent : deformedCP frame ∉ stock) :
    CPS1Deformation.execute frame (CPS1Deformation.Source.program frame (CPS1Deformation.Source.heldCarrier frame stock) (deformedAttach :: rest)) stock =
      ⟨[],CPS1Deformation.Source.program frame (CPS1Deformation.Source.heldCarrier frame stock) (deformedAttach :: rest),stock,some (deformedCP frame)⟩ := by
  have required : CPS1Deformation.Reaction.reactants frame (.retained (.retained (.retained (.retained (.jointAttach joint .carbamoylPhosphate))))) = [(.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame),deformedCP frame] := by
    simp only [CPS1Deformation.Reaction.reactants,CPS1MolecularFrame.Reaction.reactants,CPS1Following.Reaction.reactants,CPS1QuantumNuclear.Reaction.reactants,CPS1ElectronicSource.Reaction.reactants,List.map_cons,List.map_nil]
    rfl
  have first := fire_two_cut (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame)
    (.retained (.retained (.retained (.retained (.jointAttach joint .carbamoylPhosphate))))) stock (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame) (deformedCP frame) required present absent
  rw [held]
  dsimp only [CPS1Deformation.Source.program,deformedAttach,deformedAttach,molecularAttach,followingAttach,nuclearAttach,electronicAttach,CPS1Deformation.Source.RawAction.reaction,CPS1MolecularFrame.Source.RawAction.reaction,CPS1Following.Source.RawAction.reaction,CPS1QuantumNuclear.Source.RawAction.reaction,CPS1ElectronicSource.Source.RawAction.reaction]
  rw [CPS1Deformation.execute,Inventory.execute_cons,first]

theorem deformed_advance_cp_cut (cursor : CPS1Deformation.Source.Cursor frame) (joint : CPS1EnzymeBath.Joint.State frame)
    (tail : CPS1Deformation.Stock frame) (rest : List CPS1Deformation.Source.RawAction)
    (head : cursor.stock = (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame) :: tail)
    (pending : cursor.pending = deformedAttach :: rest) (absent : deformedCP frame ∉ cursor.stock) :
    (CPS1Deformation.Source.advance frame cursor [] []).stock = cursor.stock ∧
    (CPS1Deformation.Source.advance frame cursor [] []).pending = cursor.pending ∧
    (CPS1Deformation.Source.advance frame cursor [] []).cut = some (deformedCP frame) := by
  have held : CPS1Deformation.Source.heldCarrier frame cursor.stock = some (.molecular (.following (.reference (.joint joint)))) := by rw [head]; rfl
  have present : (.retained (.retained (.retained (.retained (.retained (.joint joint))))) : CPS1Deformation.Species frame) ∈ cursor.stock := by rw [head]; exact List.mem_cons_self
  have cut := deformed_program_cp_cut cursor.stock joint rest held present absent
  unfold CPS1Deformation.Source.advance
  simp only [List.map_nil,List.flatMap_nil,List.append_nil,List.nil_append]
  rw [pending,cut]
  exact ⟨rfl,rfl,rfl⟩

end
end CPS1SameEventFunction
