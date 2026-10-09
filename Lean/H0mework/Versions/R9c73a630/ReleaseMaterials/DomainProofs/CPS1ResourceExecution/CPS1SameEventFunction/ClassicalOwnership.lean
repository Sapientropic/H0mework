import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalChainRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Unique

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics CPS1LocalChemicalExecution
variable {frame : CPS1Recycling.Frame}

structure OwnedChain (frame : CPS1Recycling.Frame) where
  chain : Chain frame
  rows : List (Charged.Address × Body.Row)

-- Atomic/body/joint constructors are currently owned paid graph carriers.
-- A local chain alone has not paid the CCD protonation/atomization operation.
def ownedAtomic? : CPS1AtomicSource.Current.Species frame → Option (OwnedChain frame)
  | .atomic chain => some ⟨chain,[]⟩ | _ => none

def ownedBody? : CPS1AtomicDynamics.Species frame → Option (OwnedChain frame)
  | .retained atomized => ownedAtomic? atomized
  | .body body => some ⟨body.source,body.rows⟩
  | _ => none

def ownedBath? : CPS1EnzymeBath.Species frame → Option (OwnedChain frame)
  | .retained atomic => ownedBody? atomic
  | .joint joint => some ⟨joint.originBody.source,joint.rows⟩
  | _ => none

def ownedElectronic? : CPS1ElectronicSource.Species frame → Option (OwnedChain frame)
  | .retained bath => ownedBath? bath
  | .quantum quantum => some ⟨quantum.geometry.originJoint.originBody.source,quantum.geometry.originJoint.rows⟩
  | _ => none

def ownedNuclear? : CPS1QuantumNuclear.Species frame → Option (OwnedChain frame)
  | .retained electronic => ownedElectronic? electronic
  | _ => none

def ownedFollowing? : CPS1Following.Species frame → Option (OwnedChain frame)
  | .retained nuclear => ownedNuclear? nuclear
  | .following following => some ⟨following.geometry.originJoint.originBody.source,following.geometry.originJoint.rows⟩
  | _ => none

def ownedMolecular? : CPS1MolecularFrame.Species frame → Option (OwnedChain frame)
  | .retained following => ownedFollowing? following
  | .molecular molecular => some ⟨molecular.currentJoint.originBody.source,molecular.currentJoint.rows⟩
  | _ => none

def ownedDeformed? : CPS1Deformation.Species frame → Option (OwnedChain frame)
  | .retained molecular => ownedMolecular? molecular
  | .deformed deformed => some ⟨deformed.currentJoint.originBody.source,deformed.currentJoint.rows⟩
  | _ => none

def ownedLive? : CPS1ReactiveField.LiveMaterial frame → Option (OwnedChain frame)
  | .old material => ownedDeformed? material
  | _ => none

def ownedChain (cursor : CPS1ReactiveNuclear.SourceCursor frame) : Option (OwnedChain frame) :=
  ((LiveStock cursor).filterMap ownedLive?).head?

-- Only source chain slots are reused. Bath slots remain in the complete old
-- cursor and never get reinterpreted as the newly allocated NH3 slots.
def OwnedChain.chainRows (owned : OwnedChain frame) : List (Charged.Address × Body.Row) :=
  owned.rows.filter (fun entry => entry.1.slot < (CPS1AtomicSource.Graph.fromChain frame owned.chain).atoms.length)

def rowCompatible (known : List (Charged.Address × Body.Row))
    (raw : List (Charged.Address × Body.Row)) : Except Body.Failure Unit :=
  match known.find? (fun entry =>
    match Body.row? raw entry.1 with | none => false | some row => decide (row ≠ entry.2)) with
  | none => .ok ()
  | some entry => .error (.conflictingRow entry.1)

end
end CPS1SameEventFunction.Classical
