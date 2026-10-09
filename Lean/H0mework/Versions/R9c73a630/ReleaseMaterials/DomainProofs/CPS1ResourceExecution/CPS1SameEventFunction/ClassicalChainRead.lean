import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Substrate

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1LocalChemicalExecution
variable {frame : CPS1Recycling.Frame}

def localChain? : Species frame → Option (Chain frame)
  | .chain chain => some chain | _ => none

def atomizedChain? : CPS1AtomicSource.Current.Species frame → Option (Chain frame)
  | .retained localSpecies => localChain? localSpecies
  | .atomic chain => some chain
  | _ => none

def atomicChain? : CPS1AtomicDynamics.Species frame → Option (Chain frame)
  | .retained atomized => atomizedChain? atomized
  | .body body => some body.source
  | _ => none

def bathChain? : CPS1EnzymeBath.Species frame → Option (Chain frame)
  | .retained atomic => atomicChain? atomic
  | .joint joint => some joint.originBody.source
  | _ => none

def electronicChain? : CPS1ElectronicSource.Species frame → Option (Chain frame)
  | .retained bath => bathChain? bath
  | .quantum quantum => some quantum.geometry.originJoint.originBody.source
  | _ => none

def nuclearChain? : CPS1QuantumNuclear.Species frame → Option (Chain frame)
  | .retained electronic => electronicChain? electronic
  | _ => none

def followingChain? : CPS1Following.Species frame → Option (Chain frame)
  | .retained nuclear => nuclearChain? nuclear
  | .following following => some following.geometry.originJoint.originBody.source
  | _ => none

def molecularChain? : CPS1MolecularFrame.Species frame → Option (Chain frame)
  | .retained following => followingChain? following
  | .molecular molecular => some molecular.reference.geometry.originJoint.originBody.source
  | _ => none

def deformedChain? : CPS1Deformation.Species frame → Option (Chain frame)
  | .retained molecular => molecularChain? molecular
  | .deformed deformed => some deformed.reference.geometry.originJoint.originBody.source
  | _ => none

-- Only currently owned material is read. Spent receipts and upstream previous
-- stocks do not supply a live chain or a replacement occurrence.
def liveChain? : CPS1ReactiveField.LiveMaterial frame → Option (Chain frame)
  | .old deformed => deformedChain? deformed
  | .reactive (.inherited localSpecies) => localChain? localSpecies
  | _ => none

def readChain (cursor : CPS1ReactiveNuclear.SourceCursor frame) : Option (Chain frame) :=
  ((LiveStock cursor).filterMap liveChain?).head?

end
end CPS1SameEventFunction.Classical
