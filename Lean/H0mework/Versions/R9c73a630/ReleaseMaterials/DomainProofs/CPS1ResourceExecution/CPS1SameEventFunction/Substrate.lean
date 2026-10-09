import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Body
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveNuclear.Differential

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics
open CPS1LocalChemicalExecution CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

-- This packet is a classical charged-particle restriction. The original occupied
-- field is retained in full; these ten substrate electrons are not added to C.
def ammoniaGraph : Graph.Molecule :=
  ⟨[⟨⟨0,"N"⟩,⟨"N",.N,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"H0"⟩,⟨"H0",.H,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"H1"⟩,⟨"H1",.H,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"H2"⟩,⟨"H2",.H,0,false,"N",false,false,false,false⟩⟩],
    [⟨⟨0,"N"⟩,⟨0,"H0"⟩,"SING",false,"N",.component⟩,
     ⟨⟨0,"N"⟩,⟨0,"H1"⟩,"SING",false,"N",.component⟩,
     ⟨⟨0,"N"⟩,⟨0,"H2"⟩,"SING",false,"N",.component⟩],[]⟩

def ammoniaParticles : List Charged.Particle := Charged.particles ammoniaGraph

theorem ammonia_source_complete :
    Graph.atoms ammoniaGraph .N = Chemistry.Molecule.ammonia.atoms .N ∧
    Graph.atoms ammoniaGraph .H = Chemistry.Molecule.ammonia.atoms .H ∧
    Graph.charge ammoniaGraph = Chemistry.Molecule.ammonia.charge ∧
    Charged.charge ammoniaParticles = 0 ∧ ammoniaParticles.length = 14 ∧
    (ammoniaParticles.filter (fun p => match p.address with | .nucleus _ => true | _ => false)).length = 4 ∧
    (ammoniaParticles.filter (fun p => match p.address with | .electron .. => true | _ => false)).length = 10 ∧
    Graph.dangling ammoniaGraph = [] := by decide +kernel

abbrev LiveStock (cursor : CPS1ReactiveNuclear.SourceCursor frame) :=
  CPS1ReactiveField.liveStock cursor.native.current

structure AmmoniaAt (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  slot : Fin (LiveStock cursor).length
  species : CPS1BiologicalUpdate.liveLocal? ((LiveStock cursor).get slot) = some (molecule frame .ammonia)

def AmmoniaAt.material {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : AmmoniaAt cursor) :=
  (LiveStock cursor).get source.slot

def AmmoniaAt.unspent {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : AmmoniaAt cursor) :=
  (LiveStock cursor).eraseIdx source.slot.val

def ammoniaAt? (cursor : CPS1ReactiveNuclear.SourceCursor frame) : Option (AmmoniaAt cursor) :=
  match selected : (List.finRange (LiveStock cursor).length).find?
      (fun slot => decide (CPS1BiologicalUpdate.liveLocal? ((LiveStock cursor).get slot) = some (molecule frame .ammonia))) with
  | none => none
  | some slot => some ⟨slot,of_decide_eq_true (List.find?_some (p := fun index => decide (CPS1BiologicalUpdate.liveLocal? ((LiveStock cursor).get index) = some (molecule frame .ammonia))) selected)⟩

inductive SourceFailure
  | noChain | differentChain | noAmmonia | noActiveField | retainedField
  | germ (failure : CPS1ReactiveNuclear.GermFailure)
  | substrate (failure : Body.Failure)
  deriving DecidableEq

structure SourceAt (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  active : Active frame
  actualActive : cursor.native.active = some active
  currentSource : active.source = cursor.native.current
  germ : CPS1ReactiveNuclear.Germ active.source.old active.fields
  chain : Chain frame
  chainSource : CPS1LocalChemicalExecution.Source.heldChain frame (CPS1BiologicalUpdate.liveLocal cursor.native.current) = some chain
  sameChain : chain = germ.birth.owner.currentJoint.originBody.source
  ammonia : AmmoniaAt cursor

-- Native source recognition never accepts a caller-selected germ or chain.
def sourceAt (cursor : CPS1ReactiveNuclear.SourceCursor frame) : Except SourceFailure (SourceAt cursor) := by
  classical
  exact match chainRead : CPS1LocalChemicalExecution.Source.heldChain frame (CPS1BiologicalUpdate.liveLocal cursor.native.current) with
  | none => .error .noChain
  | some chain =>
    match ammoniaAt? cursor with
    | none => .error .noAmmonia
    | some ammonia =>
      match actualActive : cursor.native.active with
      | none => .error .noActiveField
      | some active =>
        let original : Except CPS1ReactiveNuclear.GermFailure (CPS1ReactiveNuclear.Germ active.source.old active.fields) :=
          by simpa only [CPS1ReactiveNuclear.GermAt,actualActive] using cursor.germ
        match original with
        | .error cut => .error (.germ cut)
        | .ok germ =>
          if currentSource : active.source = cursor.native.current then
            if same : chain = germ.birth.owner.currentJoint.originBody.source then
              .ok ⟨active,actualActive,currentSource,germ,chain,chainRead,same,ammonia⟩
            else .error .differentChain
          else .error .retainedField

structure Raw where
  rows : List (Charged.Address × Body.Row)
  reserve : ℝ
  time : ℝ

structure Packet (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) where
  source : SourceAt cursor
  nodes : List Body.Node
  actual : Body.gather ammoniaParticles raw.rows = .ok nodes

def packet (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) : Except SourceFailure (Packet cursor raw) := do
  let source ← sourceAt cursor
  match actual : Body.gather ammoniaParticles raw.rows with
  | .error failure => .error (.substrate failure)
  | .ok nodes => .ok ⟨source,nodes,actual⟩

end
end CPS1SameEventFunction
