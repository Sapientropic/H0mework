import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ClockProducer
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3WriterStep
set_option autoImplicit false
namespace FlyCNS.C3Clock

inductive ScalarKind where
  | signed | unsigned | object
  deriving DecidableEq
def scalarKind (value : Nat) : ScalarKind :=
  if value<2^63 then .signed else if value<2^64 then .unsigned else .object
structure SavedCounter where
  value : Nat
  kind : ScalarKind
  bytes : ByteArray
def serialize (value : Nat) : Except String SavedCounter :=
  if value<2^64 then
    let kind := scalarKind value
    let dtype := if value<2^63 then "<i8" else "<u8"
    .ok ⟨value,kind,FlyCNS.C3Writer.npy dtype #[] (FlyCNS.C3Writer.little value 8)⟩
  else .error "an installed coordinate contains an object reference"

structure AdmittedCounter where
  value : Fin (2^63)
  bytes : ByteArray
def admitCounter (value : Nat) : Except String AdmittedCounter :=
  if bound : value<2^63 then
    .ok ⟨⟨value,bound⟩,FlyCNS.C3Writer.npy "<i8" #[] (FlyCNS.C3Writer.little value 8)⟩
  else .error "field interpretation changed: body.physics_ticks"

theorem admitted_kind {value : Nat} {admitted : AdmittedCounter}
    (accepted : admitCounter value=.ok admitted) : scalarKind value=.signed := by
  unfold admitCounter at accepted
  split at accepted
  next h => simp [scalarKind,h]
  next h => contradiction
theorem admitted_bounded {value : Nat} {admitted : AdmittedCounter}
    (accepted : admitCounter value=.ok admitted) : value≤signedLimit := by
  unfold admitCounter at accepted
  split at accepted
  next h => unfold signedLimit;omega
  next h => contradiction

def admitGenerated (visit : Nat) : Except String AdmittedCounter :=
  admitCounter (generate visit).physics
theorem generated_successful_visit_bound {visit : Nat} {admitted : AdmittedCounter}
    (accepted : admitGenerated visit=.ok admitted) : visit≤signedLimit/1000+2 := by
  have bound := admitted_bounded accepted
  exact successful_visit_bound visit (by simpa [successfulSave] using bound)

def generatedFiniteVisit (visit : Nat) (admitted : AdmittedCounter)
    (accepted : admitGenerated visit=.ok admitted) : Fin (signedLimit/1000+3) :=
  ⟨visit,by have bound := generated_successful_visit_bound accepted;omega⟩

end FlyCNS.C3Clock
