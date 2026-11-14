import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions

set_option autoImplicit false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
namespace Lower.SourceFamily.Admissions.Timeline
open SourceOperationEffects

variable {S : Type u} {W X : S → Type u} [∀ target,AddCommGroup (W target)] {s : S}
local instance timelineGroups (n : Nat) (target : S) : AddCommGroup (Lower.Value W n target) :=
  Lower.groups W n target

abbrev Packet := AS.AdmissionPacket (W := W) (X := X) (s := s)

variable (factory : Factory W X s)

/-- The native receipt of the actual packet produces the next original admission. -/
def nextPacket (packet : Packet (W := W) (X := X) (s := s)) :=
  AS.bornAfterNative (AS.nativeAfterAdmission factory packet)

/-- Keep all paid admissions and compute only the missing cofinal successors. -/
def extend {paid : Nat} (history : Vector (Packet (W := W) (X := X) (s := s)) (paid+1))
    (extra : Nat) : Vector (Packet (W := W) (X := X) (s := s)) (paid+extra+1) :=
  Nat.dfold (α := fun added _ => Vector (Packet (W := W) (X := X) (s := s)) (paid+added+1)) extra
    (fun added _ retained => retained.push (nextPacket factory retained[paid+added])) history

private theorem extend_succ {paid : Nat}
    (history : Vector (Packet (W := W) (X := X) (s := s)) (paid+1)) (extra : Nat) :
    extend factory history (extra+1) =
      (extend factory history extra).push (nextPacket factory (extend factory history extra)[paid+extra]) := by
  simp only [extend,Nat.dfold_succ]

variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

local notation "source" => packetAt factory initial cfg language

theorem next_packetAt (ordinal : Nat) : nextPacket factory (source ordinal) = source (ordinal+1) :=
  (packetAt_successor factory initial cfg language ordinal).symm

theorem actual_at_extend (start : Nat) {paid : Nat}
    (history : Vector (Packet (W := W) (X := X) (s := s)) (paid+1))
    (actual : ∀ i : Fin (paid+1), history.get i = source (start+i.val))
    (extra : Nat) (i : Fin (paid+extra+1)) :
    (extend factory history extra).get i = source (start+i.val) := by
  induction extra with
  | zero => exact actual i
  | succ extra previous =>
    rw [extend_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change ((extend factory history extra).push (nextPacket factory (extend factory history extra)[paid+extra]))[paid+extra+1] =
        source (start+(paid+extra+1))
      rw [Vector.getElem_push_eq]
      have last := previous (Fin.last (paid+extra))
      change (extend factory history extra)[paid+extra] = source (start+(paid+extra)) at last
      rw [last,next_packetAt,Nat.add_assoc]
    · change ((extend factory history extra).push (nextPacket factory (extend factory history extra)[paid+extra]))[j.val] =
        source (start+j.val)
      rw [Vector.getElem_push_lt j.isLt]
      exact previous j

private def firstCell (start capacity : Nat) : Vector (Packet (W := W) (X := X) (s := s)) 1 :=
  (Vector.emptyWithCapacity capacity).push (source start)

def acquire (start extra : Nat) : Vector (Packet (W := W) (X := X) (s := s)) (extra+1) :=
  (extend factory (firstCell factory initial cfg language start (extra+1)) extra).cast
    (by rw [Nat.zero_add])

theorem acquire_at (start extra : Nat) (i : Fin (extra+1)) :
    (acquire factory initial cfg language start extra).get i = source (start+i.val) := by
  let cell := firstCell factory initial cfg language start (extra+1)
  have original : ∀ j : Fin 1, cell.get j = source (start+j.val) := by
    intro j
    rw [Fin.eq_zero j]
    rfl
  exact actual_at_extend factory initial cfg language start cell original extra
    (i.cast (by rw [Nat.zero_add]))

end Lower.SourceFamily.Admissions.Timeline
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
