import H0mework.Fock.CopyGraph.TimeModelCycle

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale)
open SourceGeneratedActionObservationHistory (PrefixCarrier prefixEvaluator dropFirst)
noncomputable section

abbrev Packet (depth : Nat) (index : Index depth) := PrefixCarrier SourceJointClockGraph.Carrier index.val

def phases (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier →ₗ[ℂ] Packet depth index :=
  prefixEvaluator SourceJointClockGraph.action.toLinearMap (SourceCopyGraph.recover depth index).toLinearMap index.val

def extend (depth : Nat) (index : Index depth) : Packet depth index →ₗ[ℂ] PrefixCarrier SourceJointClockGraph.Carrier (index.val + 1) :=
  LinearMap.pi fun phase => Fin.lastCases
    (SourceJointClockGraph.action.toLinearMap.comp (LinearMap.proj (0 : Fin (index.val + 1))))
    (fun earlier => LinearMap.proj earlier) phase

def next (depth : Nat) (index : Index depth) : Packet depth index →ₗ[ℂ] Packet depth index :=
  (dropFirst index.val).comp (extend depth index)

theorem phase_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) :
    phases depth index value phase = SourceCopyGraph.recover depth index (time phase.val value) := by
  change SourceCopyGraph.recover depth index ((SourceJointClockGraph.action.toLinearMap ^ phase.val) value) = _
  rw [← ContinuousLinearMap.toLinearMap_pow]
  rfl

theorem extend_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    extend depth index (phases depth index value) =
      prefixEvaluator SourceJointClockGraph.action.toLinearMap (SourceCopyGraph.recover depth index).toLinearMap (index.val + 1) value := by
  funext phase
  refine Fin.lastCases ?_ (fun earlier => ?_) phase
  · simp only [extend, LinearMap.pi_apply, Fin.lastCases_last, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [phase_source]
    change SourceJointClockGraph.action (SourceCopyGraph.recover depth index value) =
      SourceCopyGraph.recover depth index ((SourceJointClockGraph.action.toLinearMap ^ (index.val + 1)) value)
    rw [← ContinuousLinearMap.toLinearMap_pow, ← SourceCopyProgram.scale_source depth index]
    exact (recover_cycle depth index value).symm
  · simp only [extend, LinearMap.pi_apply, Fin.lastCases_castSucc, LinearMap.proj_apply]
    rfl

theorem next_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    next depth index (phases depth index value) = phases depth index (SourceJointClockGraph.action value) := by
  change dropFirst (R := ℂ) index.val (extend depth index (phases depth index value)) = _
  rw [extend_source]
  exact LinearMap.congr_fun (SourceGeneratedActionObservationHistory.dropFirst_evaluator
    SourceJointClockGraph.action.toLinearMap (SourceCopyGraph.recover depth index).toLinearMap index.val) value

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
