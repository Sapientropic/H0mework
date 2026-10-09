import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Continuity
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.NoGuard

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics

theorem source_joint_pulse (frame : CPS1Recycling.Frame) (state next : Joint.State frame)
    (dt : ℝ) (pulse : Body.Pulse) (computed : Joint.pulse? frame state dt = .ok (next,pulse))
    (stock surplus : CPS1EnzymeBath.Stock frame)
    (inventory : stock.Perm ([Species.joint state,.rawTime dt] ++ surplus)) :
    let result := CPS1EnzymeBath.execute frame [CPS1EnzymeBath.Reaction.pulse state dt] stock
    result.fired = [.pulse state dt] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ([.joint next,.spentPulse pulse] ++ surplus) ∧
      Joint.atoms frame next = Joint.atoms frame state ∧ Joint.bonds frame next = Joint.bonds frame state ∧
      Body.gather (Joint.particles frame next) next.rows = .ok pulse.after ∧
      Body.energy pulse.after+next.reserve = Body.energy pulse.before+state.reserve := by
  have aligned : stock.Perm ((CPS1EnzymeBath.Reaction.pulse state dt).reactants frame ++ surplus) := by
    simpa only [CPS1EnzymeBath.Reaction.reactants,computed,guards,List.append_nil] using inventory
  rcases Inventory.fire_available (CPS1EnzymeBath.Reaction.reactants frame) (CPS1EnzymeBath.Reaction.products frame)
    (.pulse state dt) surplus stock aligned with ⟨after,paid,generated⟩
  dsimp only
  simp only [CPS1EnzymeBath.execute,Inventory.execute,paid]
  have whole := Joint.pulse_whole frame state next dt pulse computed
  have energy := Joint.returned_energy frame state next dt pulse computed
  refine ⟨True.intro,True.intro,True.intro,?_,whole.1,whole.2.1,whole.2.2.2,energy.2.2.2.2.2.2.2.1⟩
  simpa only [CPS1EnzymeBath.Reaction.products,computed] using generated

end
end CPS1EnzymeBath
