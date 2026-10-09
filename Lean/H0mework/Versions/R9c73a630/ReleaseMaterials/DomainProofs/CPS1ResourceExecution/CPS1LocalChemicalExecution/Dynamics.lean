import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Dictionary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace CPS1LocalChemicalExecution.Vec

/-- Constant-force midpoint displacement and momentum update pay the same work.
The mass is the supplied positive inertia, not a fixed residue mass. -/
theorem kinetic_work (mass : ℚ) (positive : 0 < mass) (r p force : Vec) (dt : ℚ) :
    let nextP := p.add (force.scale dt)
    let nextR := (r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))
    kinetic mass nextP - kinetic mass p = force.dot (nextR.sub r) := by
  have nonzero : mass ≠ 0 := ne_of_gt positive
  dsimp [kinetic,dot,add,scale,sub]
  field_simp
  ring

end CPS1LocalChemicalExecution.Vec

namespace CPS1LocalChemicalExecution.Dynamics

theorem source_drive (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat)
    (r p force : Vec) (dt mass : ℚ) (positive : 0 < mass) (forward : 0 ≤ dt)
    (compatible : chain.inertiaConsistent frame address mass = true)
    (position : chain.position frame address = some r)
    (momentum : chain.momentum frame address = some p) :
    let nextP := p.add (force.scale dt)
    let nextR := (r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))
    chain.drive? frame address force dt mass =
      some ((chain.report frame address nextR nextP).recordInertia frame address mass,
        force.dot (nextR.sub r)) := by
  have valid : ¬ (mass ≤ 0 ∨ dt < 0) := by
    rintro (badMass | badTime)
    · exact (not_le_of_gt positive) badMass
    · exact (not_lt_of_ge forward) badTime
  simp only [Chain.drive?,if_neg valid,compatible,position,momentum]
  change some (_,Vec.kinetic mass _ - Vec.kinetic mass p) = _
  rw [Vec.kinetic_work mass positive r p force dt]

theorem nonpositive_mass_cut (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat)
    (force : Vec) (dt mass : ℚ) (bad : mass ≤ 0) :
    chain.drive? frame address force dt mass = none := by
  simp only [Chain.drive?,if_pos (Or.inl bad)]

theorem backwards_time_cut (frame : CPS1Recycling.Frame) (chain : Chain frame) (address : Nat)
    (force : Vec) (dt mass : ℚ) (bad : dt < 0) :
    chain.drive? frame address force dt mass = none := by
  simp only [Chain.drive?,if_pos (Or.inr bad)]

end CPS1LocalChemicalExecution.Dynamics
