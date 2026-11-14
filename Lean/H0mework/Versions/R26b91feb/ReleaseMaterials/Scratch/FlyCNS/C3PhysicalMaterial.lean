import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PhysicalKernel
set_option autoImplicit false
namespace FlyCNS.C3Physical
def floats (p : System.FilePath) : IO (Array Float) := do
  let w : FlyCNS.C3Integer.Word := ⟨8,← IO.FS.readBinFile p⟩
  return (List.range (FlyCNS.C3Integer.count w)).toArray.map fun i => Float.ofBits (w.bits i)
def integers (p : System.FilePath) : IO (Array Int) := do
  let w : FlyCNS.C3Integer.Word := ⟨4,← IO.FS.readBinFile p⟩
  return (List.range (FlyCNS.C3Integer.count w)).toArray.map fun i => (w.int i).toInt
def indices (p : System.FilePath) : IO (Array Nat) := do return (← integers p).map Int.toNat
def flags (p : System.FilePath) : IO (Array Bool) := do return (← IO.FS.readBinFile p).data.map fun b => b != 0
def writeFloats (p : System.FilePath) (values : Array Float) : IO Unit := do
  let mut bytes := ByteArray.empty
  for value in values do
    for b in [:8] do bytes := bytes.push ((value.toBits >>> UInt64.ofNat (8*b)).toUInt8)
  IO.FS.writeBinFile p bytes
def readMaterial (root : System.FilePath) : IO Material := do
  let kp := root/"kinematics-material"
  let k : FlyCNS.C3Kinematics.Material := ⟨← indices (kp/"body_parentid.bin"),← indices (kp/"body_jntadr.bin"),
    ← indices (kp/"body_jntnum.bin"),← floats (kp/"body_pos.bin"),← floats (kp/"body_quat.bin"),
    ← floats (kp/"body_ipos.bin"),← floats (kp/"body_iquat.bin"),← indices (kp/"body_sameframe.bin"),
    ← indices (kp/"jnt_type.bin"),← indices (kp/"jnt_qposadr.bin"),← floats (kp/"jnt_pos.bin"),
    ← floats (kp/"jnt_axis.bin"),← floats (kp/"qpos0.bin"),← indices (kp/"geom_bodyid.bin"),
    ← floats (kp/"geom_pos.bin"),← floats (kp/"geom_quat.bin"),← indices (kp/"geom_sameframe.bin"),
    ← indices (kp/"site_bodyid.bin"),← floats (kp/"site_pos.bin"),← floats (kp/"site_quat.bin"),← indices (kp/"site_sameframe.bin")⟩
  let ip := root/"inertia-material"
  let inertia : FlyCNS.C3Inertia.Material := ⟨← indices (ip/"body_parentid.bin"),← indices (ip/"body_rootid.bin"),
    ← indices (ip/"body_jntadr.bin"),← indices (ip/"body_jntnum.bin"),← indices (ip/"jnt_type.bin"),
    ← indices (ip/"jnt_dofadr.bin"),← floats (ip/"body_mass.bin"),← floats (ip/"body_subtreemass.bin"),
    ← floats (ip/"body_inertia.bin"),← indices (ip/"dof_bodyid.bin"),← integers (ip/"dof_parentid.bin"),
    ← floats (ip/"dof_armature.bin"),← indices (ip/"M_rowadr.bin"),← indices (ip/"M_rownnz.bin"),← indices (ip/"mapM2M.bin")⟩
  let cp := root/"contact-material"
  let collision : FlyCNS.C3PlaneMesh.Material := ⟨← indices (cp/"geom_dataid.bin"),← indices (cp/"mesh_vertadr.bin"),
    ← indices (cp/"mesh_vertnum.bin"),← integers (cp/"mesh_graphadr.bin"),← integers (cp/"mesh_graph.bin"),
    ← floats (cp/"mesh_vert.bin"),← floats (cp/"geom_rbound.bin"),← indices (cp/"pair_geom1.bin"),
    ← indices (cp/"pair_geom2.bin"),← floats (cp/"pair_margin.bin")⟩
  let jp := root/"contact-current-material"
  let jacobian : FlyCNS.C3ContactJacobian.Material := ⟨← indices (jp/"geom_bodyid.bin"),← indices (jp/"body_weldid.bin"),
    ← indices (jp/"body_rootid.bin"),← integers (jp/"body_dofadr.bin"),← indices (jp/"body_dofnum.bin"),← integers (jp/"dof_parentid.bin")⟩
  let options ← floats (jp/"options.bin")
  let contact : FlyCNS.C3ContactCurrent.Material := ⟨jacobian,← indices (jp/"M_rowadr.bin"),← indices (jp/"M_rownnz.bin"),
    ← indices (jp/"M_colind.bin"),← floats (jp/"body_invweight0.bin"),← floats (jp/"pair_solref.bin"),
    ← floats (jp/"pair_solimp.bin"),options[0]!,options[1]!⟩
  let types ← indices (jp/"actuator_trntype.bin");let ids ← indices (jp/"actuator_trnid.bin")
  let transmission : FlyCNS.C3Transmission.Material := ⟨contact,types,(List.range types.size).toArray.map fun i => ids[2*i]!,
    ← floats (jp/"actuator_gear.bin"),← indices (jp/"jnt_qposadr.bin"),← indices (jp/"jnt_dofadr.bin")⟩
  let island : FlyCNS.C3Island.Material := ⟨transmission,(← integers (jp/"body_treeid.bin")).map Int64.ofInt,← indices (jp/"dof_treeid.bin")⟩
  let vp := root/"velocity-material"
  let velocity : FlyCNS.C3Velocity.Material := ⟨← indices (vp/"body_parentid.bin"),← indices (vp/"body_dofadr.bin"),
    ← indices (vp/"body_dofnum.bin"),← indices (vp/"dof_jntid.bin"),← indices (vp/"dof_bodyid.bin"),
    ← indices (vp/"jnt_type.bin"),← indices (vp/"jnt_qposadr.bin"),← indices (vp/"jnt_dofadr.bin"),
    ← floats (vp/"jnt_stiffness.bin"),← floats (vp/"qpos_spring.bin"),← floats (vp/"dof_damping.bin"),← floats (vp/"gravity.bin")⟩
  let ap := root/"material"
  let actuation : FlyCNS.C3Actuation.Material := ⟨← floats (ap/"gain.bin"),← floats (ap/"bias0.bin"),← floats (ap/"bias1.bin"),
    ← floats (ap/"bias2.bin"),← flags (ap/"affine.bin"),← flags (ap/"ctrl_limited.bin"),
    ← floats (ap/"ctrl_low.bin"),← floats (ap/"ctrl_high.bin"),← flags (ap/"force_limited.bin"),
    ← floats (ap/"force_low.bin"),← floats (ap/"force_high.bin"),74⟩
  let np := root/"constraint-material"
  let scalar ← floats (np/"scalars.bin");let ints ← indices (np/"integers.bin")
  let constraint : FlyCNS.C3Constraint.Material := ⟨ints[0]!,scalar[0]!,ints[1]!,scalar[1]!,ints[2]!,scalar[2]!,scalar[3]!⟩
  let ep := root/"euler-material";let dt ← floats (ep/"timestep.bin")
  let euler : FlyCNS.C3Euler.Material := ⟨dt[0]!,← floats (ep/"damping.bin")⟩
  let pp := root/"position-material"
  let position : FlyCNS.C3Position.Material := ⟨dt[0]!,← indices (pp/"joint_types.bin"),← indices (pp/"position_address.bin"),← indices (pp/"velocity_address.bin")⟩
  let dp := root/"diagnostics"
  let diagnostics : FlyCNS.C3Diagnostics.Material := ⟨← floats (dp/"body_mass.bin"),← floats (dp/"gravity.bin"),
    ← floats (dp/"jnt_stiffness.bin"),← indices (dp/"jnt_qposadr.bin"),← floats (dp/"qpos_spring.bin"),
    ← indices (dp/"M_rowadr.bin"),← indices (dp/"M_rownnz.bin"),← indices (dp/"M_colind.bin"),← floats (dp/"qpos0.bin")⟩
  return ⟨k,inertia,collision,island,velocity,actuation,constraint,euler,position,diagnostics,← floats (root/"pair-friction.bin")⟩

end FlyCNS.C3Physical
