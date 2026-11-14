import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BodyKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PhysicalMaterial
set_option autoImplicit false
namespace FlyCNS.C3Body
open FlyCNS.C3Physical
def wide (p : System.FilePath) : IO (Array Int64) := do
  let w : FlyCNS.C3Integer.Word := ⟨8,← IO.FS.readBinFile p⟩
  return (List.range (FlyCNS.C3Integer.count w)).toArray.map fun i => w.int i
def writeWide (p : System.FilePath) (values : Array Int64) : IO Unit := do
  let mut bytes := ByteArray.empty
  for v in values do
    for b in [:8] do bytes := bytes.push ((v.toUInt64 >>> UInt64.ofNat (8*b)).toUInt8)
  IO.FS.writeBinFile p bytes
def writeIndices (p : System.FilePath) (values : Array Nat) : IO Unit := do
  let mut bytes := ByteArray.empty
  for v in values do
    for b in [:4] do bytes := bytes.push ((UInt32.ofNat v >>> UInt32.ofNat (8*b)).toUInt8)
  IO.FS.writeBinFile p bytes
def material (root : System.FilePath) : IO Material := do
  let physics ← FlyCNS.C3Physical.readMaterial (root/"physical")
  let sp := root/"signal"
  let law ← floats (sp/"law.bin");let shared ← indices (sp/"shared.bin")
  let populations ← (List.range 9).toArray.mapM fun i => indices (sp/("population-"++toString i++".bin"))
  let signal : FlyCNS.C3BodySignal.Material := ⟨populations,law[0]!,law[1]!,law[2]!,law[3]!,law[4]!,law[5]!,law[6]!,law[7]!,law[8]!,shared[0]! != 0⟩
  let op := root/"observation";let ports ← indices (op/"ports.bin");let detector ← integers (op/"detector.bin")
  let observation : FlyCNS.C3Observation.Material := ⟨ports[0]!,ports.extract 2 8,detector.map Int64.ofInt,ports[1]!⟩
  let gp := root/"gait";let glaw ← floats (gp/"law.bin");let ilaw ← integers (gp/"integer-law.bin")
  let splines ← (List.range 6).toArray.mapM fun i => do
    let p := gp/toString i
    return FlyCNS.C3Gait.Spline.mk (← floats (p/"knots.bin")) (← floats (p/"coefficients.bin")) (← floats (p/"neutral.bin"))
  let cpg : FlyCNS.C3CPG.Material := ⟨glaw[0]!,← floats (gp/"weights.bin"),← floats (gp/"biases.bin"),← floats (gp/"convergence.bin")⟩
  let gait : FlyCNS.C3Gait.Material := ⟨cpg,splines,← floats (gp/"swing.bin"),← floats (gp/"base-frequencies.bin"),
    ← floats (gp/"correction-vectors.bin"),← indices (gp/"output-order.bin"),glaw[1]!,glaw.extract 2 4,glaw[4]!,glaw.extract 5 7,
    glaw[7]!,glaw[8]!,Int64.ofInt ilaw[0]!,glaw[9]!,ilaw[1]! != 0⟩
  let rp := root/"resource";let rlaw ← floats (rp/"scalars.bin")
  let resource : FlyCNS.C3Resource.Material := ⟨rlaw[0]!,rlaw[1]!,rlaw[2]!,rlaw[3]!,rlaw[4]!,rlaw[5]!,rlaw[6]!,rlaw[7]!,rlaw[8]!,
    #[← floats (rp/"patch_positions.bin")],← floats (rp/"patch_radii.bin")⟩
  let fp := root/"feedback";let sigma ← floats (fp/"odor-sigma.bin");let pos ← floats (fp/"odor-positions.bin")
  let strengths ← floats (fp/"odor-strengths.bin")
  let odor : FlyCNS.C3Odor.Material := ⟨(List.range sigma.size).toArray.map (fun i => pos.extract (3*i) (3*i+3)),sigma,
    (List.range sigma.size).toArray.map fun i => strengths.extract (2*i) (2*i+2)⟩
  let population ← (List.range 8).toArray.mapM fun i => indices (fp/("population-"++toString i++".bin"))
  let signs ← integers (fp/"signs.bin");let flaw ← floats (fp/"law.bin")
  let feedback : FlyCNS.C3Feedback.Material := ⟨odor,population,← indices (fp/"inner-sugar.bin"),← indices (fp/"inner-water.bin"),
    ← indices (fp/"targets.bin"),← indices (fp/"ligand.bin"),signs.map Int64.ofInt,flaw[0]!,flaw[1]!⟩
  let bodyports ← indices (root/"body-ports.bin");let pitch ← floats (root/"pitch.bin")
  return ⟨physics,signal,observation,gait,resource,feedback,← indices (root/"legs.bin"),← indices (root/"mouths.bin"),
    ← indices (root/"adhesion.bin"),← floats (root/"neutral.bin"),pitch[0]!,bodyports[0]!,bodyports[1]!,bodyports.extract 2 4⟩
end FlyCNS.C3Body
