import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ContactJacobianStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3FactorStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PowROM
set_option autoImplicit false
namespace FlyCNS.C3ContactCurrent
open FlyCNS.C3Actuation FlyCNS.C3Sparse

def one : Float := Float.ofBits 0x3ff0000000000000
def two : Float := Float.ofBits 0x4000000000000000

structure Material where
  jacobian : FlyCNS.C3ContactJacobian.Material
  massStart : Array Nat
  massCount : Array Nat
  massColumns : Array Nat
  inverseWeight : Array Float
  solref : Array Float
  solimp : Array Float
  timestep : Float
  impedanceRatio : Float

structure Frame where
  contact : FlyCNS.C3ContactJacobian.Frame
  mass : Array Float
  contactPair : Array Nat

structure Result where
  contact : FlyCNS.C3ContactJacobian.Result
  massFactor : FlyCNS.C3Factor.Result
  diagonal : Array Float
  inverse : Array Float
  regularizer : Array Float
  kbip : Array Float
  masterFriction : Array Float
  y : Matrix
  projection : Matrix
  supernodes : Array Nat

/-- Original current impedance. Its only non-integer power is the source
libm cubic path; all source parameters are fixed by the original ROM. -/
def impedance (m : Material) (pair : Nat) (pos margin : Float) : Float × Float := Id.run do
  let lo := m.solimp[5*pair]!
  let hi := m.solimp[5*pair+1]!
  let width := m.solimp[5*pair+2]!
  if lo == hi || width <= minimum then return ((lo+hi)/two,zero)
  let signed := (pos-margin)/width
  let x := signed.abs
  if x >= one then return (hi,zero)
  if x <= zero then return (lo,zero)
  let midpoint := m.solimp[5*pair+3]!
  let sign := if signed < zero then -one else one
  let (y,derivative) := if x <= midpoint then
    let a := one/(midpoint*midpoint)
    (a*(FlyCNS.C3Pow.cubic FlyCNS.C3Pow.original x),
      (FlyCNS.C3Pow.three*a)*(x*x))
    else
      let remainder := one-x
      let b := one/((one-midpoint)*(one-midpoint))
      (fused (-b) (FlyCNS.C3Pow.cubic FlyCNS.C3Pow.original remainder) one,
        (FlyCNS.C3Pow.three*b)*(remainder*remainder))
  return (fused y (hi-lo) lo,((derivative*sign)*(hi-lo))/width)

def generateY (m : Material) (j : Matrix) (factor : Array Float) : Matrix := Id.run do
  let mut values := #[]
  let mut starts := #[]
  let mut counts := #[]
  let mut columns := #[]
  for r in [:j.rows] do
    let mut pattern := Array.replicate 74 false
    let mut dense := Array.replicate 74 zero
    for k in [j.starts[r]!:j.starts[r]!+j.counts[r]!] do
      let c := j.columns[k]!
      dense := dense.set! c j.values[k]!
      for a in [m.massStart[c]!:m.massStart[c]!+m.massCount[c]!] do
        pattern := pattern.set! m.massColumns[a]! true
    for reverse in [:74] do
      let c := 73-reverse
      if pattern[c]! && dense[c]! != zero then
        let scale := -dense[c]!
        for a in [m.massStart[c]!:m.massStart[c]!+m.massCount[c]!-1] do
          let b := m.massColumns[a]!
          if pattern[b]! then dense := dense.set! b (fused scale factor[a]! dense[b]!)
    starts := starts.push values.size
    let first := values.size
    for c in [:74] do
      if pattern[c]! then
        let diag := m.massStart[c]!+m.massCount[c]!-1
        values := values.push (dense[c]!*(one/factor[diag]!.sqrt))
        columns := columns.push c
    counts := counts.push (values.size-first)
  return ⟨j.rows,74,values,starts,counts,columns⟩

def generateProjection (y : Matrix) (r : Array Float) : Matrix := Id.run do
  let yt := transpose y
  let n := y.rows
  let mut lower := Array.replicate (n*n) zero
  let mut pattern := Array.replicate (n*n) false
  for row in [:n] do
    for k in [y.starts[row]!:y.starts[row]!+y.counts[row]!] do
      let dof := y.columns[k]!
      for a in [yt.starts[dof]!:yt.starts[dof]!+yt.counts[dof]!] do
        let col := yt.columns[a]!
        if col <= row then
          pattern := pattern.set! (row*n+col) true
          if y.values[k]! != zero then
            lower := lower.set! (row*n+col) (fused y.values[k]! yt.values[a]! lower[row*n+col]!)
    pattern := pattern.set! (row*n+row) true
    lower := lower.set! (row*n+row) (lower[row*n+row]!+r[row]!)
  let mut values := #[]
  let mut starts := #[]
  let mut counts := #[]
  let mut columns := #[]
  for row in [:n] do
    starts := starts.push values.size
    let first := values.size
    for col in [:n] do
      let index := if col <= row then row*n+col else col*n+row
      if pattern[index]! then
        values := values.push lower[index]!
        columns := columns.push col
    counts := counts.push (values.size-first)
  return ⟨n,n,values,starts,counts,columns⟩

/-- Complete generated J/KBIP/R/D/Y/AR of this registered contact current. -/
def generate (m : Material) (f : Frame) : Result := Id.run do
  let j := FlyCNS.C3ContactJacobian.generate m.jacobian f.contact
  let factor := FlyCNS.C3Factor.factor ⟨f.mass,m.massStart,m.massCount,m.massColumns⟩
  let mut diag := #[]
  let mut inverse := #[]
  let mut regularizer := #[]
  let mut kbip := #[]
  let mut master := Array.replicate f.contact.geomFirst.size zero
  for c in [:f.contact.geomFirst.size] do
    if j.contactAddress[c]! < 0 then continue
    let pair := f.contactPair[c]!
    let (imp,derivative) := impedance m pair f.contact.distance[c]! f.contact.margin[c]!
    let bodyFirst := m.jacobian.geomBody[f.contact.geomFirst[c]!]!
    let bodySecond := m.jacobian.geomBody[f.contact.geomSecond[c]!]!
    let tran := fused m.inverseWeight[2*bodySecond]! one (m.inverseWeight[2*bodyFirst]!*one)
    let friction := f.contact.friction[5*c]!
    let approx := fused (friction*friction) tran tran
    let baseR := max minimum (((one-imp)*approx)/imp)
    let r1 := baseR/(max minimum m.impedanceRatio)
    let mu := friction*(r1/baseR).sqrt
    master := master.set! c mu
    let r := ((two*mu)*mu)*baseR
    let ref0 := max m.solref[2*pair]! (two*m.timestep)
    let ref1 := m.solref[2*pair+1]!
    let width := m.solimp[5*pair+1]!
    let stiffness := one/(max minimum (((((width*width)*ref0)*ref0)*ref1)*ref1))
    let damping := two/(max minimum (width*ref0))
    for _ in [:4] do
      regularizer := regularizer.push r
      inverse := inverse.push (one/r)
      diag := diag.push ((r*imp)/(one-imp))
      kbip := kbip ++ #[stiffness,damping,imp,derivative]
  let y := generateY m j.jacobian factor.factor
  let projection := generateProjection y regularizer
  let mut supernodes := Array.replicate j.jacobian.rows 0
  for back in [:j.jacobian.rows-1] do
    let row := j.jacobian.rows-back-2
    let left := j.jacobian.columns.extract j.jacobian.starts[row]! (j.jacobian.starts[row]!+j.jacobian.counts[row]!)
    let right := j.jacobian.columns.extract j.jacobian.starts[row+1]! (j.jacobian.starts[row+1]!+j.jacobian.counts[row+1]!)
    if left == right then supernodes := supernodes.set! row (supernodes[row+1]!+1)
  return ⟨j,factor,diag,inverse,regularizer,kbip,master,y,projection,supernodes⟩
end FlyCNS.C3ContactCurrent
