import H0mework.Versions.AB.Chemistry.LAlanineRefinementGeometry.Source

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry.Accounts

open Lean Elab Term Command Tactic Data
open scoped BigOperators
noncomputable section

def domainAccount (r : RunIndex) (d : Slab) : Prop :=
  let row := Source.domain r d
  row.rows = 1024 ∧ row.counts.size = 20 ∧ row.bucketPoint.size = 20 ∧
  row.point.size = 8 ∧ row.floating.size = 8 ∧ row.rounding.size = 8 ∧
  (∀ b : Bucket, row.bucketPoint[b.val]!.size = 8) ∧
  (∑ b : Bucket, row.counts[b.val]!) = row.rows ∧
  (∀ f : Field, (∑ b : Bucket, (row.bucketPoint[b.val]!)[f.val]!) = row.point[f.val]!) ∧
  (∀ f : Field, row.point[f.val]! = row.floating[f.val]! + row.rounding[f.val]!) ∧
  0 < row.measure ∧ 0 < row.sampledJacobianLower ∧ row.disagreements = 0 ∧ row.wholeLabel = none

def faceAccount (r : RunIndex) (f : Face) : Prop :=
  let row := Source.face r f
  row.segment = f.val / 6 ∧ row.axis = (f.val / 2) % 3 ∧ row.side = f.val % 2 ∧
  row.counts.size = 20 ∧ (∑ b : Bucket, row.counts[b.val]!) = row.rows ∧
  row.point = row.floating + row.rounding ∧ |row.floating| ≤ row.absoluteFluxUpper ∧
  0 ≤ row.sampledNormalUpper ∧ row.disagreements = 0

def seamAccount (r : RunIndex) (s : Seam) : Prop :=
  let row := Source.seam r s
  row.knot = s.val + 1 ∧ row.leftFace = 6 * s.val + 3 ∧ row.rightFace = 6 * s.val + 8 ∧
  row.pointSum = ((Source.run r).faces[row.leftFace]!).point + ((Source.run r).faces[row.rightFace]!).point ∧
  row.floatSum = ((Source.run r).faces[row.leftFace]!).floating + ((Source.run r).faces[row.rightFace]!).floating ∧
  row.pointSum = 0 ∧ row.floatSum = 0

instance (r : RunIndex) (d : Slab) : Decidable (domainAccount r d) := by
  unfold domainAccount
  infer_instance

instance (r : RunIndex) (f : Face) : Decidable (faceAccount r f) := by
  unfold faceAccount
  infer_instance

instance (r : RunIndex) (s : Seam) : Decidable (seamAccount r s) := by
  unfold seamAccount
  infer_instance

def outerFace (row : FaceReceipt) : Bool :=
  row.axis == 1 && ((row.segment == 0 && row.side == 0) || (row.segment == 7 && row.side == 1))

def runAccount (r : RunIndex) : Prop :=
  let row := Source.run r
  let a := row.account
  row.domains.size = 4 ∧ row.faces.size = 48 ∧ row.seams.size = 7 ∧
  (∀ d : Slab, domainAccount r d) ∧ (∀ f : Face, faceAccount r f) ∧ (∀ s : Seam, seamAccount r s) ∧
  (∀ f : Field,
    ((∑ d : Fin 3, (row.domains[d.val]!).point[f.val]!) - (Source.domain r 3).point[f.val]!) = a.pointSlabResidual[f.val]! ∧
    ((∑ d : Fin 3, (row.domains[d.val]!).floating[f.val]!) - (Source.domain r 3).floating[f.val]!) = a.floatSlabResidual[f.val]!) ∧
  a.pointBoundary = (∑ f : Face, (Source.face r f).point) ∧
  a.floatBoundary = (∑ f : Face, (Source.face r f).floating) ∧
  a.boundaryRounding = (∑ f : Face, (Source.face r f).rounding) ∧
  a.pointBoundary = a.floatBoundary + a.boundaryRounding ∧
  a.laplacianZepto = 1000000000 * (Source.domain r 1).floating[3]! + a.picoResolutionResidual ∧
  a.laplacianZepto = a.floatBoundary + a.divergenceResidual ∧
  a.capPoint = (∑ f : Face, if (Source.face r f).axis = 2 then (Source.face r f).point else 0) ∧
  a.sidePoint = (∑ f : Face, if (Source.face r f).axis = 0 then (Source.face r f).point else 0) ∧
  a.seamPoint = (∑ s : Seam, (Source.seam r s).pointSum) ∧
  a.outerPoint = (∑ f : Face, if outerFace (Source.face r f) then (Source.face r f).point else 0) ∧
  a.pointBoundary = a.capPoint + a.sidePoint + a.seamPoint + a.outerPoint ∧
  (∀ b : Bucket,
    row.lowerCounts[b.val]! = (∑ f : Face, if (Source.face r f).axis = 0 ∧ (Source.face r f).side = 0 then
      (Source.face r f).counts[b.val]! else 0) ∧
    row.upperCounts[b.val]! = (∑ f : Face, if (Source.face r f).axis = 0 ∧ (Source.face r f).side = 1 then
      (Source.face r f).counts[b.val]! else 0)) ∧
  (∀ f : Face, (Source.face r f).axis = 0 → (Source.face r f).sampledNormalUpper ≤ row.sampledNormalUpper) ∧
  row.sampledAbsoluteFluxUpper = (∑ f : Face, if (Source.face r f).axis = 0 then (Source.face r f).absoluteFluxUpper else 0)

elab "proveCurvedRunAccounts" : command => liftTermElabM do
  for i in [:5] do
    let inside ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 5))
    let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit 5) (mkNatLit i) inside
    let type := mkApp (mkConst ``runAccount) index
    let expanded := (← getConstInfo ``runAccount).value!.bindingBody!.instantiate1 index
    let value ← instantiateMVars (← Meta.mkDecideProof expanded)
    addDecl (.thmDecl { name := (← getCurrNamespace) ++ Name.mkSimple s!"run{i}", levelParams := [], type, value })

proveCurvedRunAccounts

theorem everyRun (r : RunIndex) : runAccount r := by
  fin_cases r
  · exact run0
  · exact run1
  · exact run2
  · exact run3
  · exact run4

end
end LAlanine40K2025.BasinRefinement.Geometry.Accounts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
