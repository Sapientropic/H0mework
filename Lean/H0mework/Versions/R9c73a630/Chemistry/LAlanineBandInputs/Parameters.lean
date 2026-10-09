import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCache.SaturationCell2

/-! Original Gaussian centres and exponents, shared before rectangle arithmetic. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs

open SourceGaussianModel SourceSignedEvaluator SourceRectangle WholeBandSource WholeBandSaturation
open Lean Elab Term Command Inertia.SourceParsing

elab "generateOriginalInputParameters" : command => liftTermElabM do
  let packet ← parse SourceFiniteData.sourceText
  let gaussian ← field packet "gaussian_source"
  let centres ← (← decode (Array (Array Json)) (← field gaussian "centres")).mapM fun row =>
    row.mapM WholeCellSource.sourceRational
  unless centres.size == 13 && centres.all (·.size == 3) do throwError "original centre census"
  let terms ← decode (Array (Array Json)) (← field gaussian "terms")
  let some (.defnInfo info) := (← getEnv).find? ``SourceRectangle.rawGroups |
    throwError "original groups missing"
  unless info.safety == .safe do throwError "unsafe original group source"
  let some rows ← Meta.getArrayLit? info.value | throwError "literal original groups"
  unless rows.size == 94 do throwError "original group census"
  let mut atoms : Array Nat := #[]
  let mut exponents : Array (Int × Nat) := #[]
  for row in rows do
    unless row.isAppOfArity ``SourceRectangle.GroupData.mk 4 do throwError "source group shape"
    let some members ← Meta.getArrayLit? row.getAppArgs[3]! | throwError "source member literals"
    unless members.size > 0 do throwError "source group representative"
    let member := members[0]!
    unless member.isAppOfArity ``Prod.mk 4 do throwError "source member address"
    let some b ← Meta.getNatValue? member.getAppArgs[2]! | throwError "source basis address"
    let some t ← Meta.getNatValue? member.getAppArgs[3]! | throwError "source term address"
    unless b < terms.size && t < terms[b]!.size do throwError "source term range"
    let term := (terms[b]!)[t]!
    let atomIndex ← decode Nat (← field term "atom")
    unless atomIndex < 13 do throwError "source atom range"
    atoms := atoms.push atomIndex
    exponents := exponents.push (← WholeCellSource.sourceRational (← field term "exponent"))
  WholeCellSource.declareSource `rawCentres (toExpr centres)
  WholeCellSource.declareSource `rawAtoms (toExpr atoms)
  WholeCellSource.declareSource `rawExponents (toExpr exponents)

generateOriginalInputParameters

abbrev Atom := Fin 13
noncomputable def atomCentre (a : Atom) (axis : Fin 3) : ℚ :=
  SourceFiniteData.ratRead ((rawCentres[a.val]!)[axis.val]!)
noncomputable def groupAtom (g : Group) : Atom :=
  ⟨rawAtoms[g.val]! % 13, Nat.mod_lt _ (by decide)⟩
noncomputable def groupAlpha (g : Group) : ℚ := SourceFiniteData.ratRead rawExponents[g.val]!

theorem original_group_parameters (g : Group) :
    (groupTerm g).exponent = groupAlpha g ∧
    (groupTerm g).centre = atomCentre (groupAtom g) := by
  fin_cases g <;> exact ⟨rfl, rfl⟩

def squaredRadius (box : Rectangle) (centre : Fin 3 → ℚ) : Pair :=
  add (add (add (point 0) (square (sub (box 0) (point (centre 0)))))
    (square (sub (box 1) (point (centre 1)))))
    (square (sub (box 2) (point (centre 2))))

noncomputable def sharedRadial (radii : Atom → Pair) (g : Group) : Pair :=
  mul (neg (point (groupAlpha g))) (radii (groupAtom g))

theorem radialPair_shared (box : Rectangle) (g : Group) :
    radialPair (groupTerm g) box =
      sharedRadial (fun a => squaredRadius box (atomCentre a)) g := by
  simp only [radialPair, relative, sharedRadial, squaredRadius,
    (original_group_parameters g).1, (original_group_parameters g).2]

end LAlanine40K2025.BasinRefinement.WholeBandGeneratedInputs
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
