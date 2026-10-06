import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.RuntimeBasinRuntimeRegression

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Geometry.Data

abbrev RunIndex := Fin 5
abbrev Slab := Fin 4
abbrev Face := Fin 48
abbrev Seam := Fin 7
abbrev Knot := Fin 9
abbrev Field := BasinPartition.SourceData.Field
abbrev Bucket := BasinPartition.SourceData.Bucket

structure DomainReceipt where
  rows : Nat
  counts : Array Nat
  bucketPoint : Array (Array Int)
  point : Array Int
  floating : Array Int
  rounding : Array Int
  measure : Int
  sampledJacobianLower : Int
  disagreements : Nat
  wholeLabel : Option Nat
  deriving Inhabited

structure FaceReceipt where
  segment : Nat
  axis : Nat
  side : Nat
  rows : Nat
  point : Int
  floating : Int
  rounding : Int
  absoluteFluxUpper : Int
  sampledNormalUpper : Int
  counts : Array Nat
  disagreements : Nat
  deriving Inhabited

structure SeamReceipt where
  knot : Nat
  leftFace : Nat
  rightFace : Nat
  pointSum : Int
  floatSum : Int
  deriving Inhabited

structure AccountReceipt where
  laplacianZepto : Int
  picoResolutionResidual : Int
  pointBoundary : Int
  floatBoundary : Int
  boundaryRounding : Int
  divergenceResidual : Int
  capPoint : Int
  sidePoint : Int
  seamPoint : Int
  outerPoint : Int
  pointSlabResidual : Array Int
  floatSlabResidual : Array Int
  deriving Inhabited

structure RunReceipt where
  steps : Nat
  epsilonHex : String
  domains : Array DomainReceipt
  faces : Array FaceReceipt
  seams : Array SeamReceipt
  account : AccountReceipt
  lowerCounts : Array Nat
  upperCounts : Array Nat
  sampledNormalUpper : Int
  sampledAbsoluteFluxUpper : Int
  deriving Inhabited

noncomputable def parentCurrent := BasinPartition.Runtime.basinRuntimeAfterFirst

theorem parent_installed :
    type_of% (BasinPartition.Runtime.basinRuntime_material_installed parentCurrent) :=
  BasinPartition.Runtime.basinRuntime_material_installed parentCurrent

theorem parent_same_occurrence :
    parentCurrent.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit :=
  BasinPartition.Runtime.basinRuntime_same_actual_next

end LAlanine40K2025.BasinRefinement.Geometry.Data
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
