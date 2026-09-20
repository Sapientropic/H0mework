import H0mework.Realization.Topology.DualExtension
import H0mework.Arithmetic.Mellin.Functional
import H0mework.Arithmetic.Mellin.QuarterEnergy
import H0mework.Arithmetic.Mellin.QuarterL2

/-!
# Narrow quarter-`L²` Mellin test carrier

The lawful test carrier, its literal `L²` feature, and its algebraic Mellin
functional are kept below equivariant residuals, q-rich coordinates, endpoint
effects, and zero consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex MeasureTheory
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

def quarterMellinL2TestSubmodule (z : ℂ) :
    Submodule ℂ ClozelPositiveMellinFunction :=
  positiveMellinQuarterL2Submodule ⊓
    positiveMellinConvergentSubmodule z

abbrev QuarterMellinL2Test (z : ℂ) :=
  quarterMellinL2TestSubmodule z

def quarterMellinL2Feature (z : ℂ) :
    QuarterMellinL2Test z →ₗ[ℂ] PositiveMellinQuarterEnergy where
  toFun value := value.2.1.toLp
    (positiveMellinLogQuarterTransform value.1)
  map_add' left right := by
    let leftMem := left.2.1
    let rightMem := right.2.1
    let sumMem := (left + right).2.1
    calc
      sumMem.toLp
          (positiveMellinLogQuarterTransform
            ((left + right : QuarterMellinL2Test z).1)) =
          (leftMem.add rightMem).toLp
            (positiveMellinLogQuarterTransform left.1 +
              positiveMellinLogQuarterTransform right.1) := by
        apply MemLp.toLp_congr
        exact ae_of_all _ fun x => by
          exact congrFun
            (map_add positiveMellinLogQuarterTransform
              left.1 right.1) x
      _ = leftMem.toLp
            (positiveMellinLogQuarterTransform left.1) +
          rightMem.toLp
            (positiveMellinLogQuarterTransform right.1) :=
        MemLp.toLp_add leftMem rightMem
  map_smul' coefficient value := by
    let valueMem := value.2.1
    let smulMem := (coefficient • value).2.1
    calc
      smulMem.toLp
          (positiveMellinLogQuarterTransform
            ((coefficient • value : QuarterMellinL2Test z).1)) =
          (valueMem.const_smul coefficient).toLp
            (coefficient •
              positiveMellinLogQuarterTransform value.1) := by
        apply MemLp.toLp_congr
        exact ae_of_all _ fun x => by
          exact congrFun
            (map_smul positiveMellinLogQuarterTransform
              coefficient value.1) x
      _ = coefficient • valueMem.toLp
          (positiveMellinLogQuarterTransform value.1) :=
        MemLp.toLp_const_smul coefficient valueMem

def quarterMellinL2Functional (z : ℂ) :
    TestDual (QuarterMellinL2Test z) where
  toFun value := mellin (positiveMellinExtension value.1) z
  map_add' left right := by
    change mellin
        (positiveMellinExtension (left.1 + right.1)) z = _
    rw [map_add]
    exact (hasMellin_add left.2.2 right.2.2).2
  map_smul' coefficient value := by
    change mellin
        (positiveMellinExtension (coefficient • value.1)) z = _
    rw [map_smul]
    exact (hasMellin_const_smul value.2.2 coefficient).2

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
