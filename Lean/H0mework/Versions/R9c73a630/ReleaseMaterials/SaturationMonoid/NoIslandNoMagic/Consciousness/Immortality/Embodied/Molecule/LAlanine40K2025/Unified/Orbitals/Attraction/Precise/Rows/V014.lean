import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_014_017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_017_023
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_023_028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_028_031
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_031_037
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_037_044
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_044_048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_048_051
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_051_057
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_057_062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_062_065
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_065_071
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_071_078
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_078_081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_081_087
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_087_094
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V014_094_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_14 (j : Basis) (ordered : (14 : Basis) ≤ j) :
    |aoIntegral (14 : Basis) j - (recordedAttraction (14 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (14 : Basis) = ⟨14,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(14 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(14 : Basis) ≤ (13 : Basis) by decide) ordered)
  · convert vcell14_14_error using 1; norm_num
  · convert vcell14_15_error using 1; norm_num
  · convert vcell14_16_error using 1; norm_num
  · convert vcell14_17_error using 1; norm_num
  · convert vcell14_18_error using 1; norm_num
  · convert vcell14_19_error using 1; norm_num
  · convert vcell14_20_error using 1; norm_num
  · convert vcell14_21_error using 1; norm_num
  · convert vcell14_22_error using 1; norm_num
  · convert vcell14_23_error using 1; norm_num
  · convert vcell14_24_error using 1; norm_num
  · convert vcell14_25_error using 1; norm_num
  · convert vcell14_26_error using 1; norm_num
  · convert vcell14_27_error using 1; norm_num
  · convert vcell14_28_error using 1; norm_num
  · convert vcell14_29_error using 1; norm_num
  · convert vcell14_30_error using 1; norm_num
  · convert vcell14_31_error using 1; norm_num
  · convert vcell14_32_error using 1; norm_num
  · convert vcell14_33_error using 1; norm_num
  · convert vcell14_34_error using 1; norm_num
  · convert vcell14_35_error using 1; norm_num
  · convert vcell14_36_error using 1; norm_num
  · convert vcell14_37_error using 1; norm_num
  · convert vcell14_38_error using 1; norm_num
  · convert vcell14_39_error using 1; norm_num
  · convert vcell14_40_error using 1; norm_num
  · convert vcell14_41_error using 1; norm_num
  · convert vcell14_42_error using 1; norm_num
  · convert vcell14_43_error using 1; norm_num
  · convert vcell14_44_error using 1; norm_num
  · convert vcell14_45_error using 1; norm_num
  · convert vcell14_46_error using 1; norm_num
  · convert vcell14_47_error using 1; norm_num
  · convert vcell14_48_error using 1; norm_num
  · convert vcell14_49_error using 1; norm_num
  · convert vcell14_50_error using 1; norm_num
  · convert vcell14_51_error using 1; norm_num
  · convert vcell14_52_error using 1; norm_num
  · convert vcell14_53_error using 1; norm_num
  · convert vcell14_54_error using 1; norm_num
  · convert vcell14_55_error using 1; norm_num
  · convert vcell14_56_error using 1; norm_num
  · convert vcell14_57_error using 1; norm_num
  · convert vcell14_58_error using 1; norm_num
  · convert vcell14_59_error using 1; norm_num
  · convert vcell14_60_error using 1; norm_num
  · convert vcell14_61_error using 1; norm_num
  · convert vcell14_62_error using 1; norm_num
  · convert vcell14_63_error using 1; norm_num
  · convert vcell14_64_error using 1; norm_num
  · convert vcell14_65_error using 1; norm_num
  · convert vcell14_66_error using 1; norm_num
  · convert vcell14_67_error using 1; norm_num
  · convert vcell14_68_error using 1; norm_num
  · convert vcell14_69_error using 1; norm_num
  · convert vcell14_70_error using 1; norm_num
  · convert vcell14_71_error using 1; norm_num
  · convert vcell14_72_error using 1; norm_num
  · convert vcell14_73_error using 1; norm_num
  · convert vcell14_74_error using 1; norm_num
  · convert vcell14_75_error using 1; norm_num
  · convert vcell14_76_error using 1; norm_num
  · convert vcell14_77_error using 1; norm_num
  · convert vcell14_78_error using 1; norm_num
  · convert vcell14_79_error using 1; norm_num
  · convert vcell14_80_error using 1; norm_num
  · convert vcell14_81_error using 1; norm_num
  · convert vcell14_82_error using 1; norm_num
  · convert vcell14_83_error using 1; norm_num
  · convert vcell14_84_error using 1; norm_num
  · convert vcell14_85_error using 1; norm_num
  · convert vcell14_86_error using 1; norm_num
  · convert vcell14_87_error using 1; norm_num
  · convert vcell14_88_error using 1; norm_num
  · convert vcell14_89_error using 1; norm_num
  · convert vcell14_90_error using 1; norm_num
  · convert vcell14_91_error using 1; norm_num
  · convert vcell14_92_error using 1; norm_num
  · convert vcell14_93_error using 1; norm_num
  · convert vcell14_94_error using 1; norm_num
  · convert vcell14_95_error using 1; norm_num
  · convert vcell14_96_error using 1; norm_num
  · convert vcell14_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
