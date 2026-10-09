import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_013_014
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_014_015
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_015_016
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_016_017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_017_018
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_018_019
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_019_020
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_020_021
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_021_022
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_022_023
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_023_024
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_024_025
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_025_026
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_026_027
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_027_028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_028_029
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_029_048
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_048_063
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_063_081
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V013_081_098

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_13 (j : Basis) (ordered : (13 : Basis) ≤ j) :
    |aoIntegral (13 : Basis) j - (recordedAttraction (13 : Basis) j : ℝ)| ≤
      (2/10^12 : ℝ) := by
  have rowSame : (13 : Basis) = ⟨13,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(13 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(13 : Basis) ≤ (12 : Basis) by decide) ordered)
  · convert vcell13_13_error using 1; norm_num
  · convert vcell13_14_error using 1; norm_num
  · convert vcell13_15_error using 1; norm_num
  · convert vcell13_16_error using 1; norm_num
  · convert vcell13_17_error using 1; norm_num
  · convert vcell13_18_error using 1; norm_num
  · convert vcell13_19_error using 1; norm_num
  · convert vcell13_20_error using 1; norm_num
  · convert vcell13_21_error using 1; norm_num
  · convert vcell13_22_error using 1; norm_num
  · convert vcell13_23_error using 1; norm_num
  · convert vcell13_24_error using 1; norm_num
  · convert vcell13_25_error using 1; norm_num
  · convert vcell13_26_error using 1; norm_num
  · convert vcell13_27_error using 1; norm_num
  · convert vcell13_28_error using 1; norm_num
  · convert vcell13_29_error using 1; norm_num
  · convert vcell13_30_error using 1; norm_num
  · convert vcell13_31_error using 1; norm_num
  · convert vcell13_32_error using 1; norm_num
  · convert vcell13_33_error using 1; norm_num
  · convert vcell13_34_error using 1; norm_num
  · convert vcell13_35_error using 1; norm_num
  · convert vcell13_36_error using 1; norm_num
  · convert vcell13_37_error using 1; norm_num
  · convert vcell13_38_error using 1; norm_num
  · convert vcell13_39_error using 1; norm_num
  · convert vcell13_40_error using 1; norm_num
  · convert vcell13_41_error using 1; norm_num
  · convert vcell13_42_error using 1; norm_num
  · convert vcell13_43_error using 1; norm_num
  · convert vcell13_44_error using 1; norm_num
  · convert vcell13_45_error using 1; norm_num
  · convert vcell13_46_error using 1; norm_num
  · convert vcell13_47_error using 1; norm_num
  · convert vcell13_48_error using 1; norm_num
  · convert vcell13_49_error using 1; norm_num
  · convert vcell13_50_error using 1; norm_num
  · convert vcell13_51_error using 1; norm_num
  · convert vcell13_52_error using 1; norm_num
  · convert vcell13_53_error using 1; norm_num
  · convert vcell13_54_error using 1; norm_num
  · convert vcell13_55_error using 1; norm_num
  · convert vcell13_56_error using 1; norm_num
  · convert vcell13_57_error using 1; norm_num
  · convert vcell13_58_error using 1; norm_num
  · convert vcell13_59_error using 1; norm_num
  · convert vcell13_60_error using 1; norm_num
  · convert vcell13_61_error using 1; norm_num
  · convert vcell13_62_error using 1; norm_num
  · convert vcell13_63_error using 1; norm_num
  · convert vcell13_64_error using 1; norm_num
  · convert vcell13_65_error using 1; norm_num
  · convert vcell13_66_error using 1; norm_num
  · convert vcell13_67_error using 1; norm_num
  · convert vcell13_68_error using 1; norm_num
  · convert vcell13_69_error using 1; norm_num
  · convert vcell13_70_error using 1; norm_num
  · convert vcell13_71_error using 1; norm_num
  · convert vcell13_72_error using 1; norm_num
  · convert vcell13_73_error using 1; norm_num
  · convert vcell13_74_error using 1; norm_num
  · convert vcell13_75_error using 1; norm_num
  · convert vcell13_76_error using 1; norm_num
  · convert vcell13_77_error using 1; norm_num
  · convert vcell13_78_error using 1; norm_num
  · convert vcell13_79_error using 1; norm_num
  · convert vcell13_80_error using 1; norm_num
  · convert vcell13_81_error using 1; norm_num
  · convert vcell13_82_error using 1; norm_num
  · convert vcell13_83_error using 1; norm_num
  · convert vcell13_84_error using 1; norm_num
  · convert vcell13_85_error using 1; norm_num
  · convert vcell13_86_error using 1; norm_num
  · convert vcell13_87_error using 1; norm_num
  · convert vcell13_88_error using 1; norm_num
  · convert vcell13_89_error using 1; norm_num
  · convert vcell13_90_error using 1; norm_num
  · convert vcell13_91_error using 1; norm_num
  · convert vcell13_92_error using 1; norm_num
  · convert vcell13_93_error using 1; norm_num
  · convert vcell13_94_error using 1; norm_num
  · convert vcell13_95_error using 1; norm_num
  · convert vcell13_96_error using 1; norm_num
  · convert vcell13_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
