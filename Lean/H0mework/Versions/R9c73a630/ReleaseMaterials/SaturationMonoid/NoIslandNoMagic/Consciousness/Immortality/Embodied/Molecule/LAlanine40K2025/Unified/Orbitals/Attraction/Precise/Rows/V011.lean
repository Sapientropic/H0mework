import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_011_012
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_012_013
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_013_014
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_014_015
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_015_016
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_016_017
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_017_018
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_018_019
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_019_020
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_020_032
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_032_046
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_046_056
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_056_067
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_067_079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_079_092
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V011_092_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_11 (j : Basis) (ordered : (11 : Basis) ≤ j) :
    |aoIntegral (11 : Basis) j - (recordedAttraction (11 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (11 : Basis) = ⟨11,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(11 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(11 : Basis) ≤ (10 : Basis) by decide) ordered)
  · convert vcell11_11_error using 1; norm_num
  · convert vcell11_12_error using 1; norm_num
  · convert vcell11_13_error using 1; norm_num
  · convert vcell11_14_error using 1; norm_num
  · convert vcell11_15_error using 1; norm_num
  · convert vcell11_16_error using 1; norm_num
  · convert vcell11_17_error using 1; norm_num
  · convert vcell11_18_error using 1; norm_num
  · convert vcell11_19_error using 1; norm_num
  · convert vcell11_20_error using 1; norm_num
  · convert vcell11_21_error using 1; norm_num
  · convert vcell11_22_error using 1; norm_num
  · convert vcell11_23_error using 1; norm_num
  · convert vcell11_24_error using 1; norm_num
  · convert vcell11_25_error using 1; norm_num
  · convert vcell11_26_error using 1; norm_num
  · convert vcell11_27_error using 1; norm_num
  · convert vcell11_28_error using 1; norm_num
  · convert vcell11_29_error using 1; norm_num
  · convert vcell11_30_error using 1; norm_num
  · convert vcell11_31_error using 1; norm_num
  · convert vcell11_32_error using 1; norm_num
  · convert vcell11_33_error using 1; norm_num
  · convert vcell11_34_error using 1; norm_num
  · convert vcell11_35_error using 1; norm_num
  · convert vcell11_36_error using 1; norm_num
  · convert vcell11_37_error using 1; norm_num
  · convert vcell11_38_error using 1; norm_num
  · convert vcell11_39_error using 1; norm_num
  · convert vcell11_40_error using 1; norm_num
  · convert vcell11_41_error using 1; norm_num
  · convert vcell11_42_error using 1; norm_num
  · convert vcell11_43_error using 1; norm_num
  · convert vcell11_44_error using 1; norm_num
  · convert vcell11_45_error using 1; norm_num
  · convert vcell11_46_error using 1; norm_num
  · convert vcell11_47_error using 1; norm_num
  · convert vcell11_48_error using 1; norm_num
  · convert vcell11_49_error using 1; norm_num
  · convert vcell11_50_error using 1; norm_num
  · convert vcell11_51_error using 1; norm_num
  · convert vcell11_52_error using 1; norm_num
  · convert vcell11_53_error using 1; norm_num
  · convert vcell11_54_error using 1; norm_num
  · convert vcell11_55_error using 1; norm_num
  · convert vcell11_56_error using 1; norm_num
  · convert vcell11_57_error using 1; norm_num
  · convert vcell11_58_error using 1; norm_num
  · convert vcell11_59_error using 1; norm_num
  · convert vcell11_60_error using 1; norm_num
  · convert vcell11_61_error using 1; norm_num
  · convert vcell11_62_error using 1; norm_num
  · convert vcell11_63_error using 1; norm_num
  · convert vcell11_64_error using 1; norm_num
  · convert vcell11_65_error using 1; norm_num
  · convert vcell11_66_error using 1; norm_num
  · convert vcell11_67_error using 1; norm_num
  · convert vcell11_68_error using 1; norm_num
  · convert vcell11_69_error using 1; norm_num
  · convert vcell11_70_error using 1; norm_num
  · convert vcell11_71_error using 1; norm_num
  · convert vcell11_72_error using 1; norm_num
  · convert vcell11_73_error using 1; norm_num
  · convert vcell11_74_error using 1; norm_num
  · convert vcell11_75_error using 1; norm_num
  · convert vcell11_76_error using 1; norm_num
  · convert vcell11_77_error using 1; norm_num
  · convert vcell11_78_error using 1; norm_num
  · convert vcell11_79_error using 1; norm_num
  · convert vcell11_80_error using 1; norm_num
  · convert vcell11_81_error using 1; norm_num
  · convert vcell11_82_error using 1; norm_num
  · convert vcell11_83_error using 1; norm_num
  · convert vcell11_84_error using 1; norm_num
  · convert vcell11_85_error using 1; norm_num
  · convert vcell11_86_error using 1; norm_num
  · convert vcell11_87_error using 1; norm_num
  · convert vcell11_88_error using 1; norm_num
  · convert vcell11_89_error using 1; norm_num
  · convert vcell11_90_error using 1; norm_num
  · convert vcell11_91_error using 1; norm_num
  · convert vcell11_92_error using 1; norm_num
  · convert vcell11_93_error using 1; norm_num
  · convert vcell11_94_error using 1; norm_num
  · convert vcell11_95_error using 1; norm_num
  · convert vcell11_96_error using 1; norm_num
  · convert vcell11_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
