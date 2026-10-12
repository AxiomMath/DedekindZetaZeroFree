module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailBruhatIdentity
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.SignedWeylInversion

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

theorem actual_tail_phase_cube (u v : (LocalField F q)ˣ) :
    actualTailPhase F ζ hζ q (u ^ 3 * v) = actualTailPhase F ζ hζ q v := by

  simp only [actualTailPhase,
    DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.kappa_eq_one]

end DedekindZetaZeroFree.KPRankOneShellRepair

end
