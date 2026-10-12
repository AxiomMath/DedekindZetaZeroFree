module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneShellContinuation KPRankOneForwardTestVector
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

include hζ in
 theorem root : ∃ ξ : (valuation (LocalField F q)).integer,
    (ξ : LocalField F q) = algebraMap F (LocalField F q) (ζ ^ 4) ∧ IsPrimitiveRoot ξ 3 := by
  have hp : IsPrimitiveRoot (algebraMap F (LocalField F q) (ζ ^ 4)) 3 :=
    (hζ.pow (by norm_num) (by norm_num : 12 = 4 * 3)).map_of_injective
      (FaithfulSMul.algebraMap_injective F (LocalField F q))
  have hv : valuation (LocalField F q) (algebraMap F (LocalField F q) (ζ ^ 4)) = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [← map_pow, hp.pow_eq_one, map_one]
  let ξ : (valuation (LocalField F q)).integer := ⟨algebraMap F (LocalField F q) (ζ ^ 4),
    by rw [Valuation.mem_integer_iff, hv]⟩
  refine ⟨ξ, rfl, ?_⟩
  exact (show IsPrimitiveRoot (((valuation (LocalField F q)).integer.subtype) ξ) 3 from hp).of_map_of_injective Subtype.val_injective

end
end DedekindZetaZeroFree.KPExceptionalRaw
