module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.Reciprocity
public import DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.PhaseCharacters

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.CorrectedWeilSource
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem inverse_four_hilbert_eq_star_residue (A : SArithmeticData F)
    (σ : F →+* ℂ) (I : A.Exterior) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) :
    (σ (((A.H_S (A.diagonal CubicWeilCorrection.fourS)
      (A.diagonal a) : Fˣ) : F)))⁻¹ =
        star (σ (A.sexticResidue I (4 : A.R))) := by
  have htwo (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
      v.valuation F (2 : F) = 1 := by
    have hnot : (2 : 𝓞 F) ∉ v.asIdeal := by
      intro h
      apply hv
      apply A.above_six
      convert v.asIdeal.mul_mem_right 3 h using 1 <;> norm_num
    convert (v.valuation_eq_one_iff_notMem (K := F)).mpr hnot using 1
    rw [map_ofNat (algebraMap (𝓞 F) F)]
  have hfour : CubicWeilCorrection.fourS (F := F) ∈ A.U := by
    intro v hv
    change v.valuation F (4 : F) = 1
    rw [show (4 : F) = 2 ^ 2 by norm_num, map_pow, htwo v hv, one_pow]
  let eps : A.U := ⟨CubicWeilCorrection.fourS, hfour⟩
  have heps : (A.unitEquiv eps : A.R) = 4 := by
    apply Subtype.ext
    rfl
  have hrec := ArithmeticContext.actual_sextic_sunit_symbol A I p a eps hp hap
  rw [heps] at hrec
  rw [hrec]
  apply Complex.inv_eq_conj
  have hroot := (mem_rootsOfUnity 6 _).mp
    (A.H_S (A.diagonal CubicWeilCorrection.fourS) (A.diagonal a)).property
  have hpow : (σ (((A.H_S (A.diagonal CubicWeilCorrection.fourS)
      (A.diagonal a) : Fˣ) : F))) ^ 6 = 1 := by
    rw [← map_pow]
    have hf := congrArg (fun u : Fˣ => (u : F)) hroot
    simpa using congrArg σ hf
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp
  rw [← Complex.norm_pow, hpow, norm_one]

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.CorrectedWeilSource
