module

public import DedekindZetaZeroFree.Arithmetic.Ideals.TraceQuotients.CodifferentGenerators
public import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteRings.Norm
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveResidueCharacterKernels
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.GeneratorIdealCoefficients
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOfGroupCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterConjugation
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitivePrincipalCharacters

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section

open scoped NumberField nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

variable {F : Type} [Field F] [nf : NumberField F]

def rayNormalizedGaussFactor
    (m : Ideal (𝓞 F)) (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (b : Ideal (𝓞 F)) (τ : ℂ) : ℂ :=
  (τ * η b) / (Real.sqrt (Ideal.absNorm m : ℝ) : ℂ)

variable (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (hprim : η.IsPrimitive)

include nf hF hm hmt hprim

private theorem normalizedGauss_residue_primitive :
    IsPrimitiveRingUnitChar
      ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)) := by
  intro J hJ
  let f := Ideal.comap (Ideal.Quotient.mk m) J
  have hmf : m ≤ f := by
    intro x hx
    change Ideal.Quotient.mk m x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hstrict : m < f := by
    apply lt_of_le_of_ne hmf
    intro heq
    apply hJ
    have hh := Ideal.map_comap_of_surjective (Ideal.Quotient.mk m)
      (Ideal.Quotient.mk_surjective) J
    change Ideal.map (Ideal.Quotient.mk m) f = J at hh
    rw [← heq, Ideal.map_quotient_self] at hh
    exact hh.symm
  obtain ⟨u, hu, hne⟩ := residueRayCharacter_exists_kernel_ne_one
    hF hm hmt η hprim f hstrict
  refine ⟨u, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 F ⧸ m)
    have hv := congrArg Units.val hu
    have hxf : x - 1 ∈ f := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hv' : Ideal.Quotient.factor hstrict.le (u : 𝓞 F ⧸ m) = 1 := hv
      have hx' : Ideal.Quotient.mk f x = 1 := by
        rw [← Ideal.Quotient.factor_mk hstrict.le x, hx]
        exact hv'
      simp [hx']
    change Ideal.Quotient.mk m (x - 1) ∈ J at hxf
    simpa only [map_sub, map_one, hx] using hxf
  · change ((residueRayCharacter hF hm hmt η u : ℂˣ) : ℂ) ≠ 1
    intro h
    apply hne
    exact Units.ext h

theorem rayNormalizedGaussFactor_norm_eq_one :
    letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
    letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
    letI := rayTraceQuotientModule m hm
    ∀ (β₀ : ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F).coeToSubmodule)
      (hgen : Function.Bijective (LinearMap.toSpanSingleton (𝓞 F ⧸ m)
        (rayTraceQuotient m)
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀)))
      (b : Ideal (𝓞 F)) (hb : b ≠ ⊥) (hbcop : m ⊔ b = ⊤)
      (hbimage : (b : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (β₀ : F) *
          (m : FractionalIdeal (𝓞 F)⁰ F) * (codifferentFractionalIdeal F)⁻¹)
      (e₀ : AddChar (𝓞 F ⧸ m) ℂ)
      (he₀ : e₀ = rayTraceGeneratorChar m hm
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀))
      (τ : ℂ)
      (hτ : τ = finiteRingGaussSum e₀
        ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η))),
      ‖rayNormalizedGaussFactor m η b τ‖ = 1 := by
  letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
  letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
  letI := rayTraceQuotientModule m hm
  letI : Nontrivial (𝓞 F ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hmt
  intro β₀ hgen b hb hbcop hbimage e₀ he₀ τ hτ
  have he : IsPrimitiveRingAddChar e₀ := by
    rw [he₀]
    exact rayTraceGeneratorChar_primitive m hm _ hgen
  have hn := finiteRingGaussSum_normalized_norm e₀ he _
    (normalizedGauss_residue_primitive hF m hm hmt η hprim)
  have hc : Fintype.card (𝓞 F ⧸ m) = Ideal.absNorm m := by
    rw [Ideal.absNorm_apply]
    exact Nat.card_eq_fintype_card.symm
  rw [hc, ← hτ] at hn
  unfold rayNormalizedGaussFactor
  rw [mul_div_right_comm, norm_mul, hn,
    rayClassCharacter_norm_eq_one hm η b hb (sup_comm m b ▸ hbcop), one_mul]

end DedekindZetaZeroFree.Hecke

end
