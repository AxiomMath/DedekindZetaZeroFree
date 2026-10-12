module

public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Nonvanishing.Mellin.PuncturedHalfPlane

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellin

open scoped NumberField
open NumberField IsDedekindDomain

private theorem rayChar_transport_apply
    {F : Type} [Field F] [NumberField F] {𝔪 𝔪' : Ideal (𝓞 F)} (h : 𝔪 = 𝔪')
    (η : RayClassCharacter F 𝔪) :
    ((h ▸ η : RayClassCharacter F 𝔪') : Ideal (𝓞 F) → ℂ) = η := by
  cases h
  rfl

theorem incomplete_nonzero_of_enlargement
    (F : Type) [Field F] [NumberField F]
    (S A : SArithmeticData F) (hSA : S.Sf ⊆ A.Sf)
    (hmod : A.modulus = S.modulus)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η)
    (hηA : (hmod.symm ▸ η).IsPrincipal)
    (Q : PrincipalRayHeckeData F A.modulus (hmod.symm ▸ η))
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hA : comparisonPrincipalIncompleteL F A (hmod.symm ▸ η) hηA Q s ≠ 0) :
    comparisonPrincipalIncompleteL F S η hη P s ≠ 0 := by
  classical
  have hchar : ∀ I : Ideal (𝓞 F), (hmod.symm ▸ η) I = η I := by
    intro I
    rw [rayChar_transport_apply (hmod.symm) η]

  have hright : ∀ z : ℂ, 1 < z.re → P.L z = Q.L z := by
    intro z hz
    have hseries : HasSum (fun I : Ideal (𝓞 F) =>
        η I * (Ideal.absNorm I : ℂ) ^ (-z)) (Q.L z) := by
      convert Q.series z hz using 1
      ext I
      rw [hchar I]
    exact (P.series z hz).unique hseries

  have hopen := mellin_punctured_halfplane_isOpen 0 (by norm_num)
  have hPa : AnalyticOnNhd ℂ P.L {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    P.L_holo.analyticOnNhd hopen
  have hQa : AnalyticOnNhd ℂ Q.L {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    Q.L_holo.analyticOnNhd hopen
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {2}ᶜ, P.L z = Q.L z := by
    apply (accPt_iff_frequently_nhdsNE.mp mellin_punctured_halfplane_two_accPt).mono
    rintro z ⟨t, ht, rfl⟩
    apply hright
    simp
  have heq := hPa.eqOn_of_preconnected_of_frequently_eq hQa
    (mellin_punctured_halfplane_isPreconnected 0 (by norm_num))
    (mellin_punctured_halfplane_two_mem 0 (by norm_num)) hfreq
  have hL : P.L s = Q.L s := heq ⟨hs, hs1⟩

  set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    (1 - η v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)) with hf
  have hchar' : ∀ v : HeightOneSpectrum (𝓞 F),
      (1 - (hmod.symm ▸ η) v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))
        = f v := by
    intro v
    rw [hf, hchar v.asIdeal]
  have hsplit : ∏ v ∈ A.Sf, f v =
      (∏ v ∈ S.Sf, f v) * ∏ v ∈ A.Sf \ S.Sf, f v := by
    rw [← Finset.prod_sdiff hSA, mul_comm]
  have key : comparisonPrincipalIncompleteL F A (hmod.symm ▸ η) hηA Q s =
      comparisonPrincipalIncompleteL F S η hη P s * (∏ v ∈ A.Sf \ S.Sf, f v) := by
    unfold comparisonPrincipalIncompleteL
    rw [hL]
    simp only [hchar']
    rw [hsplit]
    ring
  intro hS
  exact hA (by rw [key, hS, zero_mul])

end DedekindZetaZeroFree.PrincipalMellin
