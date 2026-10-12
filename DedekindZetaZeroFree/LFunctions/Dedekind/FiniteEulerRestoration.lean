module

public import DedekindZetaZeroFree.LFunctions.Hecke.DirichletSeriesRightEdgeBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.OmittedEulerProductBounds
public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Nonvanishing.Mellin.HolomorphicZeroTransfer

@[expose] public section

namespace DedekindZetaZeroFree
namespace PrincipalPointwise

noncomputable section
open scoped NumberField Classical Topology
open Filter

theorem principal_top_series_eq_dedekindZeta
    (F : Type) [Field F] [NumberField F]
    (η : RayClassCharacter F ⊤) (hη : η.IsPrincipal)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-s)) =
      NumberField.dedekindZeta F s := by
  have hsum := (heckeDirichlet_right_edge F s.re hs ⊤ top_ne_bot η s le_rfl).1
  have hgroup := hsum.hasSum.tsum_fiberwise (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hfiber (n : ℕ) :
      (∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
        η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) =
      LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      have hz (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 0}) :
          η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) = 0 := by
        have hI : I.val = ⊥ := Ideal.absNorm_eq_zero_iff.mp I.property
        rw [hI, (η.eq_zero_iff' ⊥).mpr (Or.inl rfl), zero_mul]
      simp [hz, LSeries.term]
    · have hterm (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}) :
          η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := by
        have hI : I.val ≠ ⊥ := by
          intro h
          exact hn (by simpa [h] using I.property.symm)
        rw [hη I.val hI (by simp), one_mul, I.property]
      simp_rw [hterm]
      rw [tsum_const, nsmul_eq_mul, LSeries.term_of_ne_zero hn]
      simp [Complex.cpow_neg, div_eq_mul_inv]
  have heq : (fun n => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) =
      LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s :=
    funext hfiber
  change HasSum (fun n => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
    η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) _ at hgroup
  rw [heq] at hgroup
  exact hgroup.tsum_eq.symm

theorem continuation_eq_of_right_match
    (L f : ℂ → ℂ)
    (hL : DifferentiableOn ℂ L {s : ℂ | 0 < s.re ∧ s ≠ 1})
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hmatch : ∀ s : ℂ, 1 < s.re → L s = f s) :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → L s = f s := by
  have hopen := mellin_punctured_halfplane_isOpen 0 (by norm_num)
  have hLa : AnalyticOnNhd ℂ L {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    hL.analyticOnNhd hopen
  have hfa : AnalyticOnNhd ℂ f {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (hf.mono (fun s hs => hs.2)).analyticOnNhd hopen
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), L z = f z := by
    have hacc := mellin_punctured_halfplane_two_accPt
    apply (accPt_iff_frequently_nhdsNE.mp hacc).mono
    rintro z ⟨t, ht, rfl⟩
    apply hmatch
    simp
  have heq := hLa.eqOn_of_preconnected_of_frequently_eq hfa
    (mellin_punctured_halfplane_isPreconnected 0 (by norm_num))
    (mellin_punctured_halfplane_two_mem 0 (by norm_num)) hfreq
  intro s hs hs1
  exact heq ⟨hs, hs1⟩

theorem principal_top_continuation_eq
    (F : Type) [Field F] [NumberField F]
    (η : RayClassCharacter F ⊤) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F ⊤ η)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s) :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → P.L s = f s := by
  apply continuation_eq_of_right_match P.L f P.L_holo hf
  intro s hs
  rw [← (P.series s hs).tsum_eq,
    principal_top_series_eq_dedekindZeta F η hη s hs, hmatch s hs]

theorem continuation_ne_zero_of_incomplete_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : SArithmeticData F) (hmod : S.modulus = ⊤)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F S.modulus η)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta F s)
    (hzero : ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 →
      comparisonPrincipalIncompleteL F S η hη P s ≠ 0) :
    ∀ s : ℂ, (5999 / 6000 : ℝ) < s.re → s ≠ 1 → f s ≠ 0 := by
  have hLf : ∀ s : ℂ, 0 < s.re → s ≠ 1 → P.L s = f s := by
    clear hzero
    revert η hη P
    rw [hmod]
    intro η hη P
    exact principal_top_continuation_eq F η hη P f hf hmatch
  intro s hs hs1 hfs
  apply hzero s hs hs1
  simp [comparisonPrincipalIncompleteL, hLf s (by linarith) hs1, hfs]

end
end PrincipalPointwise
end DedekindZetaZeroFree
