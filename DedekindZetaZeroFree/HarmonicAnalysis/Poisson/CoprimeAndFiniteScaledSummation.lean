module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalHeckeSummation
public import DedekindZetaZeroFree.Arithmetic.Ideals.NonzeroMultiplesEquivalence
public import DedekindZetaZeroFree.Arithmetic.Ideals.MoebiusCoprimality

@[expose] public section

section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

theorem finite_scaled_principalPoisson
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (D : Finset (Ideal (𝓞 F)))
    (hD : ∀ d ∈ D, d ≠ ⊥) (a : Ideal (𝓞 F) → ℂ) :
    let T : ℝ → ℂ := fun x => if 0 < x then
      mellinInv 2 (fun s =>
        (principalDiscriminant F : ℂ) ^ (s - 1 / 2) *
        Complex.Gammaℂ s ^ principalComplexPlaces F *
        (Complex.Gammaℂ (1 - s))⁻¹ ^ (principalComplexPlaces F - 1) *
        Vendor.originMellinQ h (1 - s)) x else 0
    let α := principalPoleCoefficient F hF
    let κ := α / ((Real.sqrt (principalDiscriminant F) : ℂ) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F)
    let z0 : ℂ := if principalComplexPlaces F = 1 then -α / 2 else 0
    (∑ d ∈ D, a d *
      (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
        h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))))) =
      κ * (X : ℂ) * Vendor.originMellinH h 1 *
        (∑ d ∈ D, a d / (Ideal.absNorm d : ℂ)) +
      z0 * h 0 * (∑ d ∈ D, a d) +
      ∑ d ∈ D, a d * ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
        (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          T (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ))) := by
  dsimp only
  set T : ℝ → ℂ := (fun x => if 0 < x then
      mellinInv 2 (fun s =>
        (principalDiscriminant F : ℂ) ^ (s - 1 / 2) *
        Complex.Gammaℂ s ^ principalComplexPlaces F *
        (Complex.Gammaℂ (1 - s))⁻¹ ^ (principalComplexPlaces F - 1) *
        Vendor.originMellinQ h (1 - s)) x else 0)
  set α := principalPoleCoefficient F hF with hα
  set κ := α / ((Real.sqrt (principalDiscriminant F) : ℂ) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F) with hκ
  set z0 : ℂ := (if principalComplexPlaces F = 1 then -α / 2 else 0) with hz0
  have key : ∀ d ∈ D,
      a d * (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
        h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ)))) =
      κ * (X : ℂ) * Vendor.originMellinH h 1 * (a d / (Ideal.absNorm d : ℂ)) +
      z0 * h 0 * a d +
      a d * ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
        (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          T (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ))) := by
    intro d hd
    have hdpos : (0 : ℝ) < (Ideal.absNorm d : ℝ) := by
      have hne : Ideal.absNorm d ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hD d hd
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hpp := principalPoisson F hF h hh hcompact
      (X / (Ideal.absNorm d : ℝ)) (div_pos hX hdpos)
    dsimp only at hpp
    obtain ⟨-, -, hmain⟩ := hpp
    rw [← hα] at hmain
    have h1 : ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) =
        (X : ℂ) / (Ideal.absNorm d : ℂ) := by push_cast; ring
    have h2 : ∀ I : Ideal (𝓞 F),
        (X / (Ideal.absNorm d : ℝ)) * (Ideal.absNorm I : ℝ) =
          X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ) := by
      intro I; ring
    have htsum : (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          (if 0 < (X / (Ideal.absNorm d : ℝ)) * (Ideal.absNorm I : ℝ) then
            mellinInv 2 (fun s =>
              (principalDiscriminant F : ℂ) ^ (s - 1 / 2) *
              Complex.Gammaℂ s ^ principalComplexPlaces F *
              (Complex.Gammaℂ (1 - s))⁻¹ ^ (principalComplexPlaces F - 1) *
              Vendor.originMellinQ h (1 - s))
              ((X / (Ideal.absNorm d : ℝ)) * (Ideal.absNorm I : ℝ)) else 0)) =
        (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
          T (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ))) := by
      apply tsum_congr; intro I
      by_cases hI : I = ⊥
      · simp [hI]
      · simp only [if_neg hI]; rw [h2 I]
    rw [htsum, h1] at hmain
    have hmul := congrArg (fun z : ℂ => a d * z) hmain
    rw [mul_add, mul_sub] at hmul
    rw [hmul]
    rw [hz0, hκ]
    by_cases hr : principalComplexPlaces F = 1
    · simp only [if_pos hr]; ring
    · simp only [if_neg hr]; ring
  rw [Finset.sum_congr rfl key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

end

end

section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

private theorem finsum_ite_eq_finsum_subtype {α : Type*} {M : Type*} [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (g : α → M) :
    (∑ᶠ a : α, if p a then g a else 0) = ∑ᶠ a : Subtype p, g a := by
  rw [finsum_subtype_eq_finsum_cond (f := g) (p := p)]
  apply finsum_congr
  intro i
  by_cases hp : p i
  · rw [if_pos hp]
    exact (finsum_eq_single (fun _ : p i => g i) hp
      (fun x hx => absurd (Subsingleton.elim x hp) hx)).symm
  · rw [if_neg hp]
    haveI : IsEmpty (p i) := ⟨fun x => hp x⟩
    exact (finsum_of_isEmpty (fun _ : p i => g i)).symm

theorem multiplesFinsum_eq_scaledPrincipal
    {F : Type*} [Field F] [NumberField F]
    (h : ℝ → ℂ) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (d : Ideal (𝓞 F)) (hd : d ≠ ⊥) :
    (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then
      h ((Ideal.absNorm I : ℝ) / X) else 0) =
    ∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
      h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))) := by
  classical

  let e : {J : Ideal (𝓞 F) // J ≠ ⊥} → {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ d ∣ I} :=
    fun J => ⟨d * J.val, mul_ne_zero hd J.2, ⟨J.val, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro J₁ J₂ hJ
      refine Subtype.ext (mul_left_cancel₀ hd ?_)
      exact congrArg Subtype.val hJ
    · intro I
      obtain ⟨J, hJ⟩ := I.2.2
      refine ⟨⟨J, fun hbot => I.2.1 ?_⟩, Subtype.ext hJ.symm⟩
      rw [hJ, hbot, Ideal.mul_bot]

  have heq : ∀ J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      h ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ))) =
        h ((Ideal.absNorm (e J).val : ℝ) / X) := by
    intro J
    congr 1
    show (Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ)) =
      (Ideal.absNorm (d * J.val) : ℝ) / X
    have hdN : (Ideal.absNorm d : ℝ) ≠ 0 := by
      have : Ideal.absNorm d ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
      exact_mod_cast this
    rw [map_mul, Nat.cast_mul]
    field_simp
  have key : (∑ᶠ J : {J : Ideal (𝓞 F) // J ≠ ⊥},
        h ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ)))) =
      ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ d ∣ I},
        h ((Ideal.absNorm I.val : ℝ) / X) :=
    finsum_eq_of_bijective e he heq
  rw [finsum_ite_eq_finsum_subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥ ∧ d ∣ I)
    (fun I => h ((Ideal.absNorm I : ℝ) / X))]
  rw [show (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
        h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ)))) =
      ∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ then
        h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))) else 0 from by
    apply finsum_congr
    intro I
    by_cases hI : I = ⊥ <;> simp [hI]]
  rw [finsum_ite_eq_finsum_subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥)
    (fun I => h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ))))]
  exact key.symm

end DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact

end

end

section
/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve

theorem poissonCoprimeExact
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    (X : ℝ) (hX : 0 < X) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    let T : ℝ → ℂ := fun x => if 0 < x then
      mellinInv 2 (fun s =>
        (principalDiscriminant F : ℂ) ^ (s - 1 / 2) *
        Complex.Gammaℂ s ^ principalComplexPlaces F *
        (Complex.Gammaℂ (1 - s))⁻¹ ^ (principalComplexPlaces F - 1) *
        Vendor.originMellinQ h (1 - s)) x else 0
    let α := principalPoleCoefficient F hF
    let κ := α / ((Real.sqrt (principalDiscriminant F) : ℂ) *
      Complex.Gammaℂ 1 ^ principalComplexPlaces F)
    let z0 : ℂ := if principalComplexPlaces F = 1 then -α / 2 else 0
    let P : ℂ := ∑ d ∈ idealDivisors m,
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ)
    (∑ᶠ I : Ideal (𝓞 F),
      if I ≠ ⊥ ∧ I ⊔ m = ⊤ then h ((Ideal.absNorm I : ℝ) / X) else 0) =
      κ * (X : ℂ) * Vendor.originMellinH h 1 * P +
      z0 * h 0 * (∑ d ∈ idealDivisors m,
        (UniqueFactorizationMonoid.moebius d : ℂ)) +
      ∑ d ∈ idealDivisors m,
        (UniqueFactorizationMonoid.moebius d : ℂ) *
          ((X : ℂ) / (Ideal.absNorm d : ℂ)) *
          (∑' I : Ideal (𝓞 F), if I = ⊥ then 0 else
            T (X * (Ideal.absNorm I : ℝ) / (Ideal.absNorm d : ℝ))) := by
  have hg : Function.HasFiniteSupport (fun I : Ideal (𝓞 F) =>
      if I = ⊥ then (0 : ℂ) else h ((Ideal.absNorm I : ℝ) / X)) := by
    have heq : idealMellinWeight (fun _ : Ideal (𝓞 F) => (1 : ℂ)) h X =
        (fun I => if I = ⊥ then (0 : ℂ) else h ((Ideal.absNorm I : ℝ) / X)) := by
      funext I
      simp [idealMellinWeight]
    rw [← heq]
    exact idealMellinWeight_hasFiniteSupport (F := F) (fun _ => (1 : ℂ)) hcompact hX
  change (∑ᶠ I : Ideal (𝓞 F),
      if I ≠ ⊥ ∧ I ⊔ m = ⊤ then h ((Ideal.absNorm I : ℝ) / X) else 0) = _
  rw [PoissonCoprimeExact.coprimeFinsum_eq_moebiusMultiples
    (fun I => h ((Ideal.absNorm I : ℝ) / X)) hg m hm]
  calc
    _ = ∑ d ∈ idealDivisors m, (UniqueFactorizationMonoid.moebius d : ℂ) *
        (∑ᶠ I : Ideal (𝓞 F), if I = ⊥ then 0 else
          h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [PoissonCoprimeExact.multiplesFinsum_eq_scaledPrincipal
        h hcompact X hX d (ne_bot_of_mem_idealDivisors hd)]
    _ = _ := PoissonCoprimeExact.finite_scaled_principalPoisson
       F hF h hh hcompact X hX (idealDivisors m)
      (fun _ hd => ne_bot_of_mem_idealDivisors hd)
      (fun d => (UniqueFactorizationMonoid.moebius d : ℂ))

end DedekindZetaZeroFree.LargeSieve

end

end
