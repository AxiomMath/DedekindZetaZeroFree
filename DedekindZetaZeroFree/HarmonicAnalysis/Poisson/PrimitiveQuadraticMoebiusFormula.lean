module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SigmaFourKernelsAndReindexing
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticRootNumber
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.NonprincipalHeckeSummation
public import DedekindZetaZeroFree.LFunctions.Hecke.LocalContinuationAndFunctionalEquations
public import DedekindZetaZeroFree.Arithmetic.Ideals.MoebiusCoprimality

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

private theorem sup_radical_eq_top_iff {F : Type} [Field F] [NumberField F]
    (I m : Ideal (𝓞 F)) : I ⊔ m.radical = ⊤ ↔ I ⊔ m = ⊤ := by
  constructor
  · intro h
    apply Ideal.radical_eq_top.mp
    have heq : (I ⊔ m).radical = (I ⊔ m.radical).radical := by
      calc
        (I ⊔ m).radical = (I.radical ⊔ m.radical).radical := Ideal.radical_sup I m
        _ = (I ⊔ m.radical).radical := by
          rw [Ideal.radical_sup I m.radical, Ideal.radical_idem]
    rw [heq, h, Ideal.radical_top]
  · intro h
    apply top_unique
    calc
      (⊤ : Ideal (𝓞 F)) = I ⊔ m := h.symm
      _ ≤ I ⊔ m.radical := sup_le_sup_left Ideal.le_radical _

private theorem finsum_ite_subtype {α : Type*} (p : α → Prop) [DecidablePred p] (g : α → ℂ) :
    (∑ᶠ a : α, if p a then g a else 0) = ∑ᶠ a : Subtype p, g a := by
  classical
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

private theorem multiples_character {F : Type} [Field F] [NumberField F]
    {f : Ideal (𝓞 F)} (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (h : ℝ → ℂ) (X : ℝ) (d : Ideal (𝓞 F)) (hd : d ≠ ⊥) :
    (∑ᶠ I : Ideal (𝓞 F), if I ≠ ⊥ ∧ d ∣ I then
      h ((Ideal.absNorm I : ℝ) / X) * η I else 0) =
      η d * ∑ᶠ I : Ideal (𝓞 F), idealMellinWeight η.toFun h
        (X / (Ideal.absNorm d : ℝ)) I := by
  classical
  let e : {J : Ideal (𝓞 F) // J ≠ ⊥} → {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ d ∣ I} :=
    fun J => ⟨d * J.val, mul_ne_zero hd J.2, ⟨J.val, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro J₁ J₂ hJ
      exact Subtype.ext (mul_left_cancel₀ hd (congrArg Subtype.val hJ))
    · intro I
      obtain ⟨J, hJ⟩ := I.2.2
      refine ⟨⟨J, fun hbot => I.2.1 ?_⟩, Subtype.ext hJ.symm⟩
      rw [hJ, hbot, Ideal.mul_bot]
  have hNd : (Ideal.absNorm d : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hd)
  rw [finsum_ite_subtype (fun I : Ideal (𝓞 F) => I ≠ ⊥ ∧ d ∣ I)
    (fun I => h ((Ideal.absNorm I : ℝ) / X) * η I)]
  rw [mul_finsum]
  have hr : (fun I : Ideal (𝓞 F) => η d * idealMellinWeight η.toFun h
      (X / (Ideal.absNorm d : ℝ)) I) =
      (fun I => if I ≠ ⊥ then η d * (η I *
        h ((Ideal.absNorm I : ℝ) / (X / (Ideal.absNorm d : ℝ)))) else 0) := by
    funext I; by_cases hI : I = ⊥ <;> simp [idealMellinWeight, hI]
  rw [hr, finsum_ite_subtype]
  symm
  apply finsum_eq_of_bijective e he
  intro J
  change η d * (η J.val * h ((Ideal.absNorm J.val : ℝ) /
    (X / (Ideal.absNorm d : ℝ)))) =
    h ((Ideal.absNorm (d * J.val) : ℝ) / X) * η (d * J.val)
  rw [η.map_mul', map_mul, Nat.cast_mul]
  have harg : (Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ)) =
      (Ideal.absNorm d : ℝ) * (Ideal.absNorm J.val : ℝ) / X := by field_simp
  rw [harg]; ring

theorem S4all_primitive_mobius_poisson
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    {m f : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hprim : η.IsPrimitive)
    (hquad : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hnonprincipal : ¬ η.IsPrincipal)
    (h : ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (hcompact : HasCompactSupport h)
    {X : ℝ} (hX : 0 < X) :
    let dotH := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
      (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) h
    Summable (fun I : Ideal (𝓞 F) => ‖S4allTerm m h X η I‖) ∧
    (∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m.radical,
      Summable (fun I : Ideal (𝓞 F) =>
        ‖S4allTerm ⊤ dotH
          ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) η I‖)) ∧
    S4all m h X η =
      ∑ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m.radical,
        (UniqueFactorizationMonoid.moebius e : ℂ) * η e *
          ((X : ℂ) /
            ((Ideal.absNorm e : ℂ) * (Real.sqrt (Ideal.absNorm f : ℝ) : ℂ))) *
          S4all ⊤ dotH ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) η := by
  classical
  dsimp only
  let dotH := DedekindZetaZeroFree.LargeSieve.fieldTransform (DedekindZetaZeroFree.LargeSieve.principalDiscriminant F)
    (DedekindZetaZeroFree.LargeSieve.principalComplexPlaces F) h
  obtain ⟨w⟩ := DedekindZetaZeroFree.LargeSieve.exists_entireHeckeWitness hF hf η hprim hnonprincipal
  have hW : w.W = 1 :=
    (DedekindZetaZeroFree.LargeSieve.quadratic_entireHeckeWitness_root_number
       hF hf η hprim hquad hnonprincipal w).2.1
  have hNf : 0 < (Ideal.absNorm f : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hf)
  have hp : ∀ e ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors m.radical,
      Summable (fun I : Ideal (𝓞 F) => ‖S4allTerm ⊤ dotH
        ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) η I‖) ∧
      (∑ᶠ I : Ideal (𝓞 F), DedekindZetaZeroFree.LargeSieve.idealMellinWeight η.toFun h
        (X / (Ideal.absNorm e : ℝ)) I) =
        ((X : ℂ) / ((Ideal.absNorm e : ℂ) *
          (Real.sqrt (Ideal.absNorm f : ℝ) : ℂ))) *
        S4all ⊤ dotH ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) η := by
    intro e he
    have hNe : 0 < (Ideal.absNorm e : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors he))
    obtain ⟨habs, hsum, hpoisson⟩ := DedekindZetaZeroFree.LargeSieve.nonprincipalPoisson_of_witness
      hF f hf η w h hh hcompact (X / (Ideal.absNorm e : ℝ)) (div_pos hX hNe)
    have hterms : (fun I : Ideal (𝓞 F) =>
        if I = ⊥ then 0 else (starRingEnd ℂ) (η I) *
          DedekindZetaZeroFree.LargeSieve.fieldTransform (((|NumberField.discr F| : ℤ) : ℝ))
            (NumberField.InfinitePlace.nrComplexPlaces F) h
            ((X / (Ideal.absNorm e : ℝ)) * (Ideal.absNorm I : ℝ) /
              (Ideal.absNorm f : ℝ))) =
        (fun I => S4allTerm ⊤ dotH
          ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) η I) := by
      funext I
      by_cases hI : I = ⊥
      · simp [S4allTerm, hI]
      · have harg : (X / (Ideal.absNorm e : ℝ)) * (Ideal.absNorm I : ℝ) /
            (Ideal.absNorm f : ℝ) =
            (Ideal.absNorm I : ℝ) /
              ((Ideal.absNorm e : ℝ) * (Ideal.absNorm f : ℝ) / X) := by
          field_simp
        simp only [hI, if_false, S4allTerm, ne_eq, not_false_eq_true,
          sup_top_eq, and_self, if_true, DedekindZetaZeroFree.LargeSieve.rayClassCharacter_conj_of_cube_eq_self hquad]
        rw [harg]
        exact mul_comm _ _
    rw [hterms] at hsum hpoisson
    refine ⟨habs.congr (fun I => congrArg norm (congrFun hterms I)), ?_⟩
    rw [hW] at hpoisson
    simpa [S4all, Complex.ofReal_div, Complex.ofReal_natCast, one_mul, div_div] using hpoisson
  refine ⟨summable_of_hasFiniteSupport
    ((finite_support_S4allTerm h hcompact hX η).subset (by
      intro I hI
      simpa only [Function.mem_support, norm_ne_zero_iff] using hI)),
    fun e he => (hp e he).1, ?_⟩
  have hrad : m.radical ≠ ⊥ := by
    intro hzero
    exact hm (bot_unique (hzero ▸ Ideal.le_radical))
  have hg : Function.HasFiniteSupport (fun I : Ideal (𝓞 F) => if I = ⊥ then 0 else
      h ((Ideal.absNorm I : ℝ) / X) * η I) := by
    have ht := DedekindZetaZeroFree.LargeSieve.idealMellinWeight_hasFiniteSupport (F := F) η.toFun hcompact hX
    have heq : (fun I : Ideal (𝓞 F) => if I = ⊥ then 0 else
        h ((Ideal.absNorm I : ℝ) / X) * η I) = DedekindZetaZeroFree.LargeSieve.idealMellinWeight η.toFun h X := by
      funext I; simp only [DedekindZetaZeroFree.LargeSieve.idealMellinWeight]; split_ifs <;> ring
    rw [heq]; exact ht
  rw [S4all, tsum_eq_finsum (finite_support_S4allTerm h hcompact hX η)]
  have hsrc : (fun I : Ideal (𝓞 F) => S4allTerm m h X η I) =
      (fun I => if I ≠ ⊥ ∧ I ⊔ m.radical = ⊤ then
        h ((Ideal.absNorm I : ℝ) / X) * η I else 0) := by
    funext I
    simp only [S4allTerm, sup_radical_eq_top_iff]
  rw [hsrc, DedekindZetaZeroFree.LargeSieve.PoissonCoprimeExact.coprimeFinsum_eq_moebiusMultiples
    (fun I => h ((Ideal.absNorm I : ℝ) / X) * η I) hg m.radical hrad]
  apply Finset.sum_congr rfl
  intro e he
  rw [multiples_character η h X e (DedekindZetaZeroFree.LargeSieve.ne_bot_of_mem_idealDivisors he), (hp e he).2]
  ring

end DedekindZetaZeroFree.LargeSieve.Bilinear

end
