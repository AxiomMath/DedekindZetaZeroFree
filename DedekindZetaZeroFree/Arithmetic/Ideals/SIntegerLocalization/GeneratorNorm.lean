module

public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.GeneratorValuation

@[expose] public section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SIntegerLocalization
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private theorem exponent_eq_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hext : I ⊔ (∏ v ∈ S, v.asIdeal) = ⊤)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) : idealPrimeExponent v.asIdeal I = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hf
  have hle := (Ideal.mem_normalizedFactors_iff hI).mp hf |>.2
  have hs : (∏ w ∈ S, w.asIdeal) ≤ v.asIdeal := v.isPrime.prod_le.mpr ⟨v, hv, le_rfl⟩
  exact v.isPrime.ne_top (top_le_iff.mp (hext ▸ sup_le hle hs))

theorem finite_norm_compensation (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hext : I ⊔ (∏ v ∈ S, v.asIdeal) = ⊤)
    (r : (S : Set (HeightOneSpectrum (𝓞 F))).integer F) (hr : r ≠ 0)
    (hspan : Ideal.span {r} = Ideal.map (algebraMap (𝓞 F) _) I) :
    (∏ᶠ w : FinitePlace F, w (r : F)) * (Ideal.absNorm I : ℝ) =
      ∏ v : S, HeightOneSpectrum.adicAbv F v.val (r : F) := by
  let f (v : HeightOneSpectrum (𝓞 F)) : ℝ := HeightOneSpectrum.adicAbv F v (r : F)
  let g (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
    (Ideal.absNorm (v.maxPowDividing I) : ℝ)
  have hf : f.HasFiniteMulSupport := by
    have hh := FinitePlace.hasFiniteMulSupport (fun h => hr (Subtype.ext h))
    have heq : Function.mulSupport f =
        FinitePlace.equivHeightOneSpectrum.symm ⁻¹' (Function.mulSupport fun w : FinitePlace F => w (r : F)) := by
      ext v
      simp only [Set.mem_preimage, Function.mem_mulSupport, f,
        FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
    rw [Function.HasFiniteMulSupport, heq]
    exact hh.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)
  have hg : g.HasFiniteMulSupport := by
    apply (Ideal.finite_factors hI).subset
    intro v hv
    by_contra hn
    have hzero : idealPrimeExponent v.asIdeal I = 0 := by
      apply Multiset.count_eq_zero.mpr
      exact fun h => hn (Ideal.mem_normalizedFactors_iff hI |>.mp h |>.2 |> Ideal.dvd_iff_le.mpr)
    apply hv
    change g v = 1
    simp only [g, HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count _ hI]
    change (Ideal.absNorm (v.asIdeal ^ idealPrimeExponent v.asIdeal I) : ℝ) = 1
    rw [hzero, pow_zero]
    simp
  have hgnorm : ∏ᶠ v, g v = (Ideal.absNorm I : ℝ) := by
    have hmap := ((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) (fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I)
    rw [Ideal.finprod_heightOneSpectrum_factorization hI] at hmap
    exact hmap.symm
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  change (∏ᶠ v, f v) * (Ideal.absNorm I : ℝ) = _
  rw [← hgnorm, ← finprod_mul_distrib hf hg]
  have hgone (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) : g v = 1 := by
    simp only [g, HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count _ hI]
    change (Ideal.absNorm (v.asIdeal ^ idealPrimeExponent v.asIdeal I) : ℝ) = 1
    rw [exponent_eq_zero S I hI hext v hv, pow_zero]
    simp
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) : f v * g v = 1 := by
    change HeightOneSpectrum.adicAbv F v (r : F) *
      (Ideal.absNorm (v.maxPowDividing I) : ℝ) = 1
    rw [HeightOneSpectrum.adicAbv_def, generator_valuation S I hI r hr hspan v hv,
      HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count _ hI]
    simp only [map_pow, Nat.cast_pow]
    rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp [idealPrimeExponent])]
    simp only [NNReal.coe_zpow]
    change (Ideal.absNorm v.asIdeal : ℝ) ^ (-(idealPrimeExponent v.asIdeal I : ℤ)) *
      (Ideal.absNorm v.asIdeal : ℝ) ^ idealPrimeExponent v.asIdeal I = 1
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀]
    exact pow_ne_zero _ (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  · rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [hgone v.val v.property, mul_one, f]
  · intro v hv
    by_contra hn
    exact hv (hout v hn)

theorem generator_norm (S : Finset (HeightOneSpectrum (𝓞 F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hext : I ⊔ (∏ v ∈ S, v.asIdeal) = ⊤)
    (r : (S : Set (HeightOneSpectrum (𝓞 F))).integer F) (hr : r ≠ 0)
    (hspan : Ideal.span {r} = Ideal.map (algebraMap (𝓞 F) _) I) :
    (∏ w : InfinitePlace F, w (r : F) ^ w.mult) *
      (∏ v : S, HeightOneSpectrum.adicAbv F v.val (r : F)) = (Ideal.absNorm I : ℝ) := by
  have hprod := NumberField.prod_abs_eq_one (fun h => hr (Subtype.ext h))
  rw [← finite_norm_compensation S I hI hext r hr hspan,
    ← mul_assoc, hprod, one_mul]

end
end DedekindZetaZeroFree.SIntegerLocalization
