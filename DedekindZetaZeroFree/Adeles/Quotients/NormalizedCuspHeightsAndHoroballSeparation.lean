module

public import DedekindZetaZeroFree.Geometry.HyperbolicActionMetricAndVolume

@[expose] public section

noncomputable section

open scoped Classical nonZeroDivisors

namespace DedekindZetaZeroFree.KPCusp

def complexPlace (F : Type*) [Field F] [NumberField F]
    (i : Fin (NumberField.InfinitePlace.nrComplexPlaces F)) :
    NumberField.InfinitePlace F :=
  ((Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}).symm i).val

end DedekindZetaZeroFree.KPCusp

end

section

noncomputable section
open scoped Classical nonZeroDivisors

namespace DedekindZetaZeroFree.KPCusp

abbrev Row (F : Type*) [Field F] := {r : F × F // r ≠ 0}

def scaleRow (F : Type*) [Field F] (a : Fˣ) (r : Row F) : Row F :=
  ⟨(a : F) • r.val, smul_ne_zero (Units.ne_zero a) r.property⟩

def flag (F : Type*) [Field F] (r : Row F) : Submodule F (F × F) :=
  LinearMap.ker
    ({ toFun := fun v => r.val.1 * v.1 + r.val.2 * v.2
       map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add]; ring
       map_smul' := by
         intros
         simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
         ring } : (F × F) →ₗ[F] F)

def content (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (r : Row F) :
    FractionalIdeal (NumberField.RingOfIntegers F)⁰ F :=
  FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ r.val.1 +
    FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ r.val.2 * J

def rowDenominator (F : Type*) [Field F] [NumberField F] (r : Row F)
    (i : Fin (NumberField.InfinitePlace.nrComplexPlaces F)) (z : KPArch.H3) : ℝ :=
  ‖(complexPlace F i).embedding r.val.1 * z.1 +
      (complexPlace F i).embedding r.val.2‖ ^ 2 +
    ‖(complexPlace F i).embedding r.val.1‖ ^ 2 * KPArch.height z ^ 2

def normalizedHeight (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (r : Row F)
    (z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) : ℝ :=
  (FractionalIdeal.absNorm (content F J r) : ℝ) *
    (∏ i, KPArch.height (z i)) / (∏ i, rowDenominator F r i (z i))

def horoball (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (r : Row F) (T : ℝ) :
    Set (KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) :=
  {z | T < normalizedHeight F J r z}

private theorem content_ne_zero (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (r : Row F) : content F J r ≠ 0 := by
  intro h
  change _ + _ = 0 at h
  rw [← FractionalIdeal.sup_eq_add] at h
  have hs := sup_eq_bot_iff.mp h
  have hc : r.val.1 = 0 := FractionalIdeal.spanSingleton_eq_zero_iff.mp hs.1
  have hd : r.val.2 = 0 := FractionalIdeal.spanSingleton_eq_zero_iff.mp
    ((mul_eq_zero.mp hs.2).resolve_right hJ)
  exact r.property (Prod.ext hc hd)

private theorem rowDenominator_pos (F : Type*) [Field F] [NumberField F]
    (r : Row F) (i : Fin (NumberField.InfinitePlace.nrComplexPlaces F))
    (z : KPArch.H3) : 0 < rowDenominator F r i z := by
  have hy : 0 < KPArch.height z := Real.exp_pos _
  by_cases hc : r.val.1 = 0
  · have hd : r.val.2 ≠ 0 := by
      intro hd
      exact r.property (Prod.ext hc hd)
    have hd' : (complexPlace F i).embedding r.val.2 ≠ 0 :=
      (map_ne_zero (complexPlace F i).embedding).mpr hd
    simpa [rowDenominator, hc] using sq_pos_of_pos (norm_pos_iff.mpr hd')
  · have hc' : (complexPlace F i).embedding r.val.1 ≠ 0 := (map_ne_zero (complexPlace F i).embedding).mpr hc
    exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hc')) (sq_pos_of_pos hy))

theorem normalizedHeight_pos (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (r : Row F) (z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) :
    0 < normalizedHeight F J r z := by
  have hn : 0 < FractionalIdeal.absNorm (content F J r) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm
      (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (content_ne_zero F J hJ r)))
  unfold normalizedHeight
  exact div_pos (mul_pos (by exact_mod_cast hn)
    (Finset.prod_pos fun i _ => Real.exp_pos _))
    (Finset.prod_pos fun i _ => rowDenominator_pos F r i (z i))

private theorem complex_norm_product (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (x : F) :
    (∏ i, ‖(complexPlace F i).embedding x‖ ^ 2) = (|Algebra.norm ℚ x| : ℝ) := by
  letI : NumberField.IsTotallyComplex F := NumberField.nrRealPlaces_eq_zero_iff.mp hF
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
  simp only [NumberField.IsTotallyComplex.mult_eq]
  let e : Fin (NumberField.InfinitePlace.nrComplexPlaces F) ≃ NumberField.InfinitePlace F :=
    (Fintype.equivFin {w : NumberField.InfinitePlace F // w.IsComplex}).symm.trans
      (Equiv.subtypeUnivEquiv fun w => NumberField.IsTotallyComplex.isComplex w)
  exact Fintype.prod_equiv e _ _ (fun i => by
    simp [e, complexPlace, NumberField.InfinitePlace.norm_embedding_eq])

private theorem content_scale (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (a : Fˣ) (r : Row F) : content F J (scaleRow F a r) =
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ (a : F) * content F J r := by
  simp only [content, scaleRow, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_add, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]

private theorem rowDenominator_scale (F : Type*) [Field F] [NumberField F]
    (a : Fˣ) (r : Row F) (i : Fin (NumberField.InfinitePlace.nrComplexPlaces F))
    (z : KPArch.H3) : rowDenominator F (scaleRow F a r) i z =
      ‖(complexPlace F i).embedding (a : F)‖ ^ 2 * rowDenominator F r i z := by
  simp only [rowDenominator, scaleRow, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    map_mul]
  rw [show (complexPlace F i).embedding (a : F) * (complexPlace F i).embedding r.val.1 * z.1 +
      (complexPlace F i).embedding (a : F) * (complexPlace F i).embedding r.val.2 =
      (complexPlace F i).embedding (a : F) *
        ((complexPlace F i).embedding r.val.1 * z.1 + (complexPlace F i).embedding r.val.2) by ring]
  simp only [norm_mul]
  ring

theorem normalizedHeight_scale (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (a : Fˣ) (r : Row F)
    (z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) :
    normalizedHeight F J (scaleRow F a r) z = normalizedHeight F J r z := by
  have hn : (|Algebra.norm ℚ (a : F)| : ℝ) ≠ 0 := by
    simp only [ne_eq, abs_eq_zero, Rat.cast_eq_zero, Algebra.norm_eq_zero_iff]
    exact a.ne_zero
  simp only [normalizedHeight, content_scale, map_mul,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, rowDenominator_scale,
    Finset.prod_mul_distrib, complex_norm_product F hF]
  rw [Rat.cast_abs, mul_assoc, mul_div_mul_left _ _ hn]

private theorem row_proportional (F : Type*) [Field F] (r r' : Row F)
    (hq : flag F r = flag F r') : ∃ a : Fˣ, r' = scaleRow F a r := by
  have hv : (-r.val.2, r.val.1) ∈ flag F r := by
    change r.val.1 * (-r.val.2) + r.val.2 * r.val.1 = 0
    ring
  rw [hq] at hv
  change r'.val.1 * (-r.val.2) + r'.val.2 * r.val.1 = 0 at hv
  by_cases hc : r.val.1 = 0
  · have hd : r.val.2 ≠ 0 := by
      intro hd
      exact r.property (Prod.ext hc hd)
    have hc' : r'.val.1 = 0 := by
      simpa [hc, hd] using hv
    have hd' : r'.val.2 ≠ 0 := by
      intro hd'
      exact r'.property (Prod.ext hc' hd')
    refine ⟨Units.mk0 (r'.val.2 / r.val.2) (div_ne_zero hd' hd), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [scaleRow, hc, hc']
    · simp [scaleRow, div_mul_cancel₀ _ hd]
  · have hc' : r'.val.1 ≠ 0 := by
      intro hc'
      have hd' : r'.val.2 = 0 := by simpa [hc', hc] using hv
      exact r'.property (Prod.ext hc' hd')
    refine ⟨Units.mk0 (r'.val.1 / r.val.1) (div_ne_zero hc' hc), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp [scaleRow, div_mul_cancel₀ _ hc]
    · simp only [scaleRow, Prod.smul_snd, smul_eq_mul, Units.val_mk0]
      field_simp
      linear_combination hv

theorem normalizedHeight_eq_of_flag_eq (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (r r' : Row F) (hq : flag F r = flag F r')
    (z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) :
    normalizedHeight F J r z = normalizedHeight F J r' z := by
  obtain ⟨a, rfl⟩ := row_proportional F r r' hq
  exact (normalizedHeight_scale F hF J a r z).symm

private theorem gram (a b c d : ℂ) : ‖a * d - b * c‖ ^ 2 ≤
    (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h := Complex.normSq_nonneg (a * star c + b * star d)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at *
  nlinarith
private theorem rowDenominator_product_lower_bound (F : Type*) [Field F] [NumberField F] (r r' : Row F)
    (i : Fin (NumberField.InfinitePlace.nrComplexPlaces F)) (z : KPArch.H3) :
    ‖(complexPlace F i).embedding (r.val.1 * r'.val.2 - r.val.2 * r'.val.1)‖ ^ 2 *
      KPArch.height z ^ 2 ≤ rowDenominator F r i z * rowDenominator F r' i z := by
  let e := (complexPlace F i).embedding
  have h := gram (e r.val.1 * z.1 + e r.val.2)
    (e r.val.1 * (KPArch.height z : ℂ))
    (e r'.val.1 * z.1 + e r'.val.2)
    (e r'.val.1 * (KPArch.height z : ℂ))
  have he : (e r.val.1 * z.1 + e r.val.2) * (e r'.val.1 * (KPArch.height z : ℂ)) -
      (e r.val.1 * (KPArch.height z : ℂ)) * (e r'.val.1 * z.1 + e r'.val.2) =
      -(e (r.val.1 * r'.val.2 - r.val.2 * r'.val.1) * (KPArch.height z : ℂ)) := by
    simp only [map_sub, map_mul]
    ring
  rw [he] at h
  simpa only [rowDenominator, e, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos z.2), KPArch.height, mul_pow] using h

private theorem norm_antitone (F : Type*) [Field F] [NumberField F]
    {I J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F}
    (hI : I ≠ 0) (h : I ≤ J) : FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := fun hj => hI (le_antisymm (hj ▸ h) bot_le)
  have hh : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' h le_rfl
         _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨K, hK⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hh
  have hK0 : K ≠ ⊥ := by
    intro hk
    have : I * J⁻¹ = 0 := by simpa [hk] using hK.symm
    exact (mul_ne_zero hI (inv_ne_zero hJ)) this
  have hn : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hK, FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hK0)
  have hjpos : 0 < FractionalIdeal.absNorm J :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J)
      (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hJ))
  rw [map_mul, map_inv₀, ← div_eq_mul_inv] at hn
  simpa only [one_mul] using (le_div_iff₀ hjpos).mp hn

private theorem determinant_ne_zero (F : Type*) [Field F] (r r' : Row F)
    (hq : flag F r ≠ flag F r') : r.val.1 * r'.val.2 - r.val.2 * r'.val.1 ≠ 0 := by
  intro hd
  apply hq
  by_cases hc : r.val.1 = 0
  · have hr : r.val.2 ≠ 0 := fun h => r.property (Prod.ext hc h)
    have hc' : r'.val.1 = 0 := by simpa [hc, hr] using hd
    have hr' : r'.val.2 ≠ 0 := fun h => r'.property (Prod.ext hc' h)
    ext v
    change (r.val.1 * v.1 + r.val.2 * v.2 = 0) ↔
      (r'.val.1 * v.1 + r'.val.2 * v.2 = 0)
    simp [hc, hc', hr, hr']
  · have hc' : r'.val.1 ≠ 0 := by
      intro hh
      have h2 : r'.val.2 = 0 := by simpa [hh, hc] using hd
      exact r'.property (Prod.ext hh h2)
    ext v
    change (r.val.1 * v.1 + r.val.2 * v.2 = 0) ↔
      (r'.val.1 * v.1 + r'.val.2 * v.2 = 0)
    have he : r.val.1 * (r'.val.1 * v.1 + r'.val.2 * v.2) =
        r'.val.1 * (r.val.1 * v.1 + r.val.2 * v.2) := by
      linear_combination v.2 * hd
    constructor
    · intro hv
      have hz : r.val.1 * (r'.val.1 * v.1 + r'.val.2 * v.2) = 0 := by rw [he, hv, mul_zero]
      exact (mul_eq_zero.mp hz).resolve_left hc
    · intro hv
      have hz : r'.val.1 * (r.val.1 * v.1 + r.val.2 * v.2) = 0 := by rw [← he, hv, mul_zero]
      exact (mul_eq_zero.mp hz).resolve_left hc'

private theorem determinant_content_le (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (r r' : Row F) :
    FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰
      (r.val.1 * r'.val.2 - r.val.2 * r'.val.1) * J ≤ content F J r * content F J r' := by
  apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
  intro v hv
  have hc : ∀ s : Row F, s.val.1 ∈ content F J s := by
    intro s
    exact (show FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ s.val.1 ≤ content F J s from
      by unfold content; rw [← FractionalIdeal.sup_eq_add]; exact le_sup_left)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hd : ∀ s : Row F, s.val.2 * v ∈ content F J s := by
    intro s
    apply (show FractionalIdeal.spanSingleton (NumberField.RingOfIntegers F)⁰ s.val.2 * J ≤ content F J s from
      by unfold content; rw [← FractionalIdeal.sup_eq_add]; exact le_sup_right)
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hv
  have h1 := FractionalIdeal.mul_mem_mul (hc r) (hd r')
  have h2 := FractionalIdeal.mul_mem_mul (hd r) (hc r')
  have hs := Submodule.sub_mem (content F J r * content F J r').val h1 h2
  change r.val.1 * (r'.val.2 * v) - r.val.2 * v * r'.val.1 ∈ content F J r * content F J r' at hs
  convert hs using 1 <;> ring

theorem normalizedHeight_product_le_norm_twist (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (r r' : Row F) (hq : flag F r ≠ flag F r')
    (z : KPArch.Space (NumberField.InfinitePlace.nrComplexPlaces F)) :
    normalizedHeight F J r z * normalizedHeight F J r' z ≤
      (FractionalIdeal.absNorm J : ℝ) := by
  let δ := r.val.1 * r'.val.2 - r.val.2 * r'.val.1
  have hδ : δ ≠ 0 := determinant_ne_zero F r r' hq
  have hn := norm_antitone F
    (mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hδ) hJ)
    (determinant_content_le F J r r')
  simp only [map_mul, FractionalIdeal.absNorm_span_singleton] at hn
  have hnR : (FractionalIdeal.absNorm (content F J r) : ℝ) *
      (FractionalIdeal.absNorm (content F J r') : ℝ) ≤
      (|Algebra.norm ℚ δ| : ℝ) * (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast hn
  have hg : (|Algebra.norm ℚ δ| : ℝ) * (∏ i, KPArch.height (z i)) ^ 2 ≤
      (∏ i, rowDenominator F r i (z i)) * (∏ i, rowDenominator F r' i (z i)) := by
    rw [← complex_norm_product F hF δ, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun i _ => rowDenominator_product_lower_bound F r r' i (z i))
  have hd : 0 < (∏ i, rowDenominator F r i (z i)) :=
    Finset.prod_pos fun i _ => rowDenominator_pos F r i (z i)
  have hd' : 0 < (∏ i, rowDenominator F r' i (z i)) :=
    Finset.prod_pos fun i _ => rowDenominator_pos F r' i (z i)
  have hj : 0 ≤ (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  unfold normalizedHeight
  rw [div_mul_div_comm, div_le_iff₀ (mul_pos hd hd')]
  calc
    _ = ((FractionalIdeal.absNorm (content F J r) : ℝ) *
        (FractionalIdeal.absNorm (content F J r') : ℝ)) *
        (∏ i, KPArch.height (z i)) ^ 2 := by ring
    _ ≤ ((|Algebra.norm ℚ δ| : ℝ) * (FractionalIdeal.absNorm J : ℝ)) *
        (∏ i, KPArch.height (z i)) ^ 2 := mul_le_mul_of_nonneg_right hnR (sq_nonneg _)
    _ = (FractionalIdeal.absNorm J : ℝ) *
        ((|Algebra.norm ℚ δ| : ℝ) * (∏ i, KPArch.height (z i)) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hj

end DedekindZetaZeroFree.KPCusp

end
end
