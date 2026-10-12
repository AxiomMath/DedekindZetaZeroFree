module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.Coefficients.RectangleEnvelopesAndEnergies

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma norm_one_le {a : Ideal (𝓞 F)} (ha : a ≠ ⊥) : 1 ≤ norm a := by
  unfold norm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha)

private lemma divisor_bin (X : ℝ) (hX : 1 ≤ 2 * X)
    {f : Ideal (𝓞 F)} (hf : f ≠ ⊥) (hfn : norm f ≤ 2 * X) :
    ∃ P ∈ ErrorRectangles.scales X,
      1 ≤ P ∧ P ≤ norm f ∧ ErrorRectangles.InBin P f := by
  have hf1 := norm_one_le hf
  have hex : ∃ j : ℕ, norm f ≤ (2 : ℝ) ^ j :=
    ⟨Vendor.dyadicLength (2 * max 1 X),
      hfn.trans ((mul_le_mul_of_nonneg_left (le_max_right 1 X) (by norm_num)).trans
        (Vendor.dyadicLength_cover _))⟩
  let j := Nat.find hex
  have hj : norm f ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ Vendor.dyadicLength (2 * max 1 X) := by
    apply Nat.find_min' hex
    exact hfn.trans ((mul_le_mul_of_nonneg_left (le_max_right 1 X) (by norm_num)).trans
      (Vendor.dyadicLength_cover _))
  cases hj0 : j with
  | zero =>
    refine ⟨1, Finset.mem_insert_self _ _, le_refl _, hf1, hf, ?_, ?_⟩
    · simp only [if_pos rfl]; exact hf1
    · have hle : norm f ≤ 1 := by simpa only [hj0, pow_zero] using hj
      linarith
  | succ k =>
    have hlow : (2 : ℝ) ^ k < norm f := by
      apply lt_of_not_ge
      exact Nat.find_min hex (by change k < j; omega)
    have hup : norm f ≤ 2 * (2 : ℝ) ^ k := by
      simpa only [hj0, pow_succ, mul_comm] using hj
    refine ⟨(2 : ℝ) ^ k, Finset.mem_insert_of_mem ?_,
      one_le_pow₀ (by norm_num), hlow.le, hf, ?_, hup⟩
    · apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
    · split_ifs <;> assumption

private lemma mobius_norm_bound (C : Context Q) (hn : 1 ≤ norm C.d)
    (e : Ideal (𝓞 F)) (he : e ∈ C.mobiusDivisors) :
    Real.sqrt (norm e) / norm C.d ≤ max 1 (norm c) := by
  have hc : c ≠ ⊥ := by simpa only [C.core] using C.D.bad_ne_bot
  have hcd : c * C.d ≠ ⊥ := mul_ne_zero hc C.hd0
  have hediv : e ∣ c * C.d := by
    have hrad0 : (c * C.d).radical ≠ ⊥ := by
      intro hh
      exact hcd (bot_unique (hh ▸ Ideal.le_radical))
    exact Ideal.dvd_iff_le.mpr (le_trans Ideal.le_radical
      (Ideal.dvd_iff_le.mp ((DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hrad0).mp he)))
  have hen : norm e ≤ norm c * norm C.d := by
    unfold norm
    rw [← Nat.cast_mul, ← map_mul]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr hcd)) (map_dvd Ideal.absNorm hediv)
  have hnpos : 0 < norm C.d := by linarith
  have hq : 1 ≤ max 1 (norm c) := le_max_left _ _
  have hqn : 1 ≤ max 1 (norm c) * norm C.d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hn)]
  have hle : norm e ≤ (max 1 (norm c) * norm C.d) ^ 2 := by
    have hle1 : norm c * norm C.d ≤ max 1 (norm c) * norm C.d :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hnpos.le
    nlinarith
  rw [div_le_iff₀ hnpos, Real.sqrt_le_left (by positivity)]
  exact hle

def ShortGeometry (C : Context Q) (B : ℝ) : Prop :=
  ∀ e ∈ C.mobiusDivisors, ∀ p ∈ C.pairs,
    ∀ f ∈ idealDivisors (p.1 * p.2), norm f ≤ C.Z1 B e →
      ∃ f₁ f₂ : Ideal (𝓞 F), f = f₁ * f₂ ∧ f₁ ∣ p.1 ∧ f₂ ∣ p.2 ∧
        ∃ P ∈ rectangles C B,
          ErrorRectangles.InBin P.1 f₁ ∧ ErrorRectangles.InBin P.2 f₂

theorem short_divisor_geometry (C : Context Q) (B : ℝ)
    (hM : 1 ≤ C.M) (hN : 1 ≤ C.N) (hδ : 0 < C.δ)
    (hB : 1 ≤ B) (hBK : B ≤ C.K) (hKM : C.K ≤ C.M)
    (hn : 1 ≤ norm C.d) (hnN : norm C.d ≤ 2 * C.N) :
    ShortGeometry C B := by
  intro e he p hp f hf hfZ
  obtain ⟨hcols, hpvalid⟩ := Finset.mem_filter.mp hp
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hcols
  have hp0 : p.1 * p.2 ≠ ⊥ := mul_ne_zero hpvalid.hu0 hpvalid.hv0
  have hfdiv := (mem_idealDivisors hp0).mp hf
  obtain ⟨f₁, f₂, hf₁, hf₂, hff⟩ := exists_dvd_and_dvd_of_dvd_mul hfdiv
  have hf0 := ne_bot_of_mem_idealDivisors hf
  have hf₁0 : f₁ ≠ ⊥ := by intro hh; simp [hh] at hff; exact hf0 hff
  have hf₂0 : f₂ ≠ ⊥ := by intro hh; simp [hh] at hff; exact hf0 hff
  have hpn (u : Ideal (𝓞 F)) (hu : u ∈ C.columns) :
      norm u ≤ 2 * C.N / norm C.d := by
    exact ((Sieve.mem_idealAdmissibleFinset _ _ _ _).mp
      (Finset.mem_filter.mp hu).1).2.2
  have hfn₁ : norm f₁ ≤ norm p.1 := by
    unfold norm
    exact_mod_cast absNorm_le_of_mem_idealDivisors ((mem_idealDivisors hpvalid.hu0).mpr hf₁)
  have hfn₂ : norm f₂ ≤ norm p.2 := by
    unfold norm
    exact_mod_cast absNorm_le_of_mem_idealDivisors ((mem_idealDivisors hpvalid.hv0).mpr hf₂)
  have hnpos : 0 < norm C.d := by linarith
  have hX : 1 ≤ 2 * (C.N / norm C.d) := by
    rw [← mul_div_assoc, le_div_iff₀ hnpos]
    simpa only [one_mul] using hnN
  obtain ⟨P₁, hP₁, hP₁1, hP₁f, hbin₁⟩ := divisor_bin (C.N / norm C.d) hX hf₁0
    (by simpa only [mul_div_assoc] using hfn₁.trans (hpn p.1 hu))
  obtain ⟨P₂, hP₂, hP₂1, hP₂f, hbin₂⟩ := divisor_bin (C.N / norm C.d) hX hf₂0
    (by simpa only [mul_div_assoc] using hfn₂.trans (hpn p.2 hv))
  refine ⟨f₁, f₂, hff, hf₁, hf₂, (P₁, P₂), ?_, hbin₁, hbin₂⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hP₁, hP₂⟩,
    hP₁1, hP₂1, hP₁f.trans (hfn₁.trans (hpn p.1 hu)),
    hP₂f.trans (hfn₂.trans (hpn p.2 hv)), p, hp, f₁, f₂, hf₁, hf₂, hbin₁, hbin₂⟩, ?_⟩
  have hprod : P₁ * P₂ ≤ norm f := by
    have hnorm : norm f = norm f₁ * norm f₂ := by
      rw [hff]; simp only [norm, map_mul, Nat.cast_mul]
    rw [hnorm]
    exact mul_le_mul hP₁f hP₂f (by linarith) (by linarith [norm_one_le hf₁0])
  have hMpos : 0 < C.M := by linarith
  have hNpos : 0 < C.N := by linarith
  have hspos : 0 < Real.sqrt (B * C.M) := Real.sqrt_pos.mpr (mul_pos (by linarith) hMpos)
  let x := C.N / Real.sqrt (B * C.M) * Real.rpow (C.M * C.N) C.δ
  let q := max 1 (norm c)
  have hx : 0 ≤ x := mul_nonneg (div_nonneg hNpos.le hspos.le)
    (Real.rpow_nonneg (mul_nonneg hMpos.le hNpos.le) _)
  have hq : 0 ≤ q := le_trans zero_le_one (le_max_left _ _)
  have heq : C.Z1 B e = x * (Real.sqrt (norm e) / norm C.d) := by
    dsimp [Context.Z1, x]; ring
  have hZ : C.Z1 B e ≤ x * q := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (mobius_norm_bound C hn e he) hx
  have hslack : x * q ≤ (8 * max 1 (norm c)) *
      (C.N / Real.sqrt (B * C.M)) * Real.rpow (C.M * C.N) C.δ := by
    change x * q ≤ 8 * q * (C.N / Real.sqrt (B * C.M)) * Real.rpow (C.M * C.N) C.δ
    calc x * q ≤ 8 * (x * q) := by nlinarith [mul_nonneg hx hq]
         _ = _ := by dsimp [x]; ring
  exact (hprod.trans hfZ).trans (hZ.trans hslack)

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.Origin

end
