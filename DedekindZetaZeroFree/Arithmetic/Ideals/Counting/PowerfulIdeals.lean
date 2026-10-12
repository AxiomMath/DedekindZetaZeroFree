module

public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries
public import DedekindZetaZeroFree.Arithmetic.Ideals.PowerfulSquarefreeFactorization

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def normPowerfulIdeals (F : Type) [Field F] [NumberField F] (X : ℝ) :
    Set (NonzeroIdeal F) :=
  { h | Powerful h.val ∧ idealNorm h.val < X }

def exteriorPowerfulDyad (cS : Ideal (𝓞 F)) (P : ℝ) : Set (ExteriorIdeal cS) :=
  { h | Powerful h.val ∧ P ≤ idealNorm h.val ∧ idealNorm h.val < 2 * P }

theorem normPowerfulIdeals_finite (F : Type) [Field F] [NumberField F] (X : ℝ) :
    (normPowerfulIdeals F X).Finite := by
  exact (normBoundedIdeals_finite F X).subset (fun _ h => h.2.le)

theorem exteriorPowerfulDyad_finite (cS : Ideal (𝓞 F)) (P : ℝ) :
    (exteriorPowerfulDyad cS P).Finite := by
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun h => ⟨h.val, h.property.1⟩
  apply Set.Finite.of_injOn (f := f) (t := normPowerfulIdeals F (2 * P))
  · intro h hh
    exact ⟨hh.1, hh.2.2⟩
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun h : NonzeroIdeal F => h.val) hab)
  · exact normPowerfulIdeals_finite F (2 * P)

private theorem powerful_norm_factor (r s : NonzeroIdeal F) :
    idealNorm (r.val ^ 2 * s.val ^ 3) = idealNorm r.val ^ 2 * idealNorm s.val ^ 3 := by
  simp [idealNorm, map_mul, map_pow]

private theorem powerful_cutoff_eq (X q : ℝ) (hX : 0 ≤ X) (hq : 0 < q) :
    Real.sqrt (X / q ^ 3) = Real.sqrt X * Real.rpow q (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_div hX, Real.sqrt_eq_rpow (q ^ 3),
    ← Real.rpow_natCast q 3, ← Real.rpow_mul hq.le]
  norm_num
  rw [Real.rpow_neg hq.le]
  simp [div_eq_mul_inv]

private theorem powerful_factor_norm_le (r s : NonzeroIdeal F) (X : ℝ)
    (hX : 0 ≤ X) (h : idealNorm (r.val ^ 2 * s.val ^ 3) < X) :
    idealNorm r.val ≤ Real.sqrt (X / idealNorm s.val ^ 3) := by
  have hr := idealNorm_ge_one r.val r.property
  have hs := idealNorm_ge_one s.val s.property
  apply (Real.le_sqrt (by linarith) (div_nonneg hX (by positivity))).2
  apply (le_div_iff₀ (by positivity : 0 < idealNorm s.val ^ 3)).2
  exact (powerful_norm_factor r s ▸ h).le

def powerfulFactors (h : NonzeroIdeal F) : NonzeroIdeal F × NonzeroIdeal F :=
  if hp : Powerful h.val then
    (unique_powerful_square_cube_decomposition h.val h.property hp).exists.choose
  else (⟨⊤, by simp⟩, ⟨⊤, by simp⟩)

private theorem powerfulFactors_spec (h : NonzeroIdeal F) (hp : Powerful h.val) :
    h.val = (powerfulFactors h).1.val ^ 2 * (powerfulFactors h).2.val ^ 3 := by
  simpa [powerfulFactors, hp] using
    ((unique_powerful_square_cube_decomposition h.val h.property hp).exists.choose_spec).1

private theorem powerfulFactors_inj (X : ℝ) :
    Set.InjOn (powerfulFactors (F := F)) (normPowerfulIdeals F X) := by
  intro a ha b hb hab
  apply Subtype.ext
  rw [powerfulFactors_spec a ha.1, powerfulFactors_spec b hb.1, hab]

theorem powerful_ideal_count_bound (F : Type) [Field F] [NumberField F] :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ((normPowerfulIdeals F X).ncard : ℝ) ≤ K * Real.sqrt X := by
  obtain ⟨C, C', hC, _, hcounts⟩ := ideal_counting_harmonic_bounds F
  have hc : ∀ Y : ℝ, 0 ≤ Y →
      ((normBoundedIdeals F Y).ncard : ℝ) ≤ C * Y := by
    intro Y hY
    by_cases h : 1 ≤ Y
    · simpa using (hcounts Set.univ).1 Y h
    · have he : normBoundedIdeals F Y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro r hr
        exact h ((idealNorm_ge_one r.val r.property).trans hr)
      rw [he, Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg hC.le hY
  let w : NonzeroIdeal F → ℝ := fun s => Real.rpow (idealNorm s.val) (-(3 / 2 : ℝ))
  have hw : Summable w := ideal_norm_rpow_summable F (3 / 2) (by norm_num)
  have hw0 : ∀ s, 0 ≤ w s := fun s => Real.rpow_nonneg
    (le_trans (by norm_num) (idealNorm_ge_one s.val s.property)) _
  have hsum : 0 ≤ ∑' s, w s := tsum_nonneg hw0
  refine ⟨C * ((∑' s, w s) + 1), mul_pos hC (by linarith), ?_⟩
  intro X hX
  have hX0 : 0 ≤ X := by linarith
  let a := (normPowerfulIdeals_finite F X).toFinset
  let t := a.image (powerfulFactors (F := F))
  have ht : ∀ rs ∈ t, idealNorm (rs.1.val ^ 2 * rs.2.val ^ 3) < X := by
    intro rs hrs
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hrs
    have hh' : h ∈ normPowerfulIdeals F X := by simpa [a] using hh
    rw [← powerfulFactors_spec h hh'.1]
    exact hh'.2
  have hcard : (normPowerfulIdeals F X).ncard = t.card := by
    rw [Finset.card_image_of_injOn]
    · exact Set.ncard_eq_toFinset_card _ (normPowerfulIdeals_finite F X)
    · simpa [a] using powerfulFactors_inj (F := F) X
  have hfiber : ∀ s ∈ t.image Prod.snd,
      ((t.filter (fun rs => rs.2 = s)).card : ℝ) ≤ C * Real.sqrt X * w s := by
    intro s _
    let u := t.filter (fun rs => rs.2 = s)
    let Y := Real.sqrt (X / idealNorm s.val ^ 3)
    have hu : ∀ rs ∈ u, rs.1 ∈ normBoundedIdeals F Y := by
      intro rs hrs
      obtain ⟨hrs, hs⟩ := Finset.mem_filter.1 hrs
      change idealNorm rs.1.val ≤ Y
      dsimp [Y]
      rw [← hs]
      exact powerful_factor_norm_le rs.1 rs.2 X hX0 (ht rs hrs)
    have hi : Set.InjOn Prod.fst (↑u : Set (NonzeroIdeal F × NonzeroIdeal F)) := by
      intro rs hrs rs' hrs' he
      apply Prod.ext he
      exact (Finset.mem_filter.1 hrs).2.trans (Finset.mem_filter.1 hrs').2.symm
    have huCard : u.card ≤ (normBoundedIdeals F Y).ncard := by
      have := Set.ncard_le_ncard_of_injOn Prod.fst hu hi (normBoundedIdeals_finite F Y)
      simpa using this
    calc
      (u.card : ℝ) ≤ ((normBoundedIdeals F Y).ncard : ℝ) := by exact_mod_cast huCard
      _ ≤ C * Y := hc Y (Real.sqrt_nonneg _)
      _ = C * Real.sqrt X * w s := by
        dsimp [Y, w]
        rw [powerful_cutoff_eq X _ hX0 (by
          have := idealNorm_ge_one s.val s.property
          linarith)]
        change C * (Real.sqrt X * Real.rpow (idealNorm s.val) (-(3 / 2 : ℝ))) =
          C * Real.sqrt X * Real.rpow (idealNorm s.val) (-(3 / 2 : ℝ))
        exact (mul_assoc _ _ _).symm
  calc
    ((normPowerfulIdeals F X).ncard : ℝ) =
        ∑ s ∈ t.image Prod.snd, ((t.filter (fun rs => rs.2 = s)).card : ℝ) := by
      rw [hcard, Finset.card_eq_sum_card_image Prod.snd t, Nat.cast_sum]
    _ ≤ ∑ s ∈ t.image Prod.snd, C * Real.sqrt X * w s := Finset.sum_le_sum hfiber
    _ = C * Real.sqrt X * ∑ s ∈ t.image Prod.snd, w s := by rw [Finset.mul_sum]
    _ ≤ C * Real.sqrt X * ∑' s, w s := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum _ (fun s _ => hw0 s)) (by positivity)
    _ ≤ (C * ((∑' s, w s) + 1)) * Real.sqrt X := by
      nlinarith [Real.sqrt_nonneg X]

theorem exterior_powerful_dyad_count_bound (F : Type) [Field F] [NumberField F] :
    ∃ K' : ℝ, 0 < K' ∧ ∀ cS : Ideal (𝓞 F), cS ≠ ⊥ →
      ∀ P : ℝ, 1 ≤ P →
        ((exteriorPowerfulDyad cS P).ncard : ℝ) ≤ K' * Real.sqrt P := by
  obtain ⟨K, hK, hbound⟩ := powerful_ideal_count_bound F
  refine ⟨K * Real.sqrt 2, mul_pos hK (Real.sqrt_pos.2 (by norm_num)), ?_⟩
  intro cS _ P hP
  let f : ExteriorIdeal cS → NonzeroIdeal F := fun h => ⟨h.val, h.property.1⟩
  have hc : (exteriorPowerfulDyad cS P).ncard ≤
      (normPowerfulIdeals F (2 * P)).ncard := by
    apply Set.ncard_le_ncard_of_injOn f (ht := normPowerfulIdeals_finite F (2 * P))
    · intro h hh
      exact ⟨hh.1, hh.2.2⟩
    · intro a _ b _ hab
      exact Subtype.ext (congrArg (fun h : NonzeroIdeal F => h.val) hab)
  calc
    ((exteriorPowerfulDyad cS P).ncard : ℝ) ≤
        ((normPowerfulIdeals F (2 * P)).ncard : ℝ) := by exact_mod_cast hc
    _ ≤ K * Real.sqrt (2 * P) := hbound _ (by linarith)
    _ = (K * Real.sqrt 2) * Real.sqrt P := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

end

end DedekindZetaZeroFree
