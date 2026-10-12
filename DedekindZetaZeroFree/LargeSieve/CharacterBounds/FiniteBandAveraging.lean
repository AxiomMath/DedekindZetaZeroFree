module

public import DedekindZetaZeroFree.LargeSieve.Exponents.FinitePrimeTransfer

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma band_incidence (L : ℕ) (t : ℝ) {ι : Type*} (U : Finset ι) (bad : Fin L → ι → Prop)
    (w : ι → ℝ) (db : ∀ i a, Decidable (bad i a)) (hw : ∀ a ∈ U, 0 ≤ w a)
    (hc : ∀ a ∈ U, ((@Finset.filter (Fin L) (fun i => bad i a) (fun i => db i a) Finset.univ).card : ℝ) ≤ t) :
    (∑ i : Fin L, ∑ a ∈ @Finset.filter ι (bad i) (db i) U, w a) ≤ t * ∑ a ∈ U, w a := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ a ∈ U, ∑ i : Fin L, if bad i a then w a else 0) =
        ∑ a ∈ U, ((@Finset.filter (Fin L) (fun i => bad i a) (fun i => db i a) Finset.univ).card : ℝ) * w a := by
      congr 1
      ext a
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ a ∈ U, t * w a :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (hc a ha) (hw a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_band_average
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (R : Finset α) (S : Finset β) (T : Finset γ)
    (L : ℕ) (hL : 1 ≤ L)
    (rowGood : Fin L → α → Prop) (colGood : Fin L → β → Prop)
    (f : ∀ i : Fin L,
      {a : α // a ∈ R ∧ rowGood i a} → {a : γ // a ∈ T})
    (u : Fin L → β → ℂ) (A : α → β → ℂ) (H : γ → β → ℂ)
    (hinj : ∀ i, Function.Injective (f i))
    (hphase_le : ∀ i, ∀ b ∈ S, ‖u i b‖ ≤ 1)
    (hphase : ∀ i, ∀ b ∈ S, colGood i b → ‖u i b‖ = 1)
    (htransport : ∀ i, ∀ a : {a : α // a ∈ R ∧ rowGood i a},
      ∀ b ∈ S, colGood i b → H (f i a).val b = u i b * A a.val b)
    (t B B_T : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hB_T : 0 ≤ B_T)
    (hbad_row : ∀ a ∈ R,
      (((Finset.univ : Finset (Fin L)).filter (fun i => ¬rowGood i a)).card : ℝ) ≤ t)
    (hbad_col : ∀ b ∈ S,
      (((Finset.univ : Finset (Fin L)).filter (fun i => ¬colGood i b)).card : ℝ) ≤ t)
    (hbound : ∀ lam : β → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2 ≤
        B * (∑ b ∈ S, ‖lam b‖ ^ 2))
    (htarget : ∀ lam : β → ℂ,
      ∑ a ∈ T, ‖∑ b ∈ S, lam b * H a b‖ ^ 2 ≤
        B_T * (∑ b ∈ S, ‖lam b‖ ^ 2)) :
    (∀ lam : β → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2 ≤
        (2 * B_T + 3 * (t / (L : ℝ)) * B) * (∑ b ∈ S, ‖lam b‖ ^ 2)) ∧
    (IsLeast {C : ℝ | 0 ≤ C ∧ ∀ lam : β → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2 ≤
        C * (∑ b ∈ S, ‖lam b‖ ^ 2)} B →
      6 * t ≤ (L : ℝ) → B ≤ 4 * B_T) := by
  classical
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hresult : ∀ lam : β → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2 ≤
        (2 * B_T + 3 * (t / (L : ℝ)) * B) * (∑ b ∈ S, ‖lam b‖ ^ 2) := by
    intro lam
    have hsingle (i : Fin L) :
        ∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2 ≤
          (∑ a ∈ R with ¬rowGood i a, ‖∑ b ∈ S, lam b * A a b‖ ^ 2) +
          2 * B_T * (∑ b ∈ S, ‖lam b‖ ^ 2) +
          2 * B * (∑ b ∈ S with ¬colGood i b, ‖lam b‖ ^ 2) := by
      let extend (v : S → ℂ) : β → ℂ := fun b => if hb : b ∈ S then v ⟨b, hb⟩ else 0
      have hsum (v : S → ℂ) (K : β → ℂ) :
          (∑ b : S, v b * K b.val) = ∑ b ∈ S, extend v b * K b := by
        rw [← Finset.sum_coe_sort S]
        apply Finset.sum_congr rfl
        intro b _
        simp [extend, b.property]
      have henergy (v : S → ℂ) :
          (∑ b : S, ‖v b‖ ^ 2) = ∑ b ∈ S, ‖extend v b‖ ^ 2 := by
        rw [← Finset.sum_coe_sort S]
        apply Finset.sum_congr rfl
        intro b _
        simp [extend, b.property]
      have hA (v : S → ℂ) :
          (∑ a : R, ‖∑ b : S, v b * A a.val b.val‖ ^ 2) ≤ B * ∑ b : S, ‖v b‖ ^ 2 := by
        simp_rw [hsum]
        rw [Finset.sum_coe_sort R (fun a => ‖∑ b ∈ S, extend v b * A a b‖ ^ 2), henergy]
        exact hbound (extend v)
      have hH (v : S → ℂ) :
          (∑ a : T, ‖∑ b : S, v b * H a.val b.val‖ ^ 2) ≤ B_T * ∑ b : S, ‖v b‖ ^ 2 := by
        simp_rw [hsum]
        rw [Finset.sum_coe_sort T (fun a => ‖∑ b ∈ S, extend v b * H a b‖ ^ 2), henergy]
        exact htarget (extend v)
      let f' : {a : R // a ∈ Finset.univ ∧ ¬¬rowGood i a.val} → T :=
        fun a => f i ⟨a.val.val, a.val.property, not_not.mp a.property.2⟩
      have hf' : Function.Injective f' := by
        intro a b hab
        have he := hinj i hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : {a : α // a ∈ R ∧ rowGood i a} => z.val) he
      have htr (a : {a : R // a ∈ Finset.univ ∧ ¬¬rowGood i a.val}) (b : S)
          (hb : ¬¬colGood i b.val) :
          A a.val.val b.val = (starRingEnd ℂ) (u i b.val) * H (f' a).val b.val := by
        rw [htransport i ⟨a.val.val, a.val.property, not_not.mp a.property.2⟩
          b.val b.property (not_not.mp hb)]
        have hp : (starRingEnd ℂ) (u i b.val) * u i b.val = 1 := by
          rw [Complex.conj_mul', hphase i b.val b.property (not_not.mp hb)]
          simp
        dsimp [f']
        rw [← mul_assoc, hp, one_mul]
      have hh := exponent_finite_prime_transfer
        (fun (a : R) (b : S) => A a.val b.val)
        (fun (a : T) (b : S) => H a.val b.val) Finset.univ
        (fun a : R => ¬rowGood i a.val) (fun b : S => ¬colGood i b.val)
        (fun b : S => (starRingEnd ℂ) (u i b.val))
        (fun b => by simpa using hphase_le i b.val b.property)
        f' hf' htr B B_T hB hB_T hA hH (fun b : S => lam b.val)
      simp_rw [Finset.sum_filter] at hh ⊢
      have hsums (K : β → ℂ) : (∑ b : S, lam b.val * K b.val) =
          ∑ b ∈ S, lam b * K b := Finset.sum_coe_sort S (fun b => lam b * K b)
      simp_rw [hsums] at hh
      rw [Finset.sum_coe_sort R (fun a => ‖∑ b ∈ S, lam b * A a b‖ ^ 2),
        Finset.sum_coe_sort R (fun a => if ¬rowGood i a then ‖∑ b ∈ S, lam b * A a b‖ ^ 2 else 0),
        Finset.sum_coe_sort S (fun b => ‖lam b‖ ^ 2),
        Finset.sum_coe_sort S (fun b => if ¬colGood i b then ‖lam b‖ ^ 2 else 0)] at hh
      exact hh
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) => hsingle i)
    have hr := band_incidence L t R (fun i a => ¬rowGood i a)
      (fun a => ‖∑ b ∈ S, lam b * A a b‖ ^ 2) (fun i a => inferInstance) (fun _ _ => sq_nonneg _) (by intro a ha; simpa using hbad_row a ha)
    have hc := band_incidence L t S (fun i b => ¬colGood i b)
      (fun b => ‖lam b‖ ^ 2) (fun i b => inferInstance) (fun _ _ => sq_nonneg _) (by intro b hb; simpa using hbad_col b hb)
    have he : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := by positivity
    have hb := hbound lam
    have hsum : (L : ℝ) * (∑ a ∈ R, ‖∑ b ∈ S, lam b * A a b‖ ^ 2) ≤
        2 * (L : ℝ) * B_T * (∑ b ∈ S, ‖lam b‖ ^ 2) +
        3 * t * B * (∑ b ∈ S, ‖lam b‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hs
      have hr' := hr.trans (mul_le_mul_of_nonneg_left hb ht)
      have hc' := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
      calc
        _ ≤ t * (B * (∑ b ∈ S, ‖lam b‖ ^ (2:ℕ))) + (L : ℝ) * (2 * B_T * (∑ b ∈ S, ‖lam b‖ ^ (2:ℕ))) + 2 * B * (t * (∑ b ∈ S, ‖lam b‖ ^ (2:ℕ))) :=
          hs.trans (add_le_add (add_le_add hr' le_rfl) hc')
        _ = _ := by ring
    apply (mul_le_mul_iff_right₀ hLpos).mp
    calc
      _ ≤ 2 * (L : ℝ) * B_T * (∑ b ∈ S, ‖lam b‖ ^ 2) +
          3 * t * B * (∑ b ∈ S, ‖lam b‖ ^ 2) := hsum
      _ = _ := by field_simp <;> ring
  refine ⟨hresult, ?_⟩
  intro hleast hlarge
  have hcoef : 0 ≤ 2 * B_T + 3 * (t / (L : ℝ)) * B := by positivity
  have hb := hleast.2 ⟨hcoef, hresult⟩
  have hratio : 3 * (t / (L : ℝ)) ≤ (1 / 2 : ℝ) := by
    rw [show 3 * (t / (L : ℝ)) = (3 * t) / L by ring]
    exact (div_le_iff₀ hLpos).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right hratio hB
  linarith

end DedekindZetaZeroFree.LargeSieve.Vendor
