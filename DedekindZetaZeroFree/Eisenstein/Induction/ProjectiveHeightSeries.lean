module

public import DedekindZetaZeroFree.Eisenstein.Induction.ProjectiveHeightCounts

@[expose] public section

namespace DedekindZetaZeroFree.KPHeightSeries

noncomputable section

abbrev P1 (F : Type) [Field F] := Projectivization F (Fin 2 → F)

def compactExponent (T : Set ℂ) : ℝ :=
  2 / 3 + sInf (Complex.re '' T)

def term {F : Type} [Field F] (H : P1 F → ℝ) (a : ℝ) (ℓ : P1 F) : ℝ :=
  (H ℓ) ^ (-2 * a)

def tail {F : Type} [Field F] (H : P1 F → ℝ) (a B : ℝ) : ℝ :=
  ∑' ℓ : {ℓ : P1 F // B < H ℓ}, term H a ℓ.1

private lemma shell_identity (C B a : ℝ) (hB : 0 < B) (n : ℕ) :
    C * ((2 : ℝ) ^ (n + 1) * B) ^ 2 * ((2 : ℝ) ^ n * B) ^ (-2 * a) =
      (4 * C * B ^ (2 - 2 * a)) * ((2 : ℝ) ^ (2 - 2 * a)) ^ n := by
  have hb : B ^ (2 - 2 * a) = B ^ 2 * B ^ (-2 * a) := by
    rw [sub_eq_add_neg, Real.rpow_add hB]; norm_num
  have ht : (2 : ℝ) ^ (2 - 2 * a) = 4 * (2 : ℝ) ^ (-2 * a) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [hb, ht, mul_pow, Real.mul_rpow (by positivity) hB.le,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), pow_succ (2 : ℝ) n, mul_pow]
  rw [← pow_mul, mul_comm n 2, pow_mul]
  norm_num
  ring

private lemma finite_sum_bound {α : Type*} (H : α → ℝ) (C a B : ℝ)
    (hC : 0 < C) (ha : 1 < a) (hB : 1 ≤ B)
    (hcount : ∀ R : ℝ, 1 ≤ R → {x : α | H x ≤ R}.Finite ∧
      ({x : α | H x ≤ R}.ncard : ℝ) ≤ C * R ^ 2)
    (u : Finset α) (hu : ∀ x ∈ u, B ≤ H x) :
    ∑ x ∈ u, (H x) ^ (-2 * a) ≤
      (4 * C / (1 - (2 : ℝ) ^ (2 - 2 * a))) * B ^ (2 - 2 * a) := by
  classical
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hex : ∀ x : α, ∃ n : ℕ, B ≤ H x →
      (2 : ℝ) ^ n * B ≤ H x ∧ H x < (2 : ℝ) ^ (n + 1) * B := by
    intro x
    by_cases hx : B ≤ H x
    · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
        ((le_div_iff₀ hBp).2 (by simpa using hx)) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, fun _ => ⟨(le_div_iff₀ hBp).1 hn, (div_lt_iff₀ hBp).1 hn'⟩⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose k hk using hex
  let r : ℝ := (2 : ℝ) ^ (2 - 2 * a)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hshell : ∀ n ∈ u.image k,
      ∑ x ∈ u with k x = n, (H x) ^ (-2 * a) ≤
        (4 * C * B ^ (2 - 2 * a)) * r ^ n := by
    intro n hn
    have hR : 1 ≤ (2 : ℝ) ^ (n + 1) * B := by
      calc
        1 ≤ B := hB
        _ ≤ (2 : ℝ) ^ (n + 1) * B := by
          simpa using mul_le_mul_of_nonneg_right
            (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ (n + 1)) hBp.le
    obtain ⟨hfin, hcard⟩ := hcount _ hR
    have hcard' : ((u.filter (fun x => k x = n)).card : ℝ) ≤
        ({x : α | H x ≤ (2 : ℝ) ^ (n + 1) * B}.ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact_mod_cast Finset.card_le_card (show u.filter (fun x => k x = n) ⊆ hfin.toFinset from by
        intro x hx
        obtain ⟨hxu, hxn⟩ := Finset.mem_filter.mp hx
        apply hfin.mem_toFinset.mpr
        exact (hxn ▸ (hk x (hu x hxu)).2).le)
    calc
      _ ≤ ∑ x ∈ u with k x = n, ((2 : ℝ) ^ n * B) ^ (-2 * a) := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxu, hxn⟩ := Finset.mem_filter.mp hx
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (hxn ▸ (hk x (hu x hxu)).1) (by linarith)
      _ = ((u.filter (fun x => k x = n)).card : ℝ) *
          ((2 : ℝ) ^ n * B) ^ (-2 * a) := by simp
      _ ≤ (C * ((2 : ℝ) ^ (n + 1) * B) ^ 2) *
          ((2 : ℝ) ^ n * B) ^ (-2 * a) :=
        mul_le_mul_of_nonneg_right (hcard'.trans hcard) (by positivity)
      _ = _ := shell_identity C B a hBp n
  calc
    _ = ∑ n ∈ u.image k, ∑ x ∈ u with k x = n, (H x) ^ (-2 * a) :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem k hx) _).symm
    _ ≤ ∑ n ∈ u.image k, (4 * C * B ^ (2 - 2 * a)) * r ^ n :=
      Finset.sum_le_sum hshell
    _ = (4 * C * B ^ (2 - 2 * a)) * ∑ n ∈ u.image k, r ^ n := by
      rw [Finset.mul_sum]
    _ ≤ (4 * C * B ^ (2 - 2 * a)) * ∑' n : ℕ, r ^ n :=
      mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun _ _ => pow_nonneg hr0 _)) (by positivity)
    _ = _ := by rw [tsum_geometric_of_lt_one hr0 hr1]; dsimp [r]; ring

private lemma series_of_count {α : Type*} (H : α → ℝ) (a : ℝ) (ha : 1 < a)
    (hH : ∀ x, 1 ≤ H x)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → {x : α | H x ≤ R}.Finite ∧
      ({x : α | H x ≤ R}.ncard : ℝ) ≤ C * R ^ 2) :
    Summable (fun x => (H x) ^ (-2 * a)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
        (∑' x : {x : α // B < H x}, (H x.1) ^ (-2 * a)) ≤ C * B ^ (2 - 2 * a) := by
  classical
  obtain ⟨C, hC, hc⟩ := hcount
  have hn : ∀ x, 0 ≤ (H x) ^ (-2 * a) := fun x =>
    Real.rpow_nonneg (by linarith [hH x]) _
  have hr : (2 : ℝ) ^ (2 - 2 * a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨summable_of_sum_le (c := 4 * C / (1 - (2 : ℝ) ^ (2 - 2 * a))) hn (fun u => ?_),
    4 * C / (1 - (2 : ℝ) ^ (2 - 2 * a)), by positivity, ?_⟩
  · simpa using finite_sum_bound H C a 1 hC ha le_rfl hc u (fun x _ => hH x)
  · intro B hB
    apply Real.tsum_le_of_sum_le (fun x : {x : α // B < H x} => hn x.1)
    intro u
    let e : {x : α // B < H x} ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
    have hb := finite_sum_bound H C a B hC ha hB hc (u.map e) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.2.le)
    simpa [e, Finset.sum_map] using hb

theorem relativeHeight_summable_tail (F : Type) [Field F] [NumberField F]
    (a : ℝ) (ha : 1 < a) :
    Summable (term (Projectivization.mulHeight (K := F)) a) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
        tail (Projectivization.mulHeight (K := F)) a B ≤ C * B ^ (2 - 2 * a) := by
  exact series_of_count _ a ha Projectivization.one_le_mulHeight
    (KPChamberProjectiveCount.relativeHeight_count F)

end
end DedekindZetaZeroFree.KPHeightSeries
