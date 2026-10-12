module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FrozenTensor

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open scoped Classical

def jetSum (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  ∑ j : Fin 3, ‖iteratedDeriv j.val f u‖

lemma jetSum_nonneg (f : ℝ → ℂ) (u : ℝ) : 0 ≤ jetSum f u := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_jet_le (f : ℝ → ℂ) (u : ℝ) {j : ℕ} (hj : j ≤ 2) :
    ‖iteratedDeriv j f u‖ ≤ jetSum f u := by
  exact Finset.single_le_sum (fun a _ => norm_nonneg (iteratedDeriv a.val f u))
    (Finset.mem_univ (⟨j, by omega⟩ : Fin 3))

lemma norm_mul_jet_le (f g : ℝ → ℂ) (u A B : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfj : ∀ j : ℕ, j ≤ 2 → ‖iteratedDeriv j f u‖ ≤ A)
    (hgj : ∀ j : ℕ, j ≤ 2 → ‖iteratedDeriv j g u‖ ≤ B)
    (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j (fun t => f t * g t) u‖ ≤ 4 * A * B := by
  have hb (k l : ℕ) (hk : k ≤ 2) (hl : l ≤ 2) :
      ‖iteratedDeriv k f u * iteratedDeriv l g u‖ ≤ A * B := by
    rw [norm_mul]
    exact mul_le_mul (hfj k hk) (hgj l hl) (norm_nonneg _) hA
  interval_cases j
  · simpa using (hb 0 0 (by omega) (by omega)).trans
      (show A * B ≤ 4 * A * B by nlinarith [mul_nonneg hA hB])
  · have he : iteratedDeriv 1 (fun t => f t * g t) u =
        iteratedDeriv 1 f u * iteratedDeriv 0 g u +
          iteratedDeriv 0 f u * iteratedDeriv 1 g u := by
      rw [iteratedDeriv_fun_mul (hf.of_le (by norm_num)).contDiffAt
        (hg.of_le (by norm_num)).contDiffAt]
      simp [Finset.sum_range_succ]
      ring
    rw [he]
    have ht := norm_add_le (iteratedDeriv 1 f u * iteratedDeriv 0 g u)
      (iteratedDeriv 0 f u * iteratedDeriv 1 g u)
    nlinarith [hb 1 0 (by omega) (by omega), hb 0 1 (by omega) (by omega), mul_nonneg hA hB]
  · have he : iteratedDeriv 2 (fun t => f t * g t) u =
        iteratedDeriv 2 f u * iteratedDeriv 0 g u +
          2 * (iteratedDeriv 1 f u * iteratedDeriv 1 g u) +
            iteratedDeriv 0 f u * iteratedDeriv 2 g u := by
      rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
      simp [Finset.sum_range_succ]
      ring
    rw [he]
    have ht := (norm_add_le
      (iteratedDeriv 2 f u * iteratedDeriv 0 g u +
        2 * (iteratedDeriv 1 f u * iteratedDeriv 1 g u))
      (iteratedDeriv 0 f u * iteratedDeriv 2 g u)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    have hn : ‖(2 : ℂ) * (iteratedDeriv 1 f u * iteratedDeriv 1 g u)‖ =
        2 * ‖iteratedDeriv 1 f u * iteratedDeriv 1 g u‖ := by
      rw [norm_mul]; norm_num
    rw [hn] at ht
    nlinarith [hb 2 0 (by omega) (by omega), hb 1 1 (by omega) (by omega),
      hb 0 2 (by omega) (by omega)]

theorem norm_prod_jet_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (u : ℝ) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j (fun t => ∏ i ∈ s, f i t) u‖ ≤
      4 ^ s.card * ∏ i ∈ s, jetSum (f i) u := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    interval_cases j <;> simp [iteratedDeriv_succ]
  | @insert a s ha ih =>
    have hfs : ContDiff ℝ 2 (fun t => ∏ i ∈ s, f i t) := by
      exact contDiff_prod (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hn : 0 ≤ 4 ^ s.card * ∏ i ∈ s, jetSum (f i) u :=
      mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => jetSum_nonneg (f i) u)
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hb := norm_mul_jet_le (f a) (fun t => ∏ i ∈ s, f i t) u
      (jetSum (f a) u) (4 ^ s.card * ∏ i ∈ s, jetSum (f i) u)
      (hf a (Finset.mem_insert_self _ _)) hfs (jetSum_nonneg (f a) u) hn
      (fun k hk => norm_jet_le (f a) u hk)
      (fun k hk => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) k hk) j hj
    exact hb.trans_eq (by rw [pow_succ]; ring)

theorem norm_uniform_product_jet_le {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (u : ℝ) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j (fun t => ∏ i, f i t) u‖ ≤
      4 ^ Fintype.card ι * ∑ a : ι → Fin 3, ∏ i, ‖iteratedDeriv (a i).val (f i) u‖ := by
  have h := norm_prod_jet_le Finset.univ f (fun i _ => hf i) u j hj
  simpa only [Finset.card_univ, jetSum, Fintype.prod_sum] using h

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
