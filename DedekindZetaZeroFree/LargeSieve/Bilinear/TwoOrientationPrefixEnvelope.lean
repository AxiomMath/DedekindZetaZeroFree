module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.NormalizedShellTranspose
public import DedekindZetaZeroFree.LargeSieve.Bilinear.MainTermBoundaryBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope

open scoped NumberField Classical

private lemma prefix_numeric_bound (α η Ce : ℝ) (ha : α ∈ Set.Icc (1 : ℝ) 2)
    (he : 0 < η) (hCe : 1 ≤ Ce) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ B Y : ℝ, 1 ≤ B → 1 ≤ Y →
      ∀ M N : ℝ, 1 ≤ M → M ≤ 2 * B →
        1 ≤ N → N ≤ 2 * Y →
      (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * B) + 1 : ℝ) *
        (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * Y) + 1 : ℝ) *
        (Ce * Real.rpow (M * N) (η / 2) *
          (M + Real.rpow (N) α)) ≤
      C * Real.rpow (B * Y) η * (B + Real.rpow Y α) := by
  let d := η / 2
  let D := 2 + 1 / (d * Real.log 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hD : 0 < D := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power_constant_pos hd
  let C0 := D * D * Ce * 4 * ((4 : ℝ) ^ d * (4 : ℝ) ^ d)
  refine ⟨max 1 C0, le_max_left _ _, ?_⟩
  intro B Y hB hY M N hi hiB hj hjY
  have hB0 : 0 ≤ B := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hP : 0 < B * Y := mul_pos (by linarith) (by linarith)
  have h2B : 1 ≤ 2 * B := by linarith
  have h2Y : 1 ≤ 2 * Y := by linarith
  have hA := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hd h2B
  have hJ := DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength_small_power hd h2Y
  have hprod : M * N ≤ 4 * (B * Y) := by
    calc _ ≤ (2 * B) * (2 * Y) := mul_le_mul hiB hjY (by linarith) (by linarith)
         _ = _ := by ring
  have hp : (M * N) ^ d ≤ (4 * (B * Y)) ^ d :=
    Real.rpow_le_rpow (mul_nonneg (by linarith) (by linarith)) hprod hd.le
  have hna : (N) ^ α ≤ 4 * Y ^ α := by
    calc _ ≤ (2 * Y) ^ α := Real.rpow_le_rpow (by linarith) hjY (by linarith [ha.1])
         _ = (2 : ℝ) ^ α * Y ^ α := Real.mul_rpow (by norm_num) hY0
         _ ≤ 4 * Y ^ α := by
           apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY0 _)
           have hh := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) ha.2
           norm_num [Real.rpow_two] at hh ⊢
           exact hh
  have hs : M + (N) ^ α ≤ 4 * (B + Y ^ α) := by
    nlinarith
  have hCe0 : 0 ≤ Ce := by linarith
  have hloc : Ce * (M * N) ^ d *
      (M + (N) ^ α) ≤
      Ce * (4 * (B * Y)) ^ d * (4 * (B + Y ^ α)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp hCe0) hs
      (by positivity) (by positivity)
  have hcount : (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * B) + 1 : ℝ) *
      (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * Y) + 1 : ℝ) ≤
      (D * (2 * B) ^ d) * (D * (2 * Y) ^ d) :=
    mul_le_mul hA hJ (by positivity) (by positivity)
  have htotal := mul_le_mul hcount hloc (by positivity) (by positivity)
  have heq : (D * (2 * B) ^ d) * (D * (2 * Y) ^ d) *
      (Ce * (4 * (B * Y)) ^ d * (4 * (B + Y ^ α))) =
      C0 * (B * Y) ^ η * (B + Y ^ α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB0,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hY0,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hP.le]
    have hfour : (2 : ℝ) ^ d * (2 : ℝ) ^ d = (4 : ℝ) ^ d := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have hby : B ^ d * Y ^ d = (B * Y) ^ d := (Real.mul_rpow hB0 hY0).symm
    have hpp : (B * Y) ^ d * (B * Y) ^ d = (B * Y) ^ η := by
      rw [← Real.rpow_add hP]; congr 1; dsimp [d]; ring
    calc _ = D * D * Ce * 4 * ((2 : ℝ) ^ d * (2 : ℝ) ^ d * (4 : ℝ) ^ d) *
          (B ^ d * Y ^ d * (B * Y) ^ d) * (B + Y ^ α) := by ring
         _ = _ := by rw [hfour, hby, hpp]
  rw [heq] at htotal
  change _ ≤ max 1 C0 * (B * Y) ^ η * (B + Y ^ α)
  exact htotal.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right 1 C0) (by positivity)) (by positivity))

theorem direct_prefix_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hcq : c ∣ q)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (B X : ℝ), 1 ≤ B → 0 < X →
      ∀ (R S : Finset (Ideal (𝓞 F))),
        R ⊆ idealAdmissibleFinset F q (2 * B) →
        S ⊆ idealAdmissibleFinset F q (2 * X) →
      ∀ (u v lam : Ideal (𝓞 F) → ℂ),
        (∀ a ∈ R, ‖u a‖ ≤ 1) → (∀ b ∈ S, ‖v b‖ ≤ 1) →
        ∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2 ≤
          C * Real.rpow (B * max 1 X) η *
            (B + Real.rpow (max 1 X) α) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  classical
  intro η hη
  obtain ⟨Ce, hCe, hendpoint⟩ := bilinear_endpoint_exponent_extension_contractions
    F c Q α hα hExponent (η / 2) (by positivity)
  obtain ⟨C, hC, hn⟩ := prefix_numeric_bound α η Ce hα hη hCe
  refine ⟨C, hC, ?_⟩
  intro B X hB hX R S hR hS u v lam hu hv
  let Y := max 1 X
  have hY : 1 ≤ Y := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h2B : 1 ≤ 2 * B := by linarith
  have h2Y : 1 ≤ 2 * Y := by linarith
  have hcore : ∀ Z : ℝ, idealAdmissibleFinset F q Z ⊆ idealAdmissibleFinset F c Z := by
    intro Z a ha
    obtain ⟨hsf, hcop, hnorm⟩ := (mem_idealAdmissibleFinset F q Z a).mp ha
    exact (mem_idealAdmissibleFinset F c Z a).mpr
      ⟨hsf, top_unique (hcop ▸ sup_le_sup_left (Ideal.dvd_iff_le.mp hcq) a), hnorm⟩
  have hRc : R ⊆ idealAdmissibleFinset F c (2 * B) := hR.trans (hcore _)
  have hSc : S ⊆ idealAdmissibleFinset F c (2 * Y) := by
    intro b hb
    obtain ⟨hsf, hcop, hnorm⟩ :=
      (mem_idealAdmissibleFinset F c (2 * X) b).mp (hcore _ (hS hb))
    exact (mem_idealAdmissibleFinset F c (2 * Y) b).mpr
      ⟨hsf, hcop, hnorm.trans (mul_le_mul_of_nonneg_left (le_max_right 1 X) (by norm_num))⟩
  let I := Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * B) + 1)
  let J := Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength (2 * Y) + 1)
  let RB := fun i => clippedDyadicBlock F c (2 * B) i ∩ R
  let SB := fun j => clippedDyadicBlock F c (2 * Y) j ∩ S
  have hcover : ∀ (Z : ℝ) (hZ : 1 ≤ Z) (A : Finset (Ideal (𝓞 F))),
      A ⊆ idealAdmissibleFinset F c Z →
      (Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength Z + 1)).biUnion
        (fun i => clippedDyadicBlock F c Z i ∩ A) = A := by
    intro Z hZ A hA
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_inter.mp hai).2
    · intro ha
      have hah : a ∈ (Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength Z + 1)).biUnion
          (clippedDyadicBlock F c Z) := by
        rw [biUnion_clippedDyadicBlock F c Z hZ]
        exact hA ha
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp hah
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hai, ha⟩⟩
  have hdisj : ∀ (Z : ℝ) (hZ : 1 ≤ Z) (A : Finset (Ideal (𝓞 F))),
      Set.PairwiseDisjoint (↑(Finset.range (DedekindZetaZeroFree.LargeSieve.Vendor.dyadicLength Z + 1)) : Set ℕ)
        (fun i => clippedDyadicBlock F c Z i ∩ A) := by
    intro Z hZ A i hi j hj hij
    exact (pairwiseDisjoint_clippedDyadicBlock F c Z hZ hi hj hij).mono
      Finset.inter_subset_left Finset.inter_subset_left
  let L := Ce * Real.rpow ((2 * B) * (2 * Y)) (η / 2) *
    (2 * B + Real.rpow (2 * Y) α)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlocal : ∀ i ∈ I, ∀ j ∈ J, ∀ l : Ideal (𝓞 F) → ℂ,
      ∑ a ∈ RB i, ‖∑ b ∈ SB j, l b * (u a * (Q.χ b) a * v b)‖ ^ 2 ≤
        L * ∑ b ∈ SB j, ‖l b‖ ^ 2 := by
    intro i hi j hj l
    have hr : RB i ⊆ idealDyadicBlock F c i :=
      Finset.inter_subset_left.trans (clippedDyadicBlock_subset_idealDyadicBlock F c _ i)
    have hs : SB j ⊆ idealDyadicBlock F c j :=
      Finset.inter_subset_left.trans (clippedDyadicBlock_subset_idealDyadicBlock F c _ j)
    have hbound := hendpoint i j (RB i) (SB j) hr hs u v l
      (fun a ha => hu a (Finset.mem_inter.mp ha).2)
      (fun b hb => hv b (Finset.mem_inter.mp hb).2)
    have hrew : (∑ a ∈ RB i, ‖∑ b ∈ SB j, l b * (u a * (Q.χ b) a * v b)‖ ^ 2) =
        ∑ a ∈ RB i, ‖∑ b ∈ SB j, u a * (l b * (Q.χ b) a) * v b‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 2
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [hrew]
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    obtain ⟨hi1, hi2⟩ := dyadicScale_bounds (2 * B) h2B i hi
    obtain ⟨hj1, hj2⟩ := dyadicScale_bounds (2 * Y) h2Y j hj
    have hprod : dyadicScale i * dyadicScale j ≤ (2 * B) * (2 * Y) :=
      mul_le_mul hi2 hj2 (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow
      (show 0 ≤ dyadicScale i * dyadicScale j by positivity) hprod (show 0 ≤ η / 2 by positivity)
    have hs' : dyadicScale i + Real.rpow (dyadicScale j) α ≤
        2 * B + Real.rpow (2 * Y) α := by
      exact add_le_add hi2 (Real.rpow_le_rpow (by linarith) hj2 (by linarith [hα.1]))
    simp only [Real.rpow_eq_pow] at hs' ⊢
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by linarith)) hs'
      (by positivity) (mul_nonneg (by linarith) (by rw [Real.rpow_eq_pow]; positivity))
  have hassembled := finite_partition_quadratic_bound I J R S RB SB
    (hcover _ h2B R hRc) (hcover _ h2Y S hSc) (hdisj _ h2B R) (hdisj _ h2Y S)
    (fun b a => u a * (Q.χ b) a * v b) L hL hlocal lam
  have hrew : (∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2) =
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * (u a * (Q.χ b) a * v b)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro a ha
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hrew]
  refine hassembled.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hh := hn B Y hB hY (2 * B) (2 * Y) h2B le_rfl h2Y le_rfl
  simpa [I, J, L, Finset.card_range] using hh

end DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope

open scoped NumberField Classical

private lemma prefix_partition {A : Type*} [DecidableEq A]
    (R : Finset A) (blocks : ℕ → Finset A) (P : Finset ℕ) (U : Finset A)
    (hU : P.biUnion blocks = U) (hR : R ⊆ U) :
    R = P.biUnion (fun i => R ∩ blocks i) := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · intro ha
    have := hR ha
    rw [← hU, Finset.mem_biUnion] at this
    obtain ⟨i, hi, hai⟩ := this
    exact ⟨i, hi, ha, hai⟩
  · rintro ⟨i, hi, ha, _⟩; exact ha

private lemma prefix_partition_disjoint {A : Type*} [DecidableEq A]
    (R : Finset A) (blocks : ℕ → Finset A) (P : Finset ℕ)
    (h : Set.PairwiseDisjoint (↑P : Set ℕ) blocks) :
    Set.PairwiseDisjoint (↑P : Set ℕ) (fun i => R ∩ blocks i) := by
  intro i hi j hj hij
  exact (h hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right

private lemma prefix_block_type
    (F : Type) [Field F] [NumberField F] (q : Ideal (𝓞 F))
    (T : ℝ) (R : Finset (Ideal (𝓞 F))) (j : ℕ) :
    (R ∩ clippedDyadicBlock F q T j) ⊆ paperShell F q (dyadicScale j) ∨
      (dyadicScale j = 1 ∧ (R ∩ clippedDyadicBlock F q T j) ⊆ {⊤}) := by
  have hh : R ∩ clippedDyadicBlock F q T j ⊆ idealDyadicBlock F q j :=
    fun a ha => clippedDyadicBlock_subset_idealDyadicBlock F q T j
      (Finset.mem_inter.mp ha).2
  cases j with
  | zero => exact Or.inr ⟨rfl, hh⟩
  | succ k => exact Or.inl hh

theorem transposed_prefix_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hreciprocity : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b))
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (B X : ℝ), 1 ≤ B → 0 < X →
      ∀ (R S : Finset (Ideal (𝓞 F))),
        R ⊆ idealAdmissibleFinset F q (2 * B) →
        S ⊆ idealAdmissibleFinset F q (2 * X) →
      ∀ (u v lam : Ideal (𝓞 F) → ℂ),
        (∀ a ∈ R, ‖u a‖ ≤ 1) → (∀ b ∈ S, ‖v b‖ ≤ 1) →
        ∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2 ≤
          C * Real.rpow (B * max 1 X) η *
            (max 1 X + Real.rpow B α) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  intro η hη
  let e := η / 2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨Cext, hCext, hexp⟩ := bilinear_normalized_shell_transpose_contractions
    F c Q q hq hcq hreciprocity α hα hExponent e he
  let k := 2 + 1 / (e * Real.log 2)
  let D := k ^ 2 * Cext * (4 : ℝ) ^ η * (2 : ℝ) ^ α
  refine ⟨max 1 D, le_max_left _ _, ?_⟩
  intro B X hB hX R S hR hS u v lam hu hv
  let Y := max 1 X
  have hY : 1 ≤ Y := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h2B : 1 ≤ 2 * B := by linarith
  have h2Y : 1 ≤ 2 * Y := by linarith
  have hC0 : 0 ≤ Cext := by linarith
  have ha : 0 ≤ α := by linarith [hα.1]
  have hSY : S ⊆ idealAdmissibleFinset F q (2 * Y) := by
    intro a ha
    obtain ⟨hsf, hcop, hn⟩ := (mem_idealAdmissibleFinset F q (2 * X) a).mp (hS ha)
    exact (mem_idealAdmissibleFinset F q (2 * Y) a).mpr
      ⟨hsf, hcop, hn.trans (mul_le_mul_of_nonneg_left (le_max_right 1 X) (by norm_num))⟩
  let P := Finset.range (Vendor.dyadicLength (2 * B) + 1)
  let T := Finset.range (Vendor.dyadicLength (2 * Y) + 1)
  let row := fun i => R ∩ clippedDyadicBlock F q (2 * B) i
  let col := fun j => S ∩ clippedDyadicBlock F q (2 * Y) j
  let U := Cext * Real.rpow (4 * B * Y) e * (2 * Y + Real.rpow (2 * B) α)
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hpart := Vendor.finite_partition_quadratic_bound R S P T row col
    (prefix_partition R _ _ _ (biUnion_clippedDyadicBlock F q (2 * B) h2B) hR)
    (prefix_partition S _ _ _ (biUnion_clippedDyadicBlock F q (2 * Y) h2Y) hSY)
    (prefix_partition_disjoint R _ _ (pairwiseDisjoint_clippedDyadicBlock F q (2 * B) h2B))
    (prefix_partition_disjoint S _ _ (pairwiseDisjoint_clippedDyadicBlock F q (2 * Y) h2Y))
    (fun b a => u a * (Q.χ b) a * v b) lam U hU (by
      intro i hi j hj
      have hi' := dyadicScale_bounds (2 * B) h2B i hi
      have hj' := dyadicScale_bounds (2 * Y) h2Y j hj
      have hh := hexp (dyadicScale i) (dyadicScale j) hi'.1 hj'.1 (row i) (col j)
        (prefix_block_type F q (2 * B) R i) (prefix_block_type F q (2 * Y) S j)
        u v lam (fun a ha => hu a (Finset.mem_inter.mp ha).1)
        (fun b hb => hv b (Finset.mem_inter.mp hb).1)
      have hh0 : ∑ a ∈ row i, ‖∑ b ∈ col j, lam b * (u a * (Q.χ b) a * v b)‖ ^ 2 ≤
          Cext * Real.rpow (dyadicScale i * dyadicScale j) e *
            (dyadicScale j + Real.rpow (dyadicScale i) α) * ∑ b ∈ col j, ‖lam b‖ ^ 2 := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
      refine hh0.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      have hi0 : 0 ≤ dyadicScale i := by linarith [hi'.1]
      have hj0 : 0 ≤ dyadicScale j := by linarith [hj'.1]
      have hm : dyadicScale i * dyadicScale j ≤ 4 * B * Y := by
        calc _ ≤ (2 * B) * (2 * Y) := mul_le_mul hi'.2 hj'.2 hj0 (by positivity)
             _ = _ := by ring
      have hp : Real.rpow (dyadicScale i * dyadicScale j) e ≤ Real.rpow (4 * B * Y) e := by
        simp only [Real.rpow_eq_pow]
        exact Real.rpow_le_rpow (mul_nonneg hi0 hj0) hm he.le
      have hs : dyadicScale j + Real.rpow (dyadicScale i) α ≤ 2 * Y + Real.rpow (2 * B) α := by
        simp only [Real.rpow_eq_pow]
        exact add_le_add hj'.2 (Real.rpow_le_rpow hi0 hi'.2 ha)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC0) hs
        (by simp only [Real.rpow_eq_pow]; positivity)
        (by simp only [Real.rpow_eq_pow]; positivity))
  have hk : 0 ≤ k := (Vendor.dyadicLength_small_power_constant_pos he).le
  have hp : (P.card : ℝ) * (T.card : ℝ) ≤
      k ^ 2 * Real.rpow (4 * B * Y) e := by
    have hh := mul_le_mul (Vendor.dyadicLength_small_power he h2B)
      (Vendor.dyadicLength_small_power he h2Y)
      (by positivity : (0 : ℝ) ≤ (Vendor.dyadicLength (2 * Y) : ℝ) + 1)
      (by positivity : 0 ≤ (2 + 1 / (e * Real.log 2)) * (2 * B) ^ e)
    have hid : Real.rpow (4 * B * Y) e = (2 * B) ^ e * (2 * Y) ^ e := by
      rw [Real.rpow_eq_pow, show 4 * B * Y = (2 * B) * (2 * Y) by ring,
        Real.mul_rpow (by positivity) (by positivity)]
    simp only [Real.rpow_eq_pow] at hid ⊢
    rw [hid]
    simp only [P, T, Finset.card_range, Nat.cast_add, Nat.cast_one]
    convert hh using 1 <;> dsimp [k] <;> ring
  have hh := mul_le_mul_of_nonneg_right hp hU
  have hid : Real.rpow (4 * B * Y) e * Real.rpow (4 * B * Y) e =
      Real.rpow (4 * B * Y) (2 * e) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by positivity)]
    congr 1; ring
  have hh' : (P.card : ℝ) * (T.card : ℝ) * U ≤
      k ^ 2 * Cext * Real.rpow (4 * B * Y) (2 * e) * (2 * Y + Real.rpow (2 * B) α) := by
    simp only [Real.rpow_eq_pow] at hid ⊢ hh
    rw [← hid]
    convert hh using 1 <;> dsimp [U] <;> ring
  have harith : k ^ 2 * Cext * Real.rpow (4 * B * Y) (2 * e) *
      (2 * Y + Real.rpow (2 * B) α) ≤
      max 1 D * Real.rpow (B * Y) η * (Y + Real.rpow B α) := by
    have heq : 2 * e = η := by dsimp [e]; ring
    have hid' : (4 * B * Y) ^ (2 * e) = (4 : ℝ) ^ η * (B * Y) ^ η := by
      rw [heq, show 4 * B * Y = 4 * (B * Y) by ring,
        Real.mul_rpow (by norm_num) (mul_nonneg hB0 hY0)]
    have h2a : (2 : ℝ) ≤ (2 : ℝ) ^ α := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα.1
      simpa only [Real.rpow_one] using ht
    have hs : 2 * Y + (2 * B) ^ α ≤ (2 : ℝ) ^ α * (Y + B ^ α) := by
      rw [Real.mul_rpow (by norm_num) hB0, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right h2a hY0) le_rfl
    have hg : 0 ≤ k ^ 2 * Cext * (4 * B * Y) ^ (2 * e) := by positivity
    have ht := mul_le_mul_of_nonneg_left hs hg
    have ht' : k ^ 2 * Cext * Real.rpow (4 * B * Y) (2 * e) *
        (2 * Y + Real.rpow (2 * B) α) ≤ D * (B * Y) ^ η * (Y + B ^ α) := by
      dsimp [D]
      rw [hid']
      rw [hid'] at ht
      convert ht using 1 <;> ring
    refine ht'.trans ?_
    simp only [Real.rpow_eq_pow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 D) (by positivity)) (by positivity)
  have hfinal := hpart.trans (mul_le_mul_of_nonneg_right (hh'.trans harith)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hfinal

end DedekindZetaZeroFree.LargeSieve.Sieve.SplitPrefixEnvelope

end

section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem bilinear_prefix_two_orientation_envelope
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hreciprocity : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b))
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (B X : ℝ), 1 ≤ B → 0 < X →
      ∀ (R S : Finset (Ideal (𝓞 F))),
        R ⊆ idealAdmissibleFinset F q (2 * B) →
        S ⊆ idealAdmissibleFinset F q (2 * X) →
      ∀ (u v lam : Ideal (𝓞 F) → ℂ),
        (∀ a ∈ R, ‖u a‖ ≤ 1) → (∀ b ∈ S, ‖v b‖ ≤ 1) →
        ∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2 ≤
          C * Real.rpow (B * max 1 X) η *
            min (B + Real.rpow (max 1 X) α) (max 1 X + Real.rpow B α) *
              ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  intro η hη
  obtain ⟨Cd, hCd, hd⟩ := SplitPrefixEnvelope.direct_prefix_bound F c Q q hcq
    α hα hExponent η hη
  obtain ⟨Ct, hCt, ht⟩ := SplitPrefixEnvelope.transposed_prefix_bound F c Q q
    hq hcq hreciprocity α hα hExponent η hη
  refine ⟨max Cd Ct, le_trans hCd (le_max_left _ _), ?_⟩
  intro B X hB hX R S hR hS u v lam hu hv
  let d : ℝ := B + Real.rpow (max 1 X) α
  let t : ℝ := max 1 X + Real.rpow B α
  let P : ℝ := Real.rpow (B * max 1 X) η
  let E : ℝ := ∑ b ∈ S, ‖lam b‖ ^ 2
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have hdirect : (∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2)
      ≤ max Cd Ct * P * d * E := by
    calc
      _ ≤ Cd * P * d * E := hd B X hB hX R S hR hS u v lam hu hv
      _ = Cd * (P * d * E) := by ring
      _ ≤ max Cd Ct * (P * d * E) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max Cd Ct * P * d * E := by ring
  have htrans : (∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2)
      ≤ max Cd Ct * P * t * E := by
    calc
      _ ≤ Ct * P * t * E := ht B X hB hX R S hR hS u v lam hu hv
      _ = Ct * (P * t * E) := by ring
      _ ≤ max Cd Ct * (P * t * E) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = max Cd Ct * P * t * E := by ring
  by_cases hdt : d ≤ t
  · simpa only [d, t, P, E, min_eq_left hdt] using hdirect
  · have htd : t ≤ d := le_of_not_ge hdt
    simpa only [d, t, P, E, min_eq_right htd] using htrans

end DedekindZetaZeroFree.LargeSieve.Sieve

end
