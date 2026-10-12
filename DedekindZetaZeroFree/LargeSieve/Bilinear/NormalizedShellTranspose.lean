module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.NormalizedReciprocity
public import DedekindZetaZeroFree.LargeSieve.Exponents.EndpointExtension
public import DedekindZetaZeroFree.Analysis.FiniteMatrixDualityAndPhases
public import DedekindZetaZeroFree.Analysis.PartitionedQuadraticForms
public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormPartition
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

private lemma transpose_partition {A : Type*} [DecidableEq A]
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

private lemma transpose_partition_disjoint {A : Type*} [DecidableEq A]
    (R : Finset A) (blocks : ℕ → Finset A) (P : Finset ℕ)
    (h : Set.PairwiseDisjoint (↑P : Set ℕ) blocks) :
    Set.PairwiseDisjoint (↑P : Set ℕ) (fun i => R ∩ blocks i) := by
  intro i hi j hj hij
  exact (h hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right

private lemma transpose_admissible
    (F : Type) [Field F] [NumberField F] (c q : Ideal (𝓞 F))
    (hcq : c ∣ q) (B : ℝ) (hB : 1 ≤ B) (R : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ paperShell F q B ∨ (B = 1 ∧ R ⊆ {⊤})) :
    R ⊆ idealAdmissibleFinset F c (2 * B) ∧
      ∀ a ∈ R, Squarefree a ∧ a ⊔ q = ⊤ := by
  have hc : q ≤ c := Ideal.dvd_iff_le.mp hcq
  rcases hR with hR | ⟨rfl, hR⟩
  · have ha : ∀ a ∈ R, Squarefree a ∧ a ⊔ q = ⊤ ∧
        (Ideal.absNorm a : ℝ) ≤ 2 * B := by
      intro a ha
      obtain ⟨hsf, hcop, _, hnorm⟩ := (mem_paperShell F q B a).mp (hR ha)
      exact ⟨hsf, hcop, hnorm⟩
    refine ⟨?_, fun a h => ⟨(ha a h).1, (ha a h).2.1⟩⟩
    intro a h
    exact (mem_idealAdmissibleFinset F c (2 * B) a).mpr
      ⟨(ha a h).1, top_unique (by rw [← (ha a h).2.1]; exact sup_le_sup_left hc a),
        (ha a h).2.2⟩
  · have ha : ∀ a ∈ R, a = ⊤ := fun a h => Finset.mem_singleton.mp (hR h)
    constructor
    · intro a h
      rw [ha a h, top_mem_idealAdmissibleFinset_iff]; norm_num
    · intro a h
      rw [ha a h]
      exact ⟨by simpa [Ideal.one_eq_top] using squarefree_one (R := Ideal (𝓞 F)), by simp⟩

private lemma transpose_form_eq {A B : Type*} [DecidableEq A] [DecidableEq B]
    (R : Finset A) (S : Finset B) (K : B → A → ℂ) (lam : B → ℂ) :
    (∑ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2) =
      ‖(Matrix.toEuclideanLin (fun (a : R) (b : S) => K b a)).toContinuousLinearMap
        (WithLp.toLp 2 (fun b : S => lam b) : EuclideanSpace ℂ S)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_subtype (s := R) (p := fun a => a ∈ R) (fun _ => Iff.rfl)
    (f := fun a => ‖∑ b ∈ S, lam b * K b a‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  change (∑ b ∈ S, lam b * K b a) = ∑ b : S, K b a * lam b
  rw [Finset.sum_subtype (s := S) (p := fun b => b ∈ S) (fun _ => Iff.rfl)
    (f := fun b => lam b * K b a)]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private lemma transpose_energy_eq {B : Type*} [DecidableEq B]
    (S : Finset B) (lam : B → ℂ) :
    (∑ b ∈ S, ‖lam b‖ ^ 2) =
      ‖(WithLp.toLp 2 (fun b : S => lam b) : EuclideanSpace ℂ S)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_subtype (s := S) (p := fun b => b ∈ S) (fun _ => Iff.rfl)
    (f := fun b => ‖lam b‖ ^ 2)]

private lemma transpose_norm_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (R : Finset A) (S : Finset B) (K : B → A → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ lam : B → ℂ, ∑ a ∈ R, ‖∑ b ∈ S, lam b * K b a‖ ^ 2 ≤
      D * ∑ b ∈ S, ‖lam b‖ ^ 2) :
    ‖(Matrix.toEuclideanLin (fun (a : R) (b : S) => K b a)).toContinuousLinearMap‖ ^ 2 ≤ D := by
  let T := (Matrix.toEuclideanLin (fun (a : R) (b : S) => K b a)).toContinuousLinearMap
  have hT : ‖T‖ ≤ Real.sqrt D := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg D)
    intro v
    let lam : B → ℂ := fun b => if hb : b ∈ S then v ⟨b, hb⟩ else 0
    have hv : (WithLp.toLp 2 (fun b : S => lam b) : EuclideanSpace ℂ S) = v := by
      ext b
      simp [lam]
    have hh := h lam
    rw [transpose_form_eq, transpose_energy_eq, hv] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa [T, mul_pow, Real.sq_sqrt hD] using hh
  have := pow_le_pow_left₀ (norm_nonneg T) hT 2
  simpa [T, Real.sq_sqrt hD] using this

private lemma transpose_reverse_bound
    (F : Type) [Field F] [NumberField F] (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (α e C : ℝ) (he : 0 < e) (hC : 1 ≤ C)
    (hexp : ∀ (i j : ℕ) (R S : Finset (Ideal (𝓞 F))),
      R ⊆ idealDyadicBlock F c i → S ⊆ idealDyadicBlock F c j →
      ∀ lam : Ideal (𝓞 F) → ℂ,
      ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤
        C * Real.rpow (dyadicScale i * dyadicScale j) e *
          (dyadicScale i + Real.rpow (dyadicScale j) α) * ∑ b ∈ S, ‖lam b‖ ^ 2)
    (ha : 0 ≤ α) (B X : ℝ) (hB : 1 ≤ B) (hX : 1 ≤ X)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ idealAdmissibleFinset F c (2 * B))
    (hS : S ⊆ idealAdmissibleFinset F c (2 * X))
    (lam : Ideal (𝓞 F) → ℂ) :
    ∑ b ∈ S, ‖∑ a ∈ R, lam a * (Q.χ a) b‖ ^ 2 ≤
      (2 + 1 / (e * Real.log 2)) ^ 2 * C *
        Real.rpow (4 * B * X) (2 * e) * (2 * X + Real.rpow (2 * B) α) *
          ∑ a ∈ R, ‖lam a‖ ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h2B : 1 ≤ 2 * B := by linarith
  have h2X : 1 ≤ 2 * X := by linarith
  let P := Finset.range (Vendor.dyadicLength (2 * X) + 1)
  let T := Finset.range (Vendor.dyadicLength (2 * B) + 1)
  let row := fun i => S ∩ clippedDyadicBlock F c (2 * X) i
  let col := fun j => R ∩ clippedDyadicBlock F c (2 * B) j
  let U := C * Real.rpow (4 * B * X) e * (2 * X + Real.rpow (2 * B) α)
  have hU : 0 ≤ U := by
    dsimp [U]
    have : 0 ≤ C := by linarith
    positivity
  have hpart := Vendor.finite_partition_quadratic_bound S R P T row col
    (transpose_partition S _ _ _ (biUnion_clippedDyadicBlock F c (2 * X) h2X) hS)
    (transpose_partition R _ _ _ (biUnion_clippedDyadicBlock F c (2 * B) h2B) hR)
    (transpose_partition_disjoint S _ _ (pairwiseDisjoint_clippedDyadicBlock F c (2 * X) h2X))
    (transpose_partition_disjoint R _ _ (pairwiseDisjoint_clippedDyadicBlock F c (2 * B) h2B))
    (fun a b => (Q.χ a) b) lam U hU (by
      intro i hi j hj
      have hi' := dyadicScale_bounds (2 * X) h2X i hi
      have hj' := dyadicScale_bounds (2 * B) h2B j hj
      have hh := hexp i j (row i) (col j)
        (fun a ha => clippedDyadicBlock_subset_idealDyadicBlock F c (2 * X) i
          (Finset.mem_inter.mp ha).2)
        (fun a ha => clippedDyadicBlock_subset_idealDyadicBlock F c (2 * B) j
          (Finset.mem_inter.mp ha).2) lam
      refine hh.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      have hm : dyadicScale i * dyadicScale j ≤ 4 * B * X := by
        calc _ ≤ (2 * X) * (2 * B) := mul_le_mul hi'.2 hj'.2 (by linarith [hj'.1]) (by positivity)
             _ = _ := by ring
      have hp : Real.rpow (dyadicScale i * dyadicScale j) e ≤ Real.rpow (4 * B * X) e := by
        simp only [Real.rpow_eq_pow]
        exact Real.rpow_le_rpow (by nlinarith [hi'.1, hj'.1]) hm he.le
      have hs : dyadicScale i + Real.rpow (dyadicScale j) α ≤ 2 * X + Real.rpow (2 * B) α := by
        simp only [Real.rpow_eq_pow]
        exact add_le_add hi'.2 (Real.rpow_le_rpow (by linarith [hj'.1]) hj'.2 ha)
      have hi0 : 0 ≤ dyadicScale i := by linarith [hi'.1]
      have hj0 : 0 ≤ dyadicScale j := by linarith [hj'.1]
      have hC0 : 0 ≤ C := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC0) hs
        (by simp only [Real.rpow_eq_pow]; positivity)
        (by simp only [Real.rpow_eq_pow]; positivity))
  have hk : 0 ≤ 2 + 1 / (e * Real.log 2) :=
    (Vendor.dyadicLength_small_power_constant_pos he).le
  have hp : (P.card : ℝ) * (T.card : ℝ) ≤
      (2 + 1 / (e * Real.log 2)) ^ 2 * Real.rpow (4 * B * X) e := by
    have hh := mul_le_mul (Vendor.dyadicLength_small_power he h2X)
      (Vendor.dyadicLength_small_power he h2B)
      (by positivity : (0 : ℝ) ≤ (Vendor.dyadicLength (2 * B) : ℝ) + 1)
      (by positivity : 0 ≤ (2 + 1 / (e * Real.log 2)) * (2 * X) ^ e)
    have hid : Real.rpow (4 * B * X) e = (2 * X) ^ e * (2 * B) ^ e := by
      rw [Real.rpow_eq_pow, show 4 * B * X = (2 * X) * (2 * B) by ring,
        Real.mul_rpow (by positivity) (by positivity)]
    simp only [Real.rpow_eq_pow] at hid ⊢
    rw [hid]
    simp only [P, T, Finset.card_range, Nat.cast_add, Nat.cast_one]
    convert hh using 1 <;> ring

  refine hpart.trans ?_
  have hh := mul_le_mul_of_nonneg_right hp hU
  have hid : Real.rpow (4 * B * X) e * Real.rpow (4 * B * X) e =
      Real.rpow (4 * B * X) (2 * e) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by positivity)]
    congr 1; ring
  have hh' : (P.card : ℝ) * (T.card : ℝ) * U ≤
      (2 + 1 / (e * Real.log 2)) ^ 2 * C *
        Real.rpow (4 * B * X) (2 * e) * (2 * X + Real.rpow (2 * B) α) := by
    simp only [Real.rpow_eq_pow] at hid ⊢ hh
    rw [← hid]
    convert hh using 1 <;> dsimp [U] <;> ring
  exact mul_le_mul_of_nonneg_right hh' (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem bilinear_normalized_shell_transpose
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hreciprocity : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b))
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (B X : ℝ), 1 ≤ B → 1 ≤ X →
      ∀ (R S : Finset (Ideal (𝓞 F))),
        (R ⊆ paperShell F q B ∨ (B = 1 ∧ R ⊆ {⊤})) →
        (S ⊆ paperShell F q X ∨ (X = 1 ∧ S ⊆ {⊤})) →
        ∀ lam : Ideal (𝓞 F) → ℂ,
          ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤
            C * Real.rpow (B * X) η * (X + Real.rpow B α) *
              ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  intro η hη
  let e := η / 2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨Cext, hCext, hexp⟩ := bilinear_endpoint_exponent_extension F c Q α hα hExponent e he
  letI : Group Q.G := Q.instGroup
  letI : Finite Q.G := Q.instFinite
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  let k := 2 + 1 / (e * Real.log 2)
  let D := (Fintype.card Q.G : ℝ) ^ 2 * k ^ 2 * Cext * (4 : ℝ) ^ η * (2 : ℝ) ^ α
  refine ⟨max 1 D, le_max_left _ _, ?_⟩
  intro B X hB hX R S hR hS lam
  obtain ⟨hRc, hRq⟩ := transpose_admissible F c q hcq B hB R hR
  obtain ⟨hSc, hSq⟩ := transpose_admissible F c q hcq X hX S hS
  let A : Matrix R S ℂ := fun a b => (Q.χ b) a
  let A' : Matrix S R ℂ := fun b a => (Q.χ a) b
  let U := k ^ 2 * Cext * Real.rpow (4 * B * X) (2 * e) *
    (2 * X + Real.rpow (2 * B) α)
  have hB0 : 0 ≤ B := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hC0 : 0 ≤ Cext := by linarith
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hrev : ‖A'.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤ U := by
    apply transpose_norm_bound S R (fun a b => (Q.χ a) b) U hU
    intro l
    exact transpose_reverse_bound F c Q α e Cext he hCext hexp
      (by linarith [hα.1]) B X hB hX R S hRc hSc l
  have hphase : ∀ g h : Q.G, ‖Q.C h g‖ ≤ 1 := by
    intro g h
    have h2 := congrArg norm (Q.C_sq h g)
    rw [norm_pow, norm_one] at h2
    nlinarith [norm_nonneg (Q.C h g)]
  have hduality := Vendor.FiniteOperator.separated_phase_norm_le A A'
    (fun a => Q.cls a) (fun b => Q.cls b) (fun g h => Q.C h g) hphase (by
      intro a b
      dsimp [A, A']
      rw [hreciprocity b a (hSq b b.2).1 (hSq b b.2).2 (hRq a a.2).1 (hRq a a.2).2]
      ring)
  have hbound : ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤
      (Fintype.card Q.G : ℝ) ^ 2 * U :=
    hduality.trans (mul_le_mul_of_nonneg_left hrev (sq_nonneg _))
  have harith : (Fintype.card Q.G : ℝ) ^ 2 * U ≤
      max 1 D * Real.rpow (B * X) η * (X + Real.rpow B α) := by
    have heq : 2 * e = η := by dsimp [e]; ring
    have hid : (4 * B * X) ^ (2 * e) = (4 : ℝ) ^ η * (B * X) ^ η := by
      rw [heq, show 4 * B * X = 4 * (B * X) by ring,
        Real.mul_rpow (by norm_num) (mul_nonneg hB0 hX0)]
    have h2a : (2 : ℝ) ≤ (2 : ℝ) ^ α := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα.1
      simpa only [Real.rpow_one] using hh
    have hs : 2 * X + (2 * B) ^ α ≤ (2 : ℝ) ^ α * (X + B ^ α) := by
      rw [Real.mul_rpow (by norm_num) hB0, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right h2a hX0) le_rfl
    have hg : 0 ≤ (Fintype.card Q.G : ℝ) ^ 2 * k ^ 2 * Cext * (4 * B * X) ^ (2 * e) := by
      positivity
    have hh := mul_le_mul_of_nonneg_left hs hg
    have hh' : (Fintype.card Q.G : ℝ) ^ 2 * U ≤
        D * (B * X) ^ η * (X + B ^ α) := by
      dsimp [U, D]
      rw [hid]
      rw [hid] at hh
      convert hh using 1 <;> ring
    refine hh'.trans ?_
    simp only [Real.rpow_eq_pow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 D) (by positivity)) (by positivity)
  rw [transpose_form_eq, transpose_energy_eq]
  let v : EuclideanSpace ℂ S := WithLp.toLp 2 (fun b : S => lam b)
  calc ‖A.toEuclideanLin.toContinuousLinearMap v‖ ^ 2
      ≤ (‖A.toEuclideanLin.toContinuousLinearMap‖ * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
    _ = ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ ≤ (max 1 D * Real.rpow (B * X) η * (X + Real.rpow B α)) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hbound.trans harith) (sq_nonneg _)

theorem bilinear_normalized_shell_transpose_contractions
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hreciprocity : ∀ a b : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
      Squarefree b → b ⊔ q = ⊤ →
      (Q.χ a) b = (Q.χ b) a * Q.C (Q.cls a) (Q.cls b))
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hExponent : HasSieveExponent F c Q α) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
      ∀ (B X : ℝ), 1 ≤ B → 1 ≤ X →
      ∀ (R S : Finset (Ideal (𝓞 F))),
        (R ⊆ paperShell F q B ∨ (B = 1 ∧ R ⊆ {⊤})) →
        (S ⊆ paperShell F q X ∨ (X = 1 ∧ S ⊆ {⊤})) →
        ∀ (u v lam : Ideal (𝓞 F) → ℂ),
          (∀ a ∈ R, ‖u a‖ ≤ 1) → (∀ b ∈ S, ‖v b‖ ≤ 1) →
          ∑ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2 ≤
            C * Real.rpow (B * X) η * (X + Real.rpow B α) *
              ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  intro η hη
  obtain ⟨C, hC, hmain⟩ := bilinear_normalized_shell_transpose F c Q q hq hcq hreciprocity α hα hExponent η hη
  refine ⟨C, hC, ?_⟩
  intro B X hB hX R S hR hS u v lam hu hv
  have hnorm : ∀ a ∈ R, ‖∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b‖ ^ 2
      ≤ ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by
    intro a ha
    have hrow : (∑ b ∈ S, u a * (lam b * (Q.χ b) a) * v b)
        = u a * (∑ b ∈ S, (lam b * v b) * (Q.χ b) a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_); ring
    rw [hrow, norm_mul]
    have hu' : ‖u a‖ ≤ 1 := hu a ha
    calc (‖u a‖ * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖) ^ 2
        = ‖u a‖ ^ 2 * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by ring
      _ ≤ 1 * ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hu') (by positivity)
      _ = ‖∑ b ∈ S, (lam b * v b) * (Q.χ b) a‖ ^ 2 := by ring
  have henergy_le : ∑ b ∈ S, ‖lam b * v b‖ ^ 2 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    rw [norm_mul]
    have hv' : ‖v b‖ ≤ 1 := hv b hb
    calc (‖lam b‖ * ‖v b‖) ^ 2 = ‖lam b‖ ^ 2 * ‖v b‖ ^ 2 := by ring
      _ ≤ ‖lam b‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv') (by positivity)
      _ = ‖lam b‖ ^ 2 := by ring
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hK0 : 0 ≤ C * Real.rpow (B * X) η * (X + Real.rpow B α) := by
    simp only [Real.rpow_eq_pow]
    positivity
  exact le_trans (Finset.sum_le_sum hnorm)
    (le_trans (hmain B X hB hX R S hR hS (fun b => lam b * v b))
      (mul_le_mul_of_nonneg_left henergy_le hK0))

end DedekindZetaZeroFree.LargeSieve.Sieve
