module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.NormalizedReciprocity
public import DedekindZetaZeroFree.Analysis.FiniteMatrixDualityAndPhases
public import DedekindZetaZeroFree.Analysis.PartitionedQuadraticForms
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds
public import DedekindZetaZeroFree.Analysis.QuadraticFormRestriction
public import DedekindZetaZeroFree.LargeSieve.Bilinear.BoundaryTerms.CutoffDifferencesAndDensityRows
public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormPartition

@[expose] public section

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

theorem matrix_form_eq {A B : Type*} [DecidableEq A] [DecidableEq B]
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

theorem matrix_energy_eq {B : Type*} [DecidableEq B]
    (S : Finset B) (lam : B → ℂ) :
    (∑ b ∈ S, ‖lam b‖ ^ 2) =
      ‖(WithLp.toLp 2 (fun b : S => lam b) : EuclideanSpace ℂ S)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_subtype (s := S) (p := fun b => b ∈ S) (fun _ => Iff.rfl)
    (f := fun b => ‖lam b‖ ^ 2)]

theorem matrix_norm_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
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
    rw [matrix_form_eq, matrix_energy_eq, hv] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa [T, mul_pow, Real.sq_sqrt hD] using hh
  have := pow_le_pow_left₀ (norm_nonneg T) hT 2
  simpa [T, Real.sq_sqrt hD] using this

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section
noncomputable section
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

theorem variable_partition_bound
    {α β ι κ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq ι] [DecidableEq κ]
    (R : Finset α) (C : Finset β) (P : Finset ι) (Q : Finset κ)
    (row : ι → Finset α) (col : κ → Finset β)
    (hR : R = P.biUnion row) (hC : C = Q.biUnion col)
    (hrow : Set.PairwiseDisjoint (↑P : Set ι) row)
    (hcol : Set.PairwiseDisjoint (↑Q : Set κ) col)
    (K : β → α → ℂ) (lam : β → ℂ) (B : ι → κ → ℝ) (hB : ∀ i ∈ P, ∀ j ∈ Q, 0 ≤ B i j)
    (hblock : ∀ i ∈ P, ∀ j ∈ Q,
      ∑ a ∈ row i, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 ≤
        B i j * (∑ b ∈ col j, ‖lam b‖ ^ 2)) :
    ∑ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 ≤
      (Q.card : ℝ) * (∑ i ∈ P, ∑ j ∈ Q, B i j) * (∑ b ∈ C, ‖lam b‖ ^ 2) := by
  classical

  have hcolsum : ∀ a, (∑ b ∈ C, lam b * K b a) = ∑ j ∈ Q, ∑ b ∈ col j, lam b * K b a := by
    intro a
    rw [hC, Finset.sum_biUnion hcol]

  have hpoint : ∀ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 ≤
      (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
    intro a _
    rw [hcolsum a]
    calc ‖∑ j ∈ Q, ∑ b ∈ col j, lam b * K b a‖ ^ 2
        ≤ (∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Q _) 2
      _ ≤ (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq

  have hfactor : (∑ i ∈ P, ∑ a ∈ row i,
        (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2)
      = (Q.card : ℝ) * ∑ i ∈ P, ∑ a ∈ row i,
          ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hcollapse : (∑ i ∈ P, ∑ j ∈ Q, B i j * (∑ b ∈ col j, ‖lam b‖ ^ 2))
      ≤ (∑ i ∈ P, ∑ j ∈ Q, B i j) * (∑ b ∈ C, ‖lam b‖ ^ 2) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hB i hi j hj)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      rw [hC]
      exact Finset.mem_biUnion.mpr ⟨j, hj, hb⟩
    · intro b _ _; positivity
  calc ∑ a ∈ R, ‖∑ b ∈ C, lam b * K b a‖ ^ 2
      = ∑ i ∈ P, ∑ a ∈ row i, ‖∑ b ∈ C, lam b * K b a‖ ^ 2 := by
        rw [hR, Finset.sum_biUnion hrow]
    _ ≤ ∑ i ∈ P, ∑ a ∈ row i,
          (Q.card : ℝ) * ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun a ha => ?_
        exact hpoint a (by rw [hR]; exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
    _ = (Q.card : ℝ) * ∑ i ∈ P, ∑ a ∈ row i,
          ∑ j ∈ Q, ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := hfactor
    _ = (Q.card : ℝ) * ∑ i ∈ P, ∑ j ∈ Q, ∑ a ∈ row i,
          ‖∑ b ∈ col j, lam b * K b a‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ (Q.card : ℝ) * ∑ i ∈ P, ∑ j ∈ Q, B i j * (∑ b ∈ col j, ‖lam b‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hblock i hi j hj
    _ ≤ (Q.card : ℝ) * ((∑ i ∈ P, ∑ j ∈ Q, B i j) * (∑ b ∈ C, ‖lam b‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hcollapse (by positivity)
    _ = _ := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

theorem phase_transpose_bound
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : ∀ a ∈ R, Squarefree a ∧ a ⊔ D.bad = ⊤)
    (hS : ∀ b ∈ S, Squarefree b ∧ b ⊔ D.bad = ⊤)
    (L : ℝ) (hL : 0 ≤ L)
    (hrev : ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ b ∈ S, ‖∑ a ∈ R, z a * (Q.χ a) b‖ ^ 2) ≤
        L * ∑ a ∈ R, ‖z a‖ ^ 2) :
    ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ b ∈ S, z b * (Q.χ b) a‖ ^ 2) ≤
        (Nat.card Q.G : ℝ) ^ 2 * L * ∑ b ∈ S, ‖z b‖ ^ 2 := by
  letI : Group Q.G := Q.instGroup
  letI : Finite Q.G := Q.instFinite
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  have hrec := (DedekindZetaZeroFree.LargeSieve.algebra_normalized_reciprocity F c Q D.bad
    D.bad_ne_bot D.original_dvd_bad (fun a ha hac =>
      ⟨D.index_dvd_conductor a ha hac, D.conductor_dvd_index_bad a ha hac⟩)).2.1
  let A : Matrix R S ℂ := fun a b => (Q.χ b) a
  let A' : Matrix S R ℂ := fun b a => (Q.χ a) b
  have hn : ‖A'.toEuclideanLin.toContinuousLinearMap‖ ^ 2 ≤ L :=
    matrix_norm_bound S R (fun a b => (Q.χ a) b) L hL hrev
  have hp : ∀ g h : Q.G, ‖Q.C h g‖ ≤ 1 := by
    intro g h
    have h2 := congrArg norm (Q.C_sq h g)
    rw [norm_pow, norm_one] at h2
    nlinarith [norm_nonneg (Q.C h g)]
  have hd := Vendor.FiniteOperator.separated_phase_norm_le A A'
    (fun a => Q.cls a) (fun b => Q.cls b) (fun g h => Q.C h g) hp (by
      intro a b
      dsimp [A, A']
      rw [hrec b a (hS b b.2).1 (hS b b.2).2 (hR a a.2).1 (hR a a.2).2]
      ring)
  have hh := hd.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))
  intro z
  rw [matrix_form_eq, matrix_energy_eq]
  let v : EuclideanSpace ℂ S := WithLp.toLp 2 (fun b : S => z b)
  calc
    ‖A.toEuclideanLin.toContinuousLinearMap v‖ ^ 2 ≤
        (‖A.toEuclideanLin.toContinuousLinearMap‖ * ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
    _ = ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ ≤ _ := by
      simpa only [Nat.card_eq_fintype_card] using
        mul_le_mul_of_nonneg_right hh (sq_nonneg ‖v‖)

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

theorem norm_row_le_card_mul (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (S : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤) (a : Ideal (𝓞 F)) :
    ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  have h : ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ≤ ∑ b ∈ S, ‖lam b‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun b hb => ?_))
    rw [norm_mul]
    calc ‖lam b‖ * ‖(Q.χ b) a‖ ≤ ‖lam b‖ * 1 :=
          mul_le_mul_of_nonneg_left (quadraticFamily_norm_le_one Q (hSsf b hb).1 (hSsf b hb).2 a)
            (norm_nonneg _)
      _ = ‖lam b‖ := by ring
  calc ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2 ≤ (∑ b ∈ S, ‖lam b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem sum_sq_le_card_mul_energy (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (R S : Finset (Ideal (𝓞 F))) (lam : Ideal (𝓞 F) → ℂ)
    (hSsf : ∀ b ∈ S, Squarefree b ∧ b ⊔ c = ⊤) :
    ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
      ≤ (R.card : ℝ) * (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by
  have hE0 : 0 ≤ ∑ b ∈ S, ‖lam b‖ ^ 2 := Finset.sum_nonneg (fun b _ => by positivity)
  calc ∑ a ∈ R, ‖∑ b ∈ S, lam b * (Q.χ b) a‖ ^ 2
      ≤ ∑ _a ∈ R, (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => norm_row_le_card_mul Q S lam hSsf a)
    _ = (R.card : ℝ) * ((S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (R.card : ℝ) * (S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2 := by ring

theorem core_sup_original (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) {a : Ideal (𝓞 F)} (ha : a ⊔ D.bad = ⊤) :
    a ⊔ c = ⊤ := by
  apply top_unique
  rw [← ha]
  exact sup_le_sup_left (Ideal.le_of_dvd D.original_dvd_bad) a

theorem core_shell_subset (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (T : ℝ) :
    paperShell F D.bad T ⊆ paperShell F c T := by
  intro a ha
  obtain ⟨hs, hc, hl, hu⟩ := (mem_paperShell F D.bad T a).mp ha
  exact (mem_paperShell F c T a).mpr ⟨hs, core_sup_original Q D hc, hl, hu⟩

theorem reverse_shell_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (T U : ℝ)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ paperShell F D.bad T) (hS : S ⊆ paperShell F D.bad U) :
    ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ b ∈ S, ‖∑ a ∈ R, z a * (Q.χ a) b‖ ^ 2) ≤
        B1 F c Q U T * ∑ a ∈ R, ‖z a‖ ^ 2 := by
  apply Vendor.finite_subrange_bound (paperShell F c U) S
    (paperShell F c T) R
    (hS.trans (core_shell_subset Q D U)) (hR.trans (core_shell_subset Q D T))
    (fun a b => (Q.χ a) b) _ (B1_nonneg Q U T)
  intro z
  exact Q1_le_B1_mul_energy Q U T z

theorem transposed_shell_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (T U : ℝ)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ paperShell F D.bad T) (hS : S ⊆ paperShell F D.bad U) :
    ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ b ∈ S, z b * (Q.χ b) a‖ ^ 2) ≤
        (Nat.card Q.G : ℝ) ^ 2 * B1 F c Q U T * ∑ b ∈ S, ‖z b‖ ^ 2 := by
  apply phase_transpose_bound Q D R S
    (fun a ha => ⟨((mem_paperShell F D.bad T a).mp (hR ha)).1,
      ((mem_paperShell F D.bad T a).mp (hR ha)).2.1⟩)
    (fun b hb => ⟨((mem_paperShell F D.bad U b).mp (hS hb)).1,
      ((mem_paperShell F D.bad U b).mp (hS hb)).2.1⟩)
    _ (B1_nonneg Q U T) (reverse_shell_bound Q D T U R S hR hS)

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

private theorem intersect_partition {A : Type*} [DecidableEq A]
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

private theorem intersect_disjoint {A : Type*} [DecidableEq A]
    (R : Finset A) (blocks : ℕ → Finset A) (P : Finset ℕ)
    (h : Set.PairwiseDisjoint (↑P : Set ℕ) blocks) :
    Set.PairwiseDisjoint (↑P : Set ℕ) (fun i => R ∩ blocks i) := by
  intro i hi j hj hij
  exact (h hi hj hij).mono Finset.inter_subset_right Finset.inter_subset_right

def prefixBlock (q : Ideal (𝓞 F)) (X : ℝ) (R : Finset (Ideal (𝓞 F)))
    (i : ℕ) : Finset (Ideal (𝓞 F)) := R ∩ clippedDyadicBlock F q X i

private theorem prefixBlock_zero_card (q : Ideal (𝓞 F)) (X : ℝ)
    (R : Finset (Ideal (𝓞 F))) : (prefixBlock q X R 0).card ≤ 1 := by
  have h : prefixBlock q X R 0 ⊆ {⊤} := by
    intro a ha
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp ha).2).1
  simpa using Finset.card_le_card h

def blockMajorant (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (X N : ℝ) (R S : Finset (Ideal (𝓞 F)))
    (i j : ℕ) : ℝ :=
  if i = 0 then ((prefixBlock D.bad (2 * N) S j).card : ℝ)
  else if j = 0 then ((prefixBlock D.bad X R i).card : ℝ)
  else (Nat.card Q.G : ℝ) ^ 2 * B1 F c Q ((2 : ℝ) ^ (j - 1)) ((2 : ℝ) ^ (i - 1))

theorem blockMajorant_nonneg (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (X N : ℝ) (R S : Finset (Ideal (𝓞 F)))
    (i j : ℕ) : 0 ≤ blockMajorant Q D X N R S i j := by
  unfold blockMajorant
  split_ifs <;> try positivity
  exact mul_nonneg (sq_nonneg _) (B1_nonneg Q _ _)

theorem prefixBlock_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (X N : ℝ) (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ idealAdmissibleFinset F D.bad X)
    (hS : S ⊆ idealAdmissibleFinset F D.bad (2 * N)) (i j : ℕ)
    (z : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ prefixBlock D.bad X R i,
      ‖∑ b ∈ prefixBlock D.bad (2 * N) S j, z b * (Q.χ b) a‖ ^ 2) ≤
      blockMajorant Q D X N R S i j *
        ∑ b ∈ prefixBlock D.bad (2 * N) S j, ‖z b‖ ^ 2 := by
  have hs : ∀ b ∈ prefixBlock D.bad (2 * N) S j, Squarefree b ∧ b ⊔ c = ⊤ := by
    intro b hb
    have hh := (mem_idealAdmissibleFinset F D.bad (2 * N) b).mp
      (hS (Finset.mem_inter.mp hb).1)
    exact ⟨hh.1, core_sup_original Q D hh.2.1⟩
  have hc := sum_sq_le_card_mul_energy Q (prefixBlock D.bad X R i)
    (prefixBlock D.bad (2 * N) S j) z hs
  by_cases hi : i = 0
  · subst i
    simp only [blockMajorant, if_pos rfl]
    have h0 : ((prefixBlock D.bad X R 0).card : ℝ) ≤ 1 := by
      exact_mod_cast prefixBlock_zero_card D.bad X R
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (by positivity) h0) (by positivity))
  by_cases hj : j = 0
  · subst j
    simp only [blockMajorant, if_neg hi, if_pos rfl]
    have h0 : ((prefixBlock D.bad (2 * N) S 0).card : ℝ) ≤ 1 := by
      exact_mod_cast prefixBlock_zero_card D.bad (2 * N) S
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) h0) (by positivity))
  obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  simp only [blockMajorant, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  apply transposed_shell_bound Q D ((2 : ℝ) ^ i') ((2 : ℝ) ^ j')
  · intro a ha
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp ha).2).1
  · intro b hb
    exact (Finset.mem_inter.mp (Finset.mem_inter.mp hb).2).1

theorem sum_prefixBlock_card (q : Ideal (𝓞 F)) (X : ℝ) (hX : 1 ≤ X)
    (R : Finset (Ideal (𝓞 F))) (hR : R ⊆ idealAdmissibleFinset F q X) :
    (∑ i ∈ Finset.range (Vendor.dyadicLength X + 1),
      ((prefixBlock q X R i).card : ℝ)) = (R.card : ℝ) := by
  have hp := intersect_partition R (clippedDyadicBlock F q X)
    (Finset.range (Vendor.dyadicLength X + 1)) _
    (biUnion_clippedDyadicBlock F q X hX) hR
  have hd := intersect_disjoint R (clippedDyadicBlock F q X)
    (Finset.range (Vendor.dyadicLength X + 1))
    (pairwiseDisjoint_clippedDyadicBlock F q X hX)
  have hc := Finset.card_biUnion hd
  rw [← hp] at hc
  exact_mod_cast hc.symm

theorem sum_blockMajorant (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (X N : ℝ) (hX : 1 ≤ X) (hN : 1 ≤ N)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ idealAdmissibleFinset F D.bad X)
    (hS : S ⊆ idealAdmissibleFinset F D.bad (2 * N)) :
    (∑ i ∈ Finset.range (Vendor.dyadicLength X + 1),
      ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N) + 1),
        blockMajorant Q D X N R S i j) ≤
      (R.card : ℝ) + (S.card : ℝ) +
        (Nat.card Q.G : ℝ) ^ 2 *
          (∑ i ∈ Finset.range (Vendor.dyadicLength X),
            ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
              B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i)) := by
  rw [Finset.sum_range_succ']
  have hrow0 : (∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N) + 1),
      blockMajorant Q D X N R S 0 j) = (S.card : ℝ) := by
    simp only [blockMajorant, if_pos rfl]
    exact sum_prefixBlock_card D.bad (2 * N) (by linarith) S hS
  rw [hrow0]
  have hsum : (∑ i ∈ Finset.range (Vendor.dyadicLength X),
      ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N) + 1),
        blockMajorant Q D X N R S (i + 1) j) =
      (∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ((prefixBlock D.bad X R (i + 1)).card : ℝ)) +
        (Nat.card Q.G : ℝ) ^ 2 *
          (∑ i ∈ Finset.range (Vendor.dyadicLength X),
            ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
              B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i)) := by
    simp_rw [Finset.sum_range_succ']
    simp only [blockMajorant, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      if_false, if_true, Nat.add_sub_cancel]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]
  have hr := sum_prefixBlock_card D.bad X hX R hR
  rw [Finset.sum_range_succ'] at hr
  have hle : (∑ i ∈ Finset.range (Vendor.dyadicLength X),
      ((prefixBlock D.bad X R (i + 1)).card : ℝ)) ≤ (R.card : ℝ) := by
    have : 0 ≤ ((prefixBlock D.bad X R 0).card : ℝ) := by positivity
    linarith
  linarith

theorem assembled_prefix_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) (X N : ℝ) (hX : 1 ≤ X) (hN : 1 ≤ N)
    (R S : Finset (Ideal (𝓞 F)))
    (hR : R ⊆ idealAdmissibleFinset F D.bad X)
    (hS : S ⊆ idealAdmissibleFinset F D.bad (2 * N))
    (z : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ R, ‖∑ b ∈ S, z b * (Q.χ b) a‖ ^ 2) ≤
      ((Vendor.dyadicLength (2 * N) + 1 : ℕ) : ℝ) *
        ((R.card : ℝ) + (S.card : ℝ) + (Nat.card Q.G : ℝ) ^ 2 *
          (∑ i ∈ Finset.range (Vendor.dyadicLength X),
            ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
              B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i))) *
        (∑ b ∈ S, ‖z b‖ ^ 2) := by
  have h2N : 1 ≤ 2 * N := by linarith
  have hpart := variable_partition_bound R S
    (Finset.range (Vendor.dyadicLength X + 1))
    (Finset.range (Vendor.dyadicLength (2 * N) + 1))
    (prefixBlock D.bad X R) (prefixBlock D.bad (2 * N) S)
    (intersect_partition R _ _ _ (biUnion_clippedDyadicBlock F D.bad X hX) hR)
    (intersect_partition S _ _ _ (biUnion_clippedDyadicBlock F D.bad (2 * N) h2N) hS)
    (intersect_disjoint R _ _ (pairwiseDisjoint_clippedDyadicBlock F D.bad X hX))
    (intersect_disjoint S _ _ (pairwiseDisjoint_clippedDyadicBlock F D.bad (2 * N) h2N))
    (fun b a => (Q.χ b) a) z (blockMajorant Q D X N R S)
    (fun i _ j _ => blockMajorant_nonneg Q D X N R S i j)
    (fun i _ j _ => prefixBlock_bound Q D X N R S hR hS i j z)
  simp only [Finset.card_range] at hpart
  exact hpart.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sum_blockMajorant Q D X N hX hN R S hR hS)
      (by positivity)) (by positivity))

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section

noncomputable section
open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

theorem core_prefix_operator_bound
    {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) :
    ∃ H : ℝ, 0 < H ∧ ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
      ∀ R S : Finset (Ideal (𝓞 F)),
        R ⊆ idealAdmissibleFinset F D.bad X →
        S ⊆ idealAdmissibleFinset F D.bad (2 * N) →
        ∀ z : Ideal (𝓞 F) → ℂ,
          (∑ a ∈ R, ‖∑ u ∈ S, z u * (Q.χ u) a‖ ^ 2) ≤
            H * MainBoundaryBound.shellPrefixEnvelope F c Q X N *
              (∑ u ∈ S, ‖z u‖ ^ 2) := by
  obtain ⟨C, hC, _, hcount⟩ := DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset F
  let H : ℝ := 2 * C + (Nat.card Q.G : ℝ) ^ 2
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  intro X N hX hN R S hR hS z
  have hRc : (R.card : ℝ) ≤ C * X := hcount X hX R (fun a ha =>
    ((mem_idealAdmissibleFinset F D.bad X a).mp (hR ha)).2.2)
  have hSc : (S.card : ℝ) ≤ C * (2 * N) := hcount (2 * N) (by linarith) S (fun b hb =>
    ((mem_idealAdmissibleFinset F D.bad (2 * N) b).mp (hS hb)).2.2)
  let T : ℝ := ∑ i ∈ Finset.range (Vendor.dyadicLength X),
    ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
      B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i)
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => B1_nonneg Q _ _
  have hC0 : 0 ≤ C := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hinner : (R.card : ℝ) + (S.card : ℝ) + (Nat.card Q.G : ℝ) ^ 2 * T ≤
      H * (1 + X + N + T) := by
    have hRc' : (R.card : ℝ) ≤ (2 * C) * X := by nlinarith
    have hSc' : (S.card : ℝ) ≤ (2 * C) * N := by nlinarith
    have hH2 : 2 * C ≤ H := by dsimp [H]; nlinarith [sq_nonneg (Nat.card Q.G : ℝ)]
    have hHG : (Nat.card Q.G : ℝ) ^ 2 ≤ H := by dsimp [H]; linarith
    have hx := mul_le_mul_of_nonneg_right hH2 hX0
    have hn := mul_le_mul_of_nonneg_right hH2 hN0
    have ht := mul_le_mul_of_nonneg_right hHG hT
    nlinarith
  have hh := assembled_prefix_bound Q D X N hX hN R S hR hS z
  calc
    _ ≤ ((Vendor.dyadicLength (2 * N) + 1 : ℕ) : ℝ) *
        ((R.card : ℝ) + (S.card : ℝ) + (Nat.card Q.G : ℝ) ^ 2 * T) *
        (∑ b ∈ S, ‖z b‖ ^ 2) := hh
    _ ≤ ((Vendor.dyadicLength (2 * N) + 1 : ℕ) : ℝ) *
        (H * (1 + X + N + T)) * (∑ b ∈ S, ‖z b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner (by positivity))
        (by positivity)
    _ = _ := by unfold MainBoundaryBound.shellPrefixEnvelope; dsimp [T]; ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end
