module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PowerfulSquarefreeFactorization
public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators
public import DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection
public import DedekindZetaZeroFree.Theta.Profiles.ReflectionGaussianAndSixthUnitInvariance

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer
noncomputable section
open scoped NumberField Classical Pointwise nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]

def dyadIndices (X : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Nat.ceil X + 1)).product (Finset.range (Nat.ceil X + 1))).filter
    (fun t => (2 : ℝ) ^ t.1 * (2 : ℝ) ^ t.2 ≤ X)

def rawDyadMass (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (u : A.Rˣ) (Z : ℝ) (p q : ℕ) : ℝ :=
  ∑' h : A.Exterior, ∑' d : A.Exterior,
    if Powerful h.val ∧ Squarefree d.val ∧ h.val ⊔ d.val = ⊤ ∧
        (2 : ℝ) ^ p ≤ A.exteriorNorm h ∧ A.exteriorNorm h < 2 * (2 : ℝ) ^ p ∧
        (2 : ℝ) ^ q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * (2 : ℝ) ^ q then
      ‖ThetaReflectionData.forwardB A D
        ⟨(u : A.R) * D.generator h * D.generator d,
          mul_ne_zero (mul_ne_zero u.ne_zero (D.generates h).1) (D.generates d).1⟩ Z‖ ^ 2
    else 0

private theorem bounded_finite (A : SArithmeticData F) (X : ℝ) :
    {I : A.Exterior | A.exteriorNorm I ≤ X}.Finite := by
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Nat.ceil X)).preimage
    Subtype.val_injective.injOn).subset ?_
  intro I hI
  change Ideal.absNorm I.val ≤ Nat.ceil X
  exact_mod_cast (show (Ideal.absNorm I.val : ℝ) ≤ (Nat.ceil X : ℝ) from
    hI.trans (Nat.le_ceil X))

 def rawPair (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (u : A.Rˣ) (Z : ℝ) (p q : ℕ) (hd : A.Exterior × A.Exterior) : ℝ :=
  if Powerful hd.1.val ∧ Squarefree hd.2.val ∧ hd.1.val ⊔ hd.2.val = ⊤ ∧
      (2 : ℝ) ^ p ≤ A.exteriorNorm hd.1 ∧ A.exteriorNorm hd.1 < 2 * (2 : ℝ) ^ p ∧
      (2 : ℝ) ^ q ≤ A.exteriorNorm hd.2 ∧ A.exteriorNorm hd.2 < 2 * (2 : ℝ) ^ q then
    ‖ThetaReflectionData.forwardB A D
      ⟨(u : A.R) * D.generator hd.1 * D.generator hd.2,
        mul_ne_zero (mul_ne_zero u.ne_zero (D.generates hd.1).1) (D.generates hd.2).1⟩ Z‖ ^ 2
  else 0

private theorem rawPair_nonneg (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.Rˣ) (Z : ℝ)
    (p q : ℕ) (hd : A.Exterior × A.Exterior) : 0 ≤ rawPair A D u Z p q hd := by
  unfold rawPair
  split_ifs <;> positivity

private theorem rawPair_summable (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.Rˣ) (Z : ℝ) (p q : ℕ) :
    Summable (rawPair A D u Z p q) := by
  apply summable_of_hasFiniteSupport
  refine ((bounded_finite A (2 * (2 : ℝ) ^ p)).prod
    (bounded_finite A (2 * (2 : ℝ) ^ q))).subset ?_
  intro hd hh
  change rawPair A D u Z p q hd ≠ 0 at hh
  unfold rawPair at hh
  split_ifs at hh with h
  · exact ⟨h.2.2.2.2.1.le, h.2.2.2.2.2.2.le⟩
  · exact False.elim (hh rfl)

private theorem generator_product_B (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) (hL : A.IsSUnitIsotropicComplement H L)
    (hgen : ∀ I, A.IsAllowed L (ThetaReflectionData.rowUnit A
      ⟨D.generator I, (D.generates I).1⟩))
    (hchar : ThetaReflectionData.SixthUnitCharacterCompatibility A D)
    (u : A.Rˣ) (Z : ℝ) (I h d : A.Exterior) (hI : I.val = h.val * d.val) :
    ThetaReflectionData.forwardB A D
      ⟨(u : A.R) * D.generator I, mul_ne_zero u.ne_zero (D.generates I).1⟩ Z =
    ThetaReflectionData.forwardB A D
      ⟨(u : A.R) * D.generator h * D.generator d,
        mul_ne_zero (mul_ne_zero u.ne_zero (D.generates h).1) (D.generates d).1⟩ Z := by
  let a := ThetaReflectionData.rowUnit A ⟨D.generator I, (D.generates I).1⟩
  let b := ThetaReflectionData.rowUnit A
    ⟨D.generator h * D.generator d, mul_ne_zero (D.generates h).1 (D.generates d).1⟩
  have hg : A.Generates I (D.generator h * D.generator d) := by
    refine ⟨mul_ne_zero (D.generates h).1 (D.generates d).1, ?_⟩
    rw [← Ideal.span_singleton_mul_span_singleton, (D.generates h).2,
      (D.generates d).2]
    simp only [SArithmeticData.extendIdeal, hI, Ideal.map_mul]
  have hb : A.IsAllowed L b := by
    have he : b = ThetaReflectionData.rowUnit A ⟨D.generator h, (D.generates h).1⟩ *
        ThetaReflectionData.rowUnit A ⟨D.generator d, (D.generates d).1⟩ := by
      apply Units.ext
      rfl
    rw [he, SArithmeticData.IsAllowed, map_mul]
    exact L.mul_mem (hgen h) (hgen d)
  have ha' : A.IsAllowedGenerator L (A.extendIdeal I : FractionalIdeal A.R⁰ F) a := by
    refine ⟨?_, hgen I⟩
    rw [← (D.generates I).2, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hb' : A.IsAllowedGenerator L (A.extendIdeal I : FractionalIdeal A.R⁰ F) b := by
    refine ⟨?_, hb⟩
    rw [← hg.2, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨ε, hε, he⟩ := A.allowed_generator_unique_mod_sixth hCl H L hL _ a b ha' hb'
  let v : A.Rˣ := A.unitEquiv ⟨ε, hε⟩
  have hv : D.generator I = (v : A.R) ^ 6 * (D.generator h * D.generator d) := by
    apply Subtype.ext
    have hh := congrArg (fun x : Fˣ => (x : F)) he
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val] at hh
    have heq := (eq_div_iff b.ne_zero).mp hh
    exact heq.symm.trans (by rfl)
  have hr : (⟨(u : A.R) * D.generator I,
      mul_ne_zero u.ne_zero (D.generates I).1⟩ : ThetaReflectionData.Row A) =
      ThetaReflectionData.sixthTranslate A v
        ⟨(u : A.R) * D.generator h * D.generator d,
          mul_ne_zero (mul_ne_zero u.ne_zero (D.generates h).1) (D.generates d).1⟩ := by
    apply Subtype.ext
    simp only [ThetaReflectionData.sixthTranslate, hv]
    ring
  rw [hr, ThetaReflectionData.forwardB_sixthTranslate A D hchar]

private theorem factors_exist (A : SArithmeticData F) (I : A.Exterior) :
    ∃ hd : A.Exterior × A.Exterior, I.val = hd.1.val * hd.2.val ∧
      Powerful hd.1.val ∧ Squarefree hd.2.val ∧ hd.1.val ⊔ hd.2.val = ⊤ := by
  obtain ⟨⟨h, d⟩, hf, _⟩ := unique_coprime_powerful_squarefree_decomposition I.val I.property.1
  obtain ⟨hh, hd⟩ := exterior_of_powerful_squarefree_factorization I.property.2 hf.1
  exact ⟨(⟨h.val, h.property, hh⟩, ⟨d.val, d.property, hd⟩), hf⟩

private theorem norm_dyad (A : SArithmeticData F) (I : A.Exterior) :
    (2 : ℝ) ^ (Ideal.absNorm I.val).log2 ≤ A.exteriorNorm I ∧
      A.exteriorNorm I < 2 * (2 : ℝ) ^ (Ideal.absNorm I.val).log2 := by
  have hn : Ideal.absNorm I.val ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr I.property.1
  change (2 : ℝ) ^ (Ideal.absNorm I.val).log2 ≤ (Ideal.absNorm I.val : ℝ) ∧
    (Ideal.absNorm I.val : ℝ) < 2 * (2 : ℝ) ^ (Ideal.absNorm I.val).log2
  constructor
  · exact_mod_cast Nat.log2_self_le hn
  · have hh := Nat.lt_log2_self (n := Ideal.absNorm I.val)
    rw [pow_succ, mul_comm] at hh
    exact_mod_cast hh

private theorem dyad_mem (A : SArithmeticData F) (X : ℝ)
    (I h d : A.Exterior) (hI : I.val = h.val * d.val) (hX : A.exteriorNorm I ≤ X) :
    ((Ideal.absNorm h.val).log2, (Ideal.absNorm d.val).log2) ∈ dyadIndices X := by
  have hnorm : A.exteriorNorm I = A.exteriorNorm h * A.exteriorNorm d := by
    simp only [SArithmeticData.exteriorNorm, idealNorm, hI, map_mul, Nat.cast_mul]
  have hh := norm_dyad A h
  have hd := norm_dyad A d
  have hh1 := idealNorm_ge_one h.val h.property.1
  have hd1 := idealNorm_ge_one d.val d.property.1
  have hhX : A.exteriorNorm h ≤ X := by nlinarith
  have hdX : A.exteriorNorm d ≤ X := by nlinarith
  have hb (J : A.Exterior) (hJ : A.exteriorNorm J ≤ X) :
      (Ideal.absNorm J.val).log2 < Nat.ceil X + 1 := by
    have hn : Ideal.absNorm J.val ≤ Nat.ceil X := by
      exact_mod_cast (show (Ideal.absNorm J.val : ℝ) ≤ (Nat.ceil X : ℝ) from
        hJ.trans (Nat.le_ceil X))
    exact Nat.lt_succ_of_le ((Nat.log2_le_self _).trans hn)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hb h hhX),
    Finset.mem_range.mpr (hb d hdX)⟩, ?_⟩
  exact (mul_le_mul hh.1 hd.1 (by positivity) (A.exteriorNorm_pos h).le).trans
    (hnorm ▸ hX)

theorem canonical_mass_le_sum_dyads
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) (hL : A.IsSUnitIsotropicComplement H L)
    (hgen : ∀ I, A.IsAllowed L (ThetaReflectionData.rowUnit A
      ⟨D.generator I, (D.generates I).1⟩))
    (hchar : ThetaReflectionData.SixthUnitCharacterCompatibility A D)
    (U : Finset A.Rˣ) (X Z : ℝ) (hX : 0 < X) :
    (∑ u ∈ U, ∑' I : A.Exterior,
      if A.exteriorNorm I ≤ X then
        ‖ThetaReflectionData.forwardB A D
          ⟨(u : A.R) * D.generator I, mul_ne_zero u.ne_zero (D.generates I).1⟩ Z‖ ^ 2
      else 0) ≤
      ∑ u ∈ U, ∑ pq ∈ dyadIndices X, rawDyadMass A D u Z pq.1 pq.2 := by
  classical
  apply Finset.sum_le_sum
  intro u hu
  let S := {I : A.Exterior | A.exteriorNorm I ≤ X}
  letI : Fintype S := (bounded_finite A X).fintype
  let T := {pq // pq ∈ dyadIndices X}
  let hd : A.Exterior → A.Exterior × A.Exterior := fun I => (factors_exist A I).choose
  have hf (I : A.Exterior) : I.val = (hd I).1.val * (hd I).2.val ∧
      Powerful (hd I).1.val ∧ Squarefree (hd I).2.val ∧
      (hd I).1.val ⊔ (hd I).2.val = ⊤ := (factors_exist A I).choose_spec
  let e : S → T × (A.Exterior × A.Exterior) := fun I =>
    (⟨((Ideal.absNorm (hd I.val).1.val).log2, (Ideal.absNorm (hd I.val).2.val).log2),
      dyad_mem A X I.val (hd I.val).1 (hd I.val).2 (hf I.val).1 I.property⟩, hd I.val)
  have he : Function.Injective e := by
    intro I J hij
    have hh : hd I.val = hd J.val := congrArg Prod.snd hij
    apply Subtype.ext
    apply Subtype.ext
    rw [(hf I.val).1, (hf J.val).1, hh]
  let g : T × (A.Exterior × A.Exterior) → ℝ := fun t =>
    rawPair A D u Z t.1.val.1 t.1.val.2 t.2
  have hg0 : 0 ≤ g := fun t => rawPair_nonneg A D u Z _ _ _
  have hgs : Summable g := by
    apply (summable_prod_of_nonneg hg0).mpr
    exact ⟨fun pq => rawPair_summable A D u Z pq.val.1 pq.val.2,
      Summable.of_finite⟩
  let f : A.Exterior → ℝ := fun I =>
    if A.exteriorNorm I ≤ X then
      ‖ThetaReflectionData.forwardB A D
        ⟨(u : A.R) * D.generator I, mul_ne_zero u.ne_zero (D.generates I).1⟩ Z‖ ^ 2
    else 0
  have hleft : (∑' I : A.Exterior, f I) = ∑' I : S, f I.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro I hI
    by_contra hn
    change ¬ A.exteriorNorm I ≤ X at hn
    change f I ≠ 0 at hI
    exact hI (by simp only [f, if_neg hn])
  have hpoint (I : S) : f I.val ≤ g (e I) := by
    have hh := norm_dyad A (hd I.val).1
    have hj := norm_dyad A (hd I.val).2
    change f I.val ≤ rawPair A D u Z _ _ (hd I.val)
    rw [rawPair, if_pos ⟨(hf I.val).2.1, (hf I.val).2.2.1,
      (hf I.val).2.2.2, hh.1, hh.2, hj.1, hj.2⟩]
    have hIx : A.exteriorNorm I.val ≤ X := I.property
    simp only [f, if_pos hIx]
    rw [generator_product_B A D hCl H L hL hgen hchar u Z
      I.val (hd I.val).1 (hd I.val).2 (hf I.val).1]
  have hbound := Summable.tsum_le_tsum_of_inj e he (fun t ht => hg0 t) hpoint
    (Summable.of_finite) hgs
  change (∑' I : A.Exterior, f I) ≤ _
  rw [hleft]
  apply hbound.trans_eq
  rw [hgs.tsum_prod, tsum_fintype]
  simp only [g]
  have hraw (pq : T) :
      (∑' t : A.Exterior × A.Exterior,
        rawPair A D u Z pq.val.1 pq.val.2 t) =
        rawDyadMass A D u Z pq.val.1 pq.val.2 :=
    (rawPair_summable A D u Z pq.val.1 pq.val.2).tsum_prod
  simp_rw [hraw]
  exact Finset.sum_coe_sort (dyadIndices X)
    (fun pq => rawDyadMass A D u Z pq.1 pq.2)

end
end DedekindZetaZeroFree.RepresentationTheory.ActualRowTransfer
