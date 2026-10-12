module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.FiniteTransform

noncomputable section
open scoped Classical

variable {K : Type*} [Field K]

abbrev Residue (R : Subring K) (a : R) := R ⧸ Ideal.span ({a} : Set R)

def residueMap (R : Subring K) (a : R) : R →+* Residue R a :=
  Ideal.Quotient.mk _

def ResidueLifts (R : Subring K) (a : R) :=
  {l : Residue R a → R // ∀ d, residueMap R a (l d) = d}

def canonicalLifts (R : Subring K) (a : R) : ResidueLifts R a :=
  ⟨Quotient.out, fun d => Quotient.out_eq d⟩

def exteriorNorm (R : Subring K) (a : R) : ℕ := Nat.card (Residue R a)

def IsTrivialOn (R : Subring K) (e : AddChar K ℂ) : Prop :=
  ∀ r : R, e (r : K) = 1

def IsPrimitiveAt (R : Subring K) (s : R) (e : AddChar K ℂ) : Prop :=
  ∀ k : R, residueMap R s k ≠ 0 →
    ∃ j : R, e ((k : K) * (j : K) / (s : K)) ≠ 1

def gaussSumWithLifts (R : Subring K) (s : R) [Fintype (Residue R s)]
    (χs : MulChar (Residue R s) ℂ) (e : AddChar K ℂ)
    (ds : ResidueLifts R s) (k : R) : ℂ :=
  ∑ d : Residue R s, χs d * e ((k : K) * (ds.val d : K) / (s : K))

def gaussSum (R : Subring K) (s : R) [Fintype (Residue R s)]
    (χs : MulChar (Residue R s) ℂ) (e : AddChar K ℂ) (k : R) : ℂ :=
  gaussSumWithLifts R s χs e (canonicalLifts R s) k

def finiteCoefficientWithLifts (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (ds : ResidueLifts R s) (vA : ResidueLifts R A) : ℂ :=
  ∑ d : Residue R s,
    if residueMap R s h = residueMap R s A * d then
      χs d * ∑ v : Residue R A, χA v *
        e (((h : K) - (A : K) * (ds.val d : K)) * (vA.val v : K) /
          ((s : K) * (A : K)))
    else 0

def finiteCoefficient (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) : ℂ :=
  finiteCoefficientWithLifts R s A h χs χA e (canonicalLifts R s) (canonicalLifts R A)

def rowTransformWithLifts (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    [Fintype (Residue R (s * A))]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (ds : ResidueLifts R s) (msA : ResidueLifts R (s * A)) : ℂ :=
  ∑ m : Residue R (s * A),
    (Real.sqrt (exteriorNorm R s) : ℂ)⁻¹ *
      gaussSumWithLifts R s χs e ds (-msA.val m) *
      χA (residueMap R A (msA.val m)) *
      e ((h : K) * (msA.val m : K) / ((s : K) * (A : K)))

def rowTransform (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    [Fintype (Residue R (s * A))]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) : ℂ :=
  rowTransformWithLifts R s A h χs χA e (canonicalLifts R s)
    (canonicalLifts R (s * A))

private theorem phase_eq (R : Subring K) (e : AddChar K ℂ)
    (he : IsTrivialOn R e) (x y : K) (r : R) (hr : x - y = (r : K)) :
    e x = e y := by
  have hx : x = y + (r : K) := by rw [← hr]; ring
  rw [hx, e.map_add_eq_mul, he r, mul_one]

private theorem residue_difference (R : Subring K) (a x y : R)
    (h : residueMap R a x = residueMap R a y) : ∃ r : R, x - y = a * r := by
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)

theorem linear_phase_eq (R : Subring K) (s : R) (hs : s ≠ 0)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (x y k : R)
    (h : residueMap R s x = residueMap R s y) :
    e ((k : K) * (x : K) / (s : K)) = e ((k : K) * (y : K) / (s : K)) := by
  obtain ⟨r, hr⟩ := residue_difference R s x y h
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs
  apply phase_eq R e he _ _ (k * r)
  have hr' : (x : K) - (y : K) = (s : K) * (r : K) := by exact_mod_cast hr
  push_cast
  rw [← sub_div, ← mul_sub, hr']
  field_simp
  <;> ring

private theorem double_phase_eq (R : Subring K) (s A h x y v w : R)
    (hs : s ≠ 0) (hA : A ≠ 0) (e : AddChar K ℂ) (he : IsTrivialOn R e)
    (hxy : residueMap R s x = residueMap R s y)
    (hvw : residueMap R A v = residueMap R A w)
    (hc : residueMap R s h = residueMap R s A * residueMap R s y) :
    e (((h : K) - (A : K) * (x : K)) * (v : K) / ((s : K) * (A : K))) =
      e (((h : K) - (A : K) * (y : K)) * (w : K) / ((s : K) * (A : K))) := by
  obtain ⟨r, hr⟩ := residue_difference R s x y hxy
  obtain ⟨t, ht⟩ := residue_difference R A v w hvw
  obtain ⟨b, hb⟩ := residue_difference R s h (A * y) (by simpa using hc)
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs
  have hA' : (A : K) ≠ 0 := by exact_mod_cast hA
  have hr' : (x : K) - (y : K) = (s : K) * (r : K) := by exact_mod_cast hr
  have ht' : (v : K) - (w : K) = (A : K) * (t : K) := by exact_mod_cast ht
  have hb' : (h : K) - (A : K) * (y : K) = (s : K) * (b : K) := by exact_mod_cast hb
  apply phase_eq R e he _ _ (b * t - r * v)
  push_cast
  have hx : (x : K) = (y : K) + (s : K) * (r : K) := by linear_combination hr'
  have hv : (v : K) = (w : K) + (A : K) * (t : K) := by linear_combination ht'
  have hh : (h : K) = (A : K) * (y : K) + (s : K) * (b : K) := by linear_combination hb'
  rw [← sub_div, hx, hv, hh]
  field_simp
  <;> ring

theorem finiteCoefficient_lifts_independent (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : IsTrivialOn R e)
    (ds : ResidueLifts R s) (vA : ResidueLifts R A) :
    finiteCoefficientWithLifts R s A h χs χA e ds vA =
      finiteCoefficient R s A h χs χA e := by
  unfold finiteCoefficient finiteCoefficientWithLifts
  apply Finset.sum_congr rfl
  intro d _
  split_ifs with hc
  · congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    apply double_phase_eq R s A h _ _ _ _ hs hA e he
    · rw [ds.property, (canonicalLifts R s).property]
    · rw [vA.property, (canonicalLifts R A).property]
    · simpa only [(canonicalLifts R s).property] using hc
  · rfl

private theorem residue_factor (R : Subring K) (s A x y : R)
    (h : residueMap R (s * A) x = residueMap R (s * A) y) :
    residueMap R s x = residueMap R s y := by
  obtain ⟨r, hr⟩ := residue_difference R (s * A) x y h
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  exact ⟨A * r, by rw [hr]; ring⟩

def residueDecomposition (R : Subring K) (s A : R)
    (ds : ResidueLifts R s) (vA : ResidueLifts R A) :
    Residue R A × Residue R s → Residue R (s * A) :=
  fun p => residueMap R (s * A) (vA.val p.1 + A * ds.val p.2)

private theorem residueDecomposition_bijective (R : Subring K) (s A : R)
    (hA : A ≠ 0) (ds : ResidueLifts R s) (vA : ResidueLifts R A) :
    Function.Bijective (residueDecomposition R s A ds vA) := by
  constructor
  · intro p q hpq
    obtain ⟨r, hr⟩ := residue_difference R (s * A) _ _ hpq
    have hv : p.1 = q.1 := by
      have hv' : residueMap R A (vA.val p.1) = residueMap R A (vA.val q.1) := by
        apply Ideal.Quotient.eq.mpr
        apply Ideal.mem_span_singleton.mpr
        refine ⟨s * r - ds.val p.2 + ds.val q.2, ?_⟩
        linear_combination hr
      simpa only [vA.property] using hv'
    apply Prod.ext hv
    have hl : vA.val p.1 = vA.val q.1 := congrArg vA.val hv
    have hj : ds.val p.2 - ds.val q.2 = s * r := by
      apply mul_left_cancel₀ hA
      rw [hl] at hr
      linear_combination hr
    have : residueMap R s (ds.val p.2) = residueMap R s (ds.val q.2) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨r, hj⟩)
    simpa only [ds.property] using this
  · intro m
    let x := (canonicalLifts R (s * A)).val m
    let v := residueMap R A x
    obtain ⟨j, hj⟩ := residue_difference R A x (vA.val v) (by rw [vA.property])
    refine ⟨(v, residueMap R s j), ?_⟩
    change residueMap R (s * A) (vA.val v + A * ds.val (residueMap R s j)) = m
    rw [← (canonicalLifts R (s * A)).property m]
    obtain ⟨r, hr⟩ := residue_difference R s (ds.val (residueMap R s j)) j
      (ds.property _)
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    change vA.val v + A * ds.val (residueMap R s j) - x = s * A * r
    linear_combination A * hr - hj

def residueAddChar (R : Subring K) (s k : R) (hs : s ≠ 0)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (ds : ResidueLifts R s) :
    AddChar (Residue R s) ℂ where
  toFun j := e ((k : K) * (ds.val j : K) / (s : K))
  map_zero_eq_one' := by
    rw [linear_phase_eq R s hs e he (ds.val 0) 0 k (by simp [ds.property])]
    simp
  map_add_eq_mul' x y := by
    rw [linear_phase_eq R s hs e he (ds.val (x + y)) (ds.val x + ds.val y) k
      (by simp [ds.property])]
    rw [Subring.coe_add, mul_add, add_div, e.map_add_eq_mul]

private theorem residue_orthogonality (R : Subring K) (s k : R) (hs : s ≠ 0)
    [Fintype (Residue R s)] (e : AddChar K ℂ) (he : IsTrivialOn R e)
    (hp : IsPrimitiveAt R s e) (ds : ResidueLifts R s) :
    (∑ j : Residue R s, e ((k : K) * (ds.val j : K) / (s : K))) =
      if residueMap R s k = 0 then (exteriorNorm R s : ℂ) else 0 := by
  let ψ := residueAddChar R s k hs e he ds
  have hz : ψ = 0 ↔ residueMap R s k = 0 := by
    constructor
    · intro h
      by_contra hk
      obtain ⟨j, hj⟩ := hp k hk
      have heq := congrArg (fun f : AddChar (Residue R s) ℂ => f (residueMap R s j)) h
      change e ((k : K) * (ds.val (residueMap R s j) : K) / (s : K)) = 1 at heq
      rw [linear_phase_eq R s hs e he _ j k (ds.property _)] at heq
      exact hj heq
    · intro hk
      ext j
      change e ((k : K) * (ds.val j : K) / (s : K)) = 1
      rw [mul_comm]
      rw [linear_phase_eq R s hs e he k 0 (ds.val j) (by simpa using hk)]
      simp
  change (∑ j, ψ j) = _
  rw [AddChar.sum_eq_ite]
  simp only [hz, exteriorNorm, Nat.card_eq_fintype_card]

def rawRowTerm (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] (χs : MulChar (Residue R s) ℂ)
    (χA : MulChar (Residue R A) ℂ) (e : AddChar K ℂ)
    (ds : ResidueLifts R s) (m : R) : ℂ :=
  gaussSumWithLifts R s χs e ds (-m) * χA (residueMap R A m) *
    e ((h : K) * (m : K) / ((s : K) * (A : K)))

private theorem rawRowTerm_eq (R : Subring K) (s A h x y : R)
    (hs : s ≠ 0) (hA : A ≠ 0) [Fintype (Residue R s)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (ds : ResidueLifts R s)
    (hxy : residueMap R (s * A) x = residueMap R (s * A) y) :
    rawRowTerm R s A h χs χA e ds x = rawRowTerm R s A h χs χA e ds y := by
  obtain ⟨r, hr⟩ := residue_difference R (s * A) x y hxy
  have hxA : residueMap R A x = residueMap R A y :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨s * r, by rw [hr]; ring⟩)
  have hxs := residue_factor R s A x y hxy
  unfold rawRowTerm
  rw [hxA]
  have hg : gaussSumWithLifts R s χs e ds (-x) =
      gaussSumWithLifts R s χs e ds (-y) := by
    unfold gaussSumWithLifts
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    simp only [Subring.coe_neg]
    rw [mul_comm (-(x : K)), mul_comm (-(y : K))]
    exact linear_phase_eq R s hs e he (-x) (-y) (ds.val d)
      (by simpa only [map_neg] using congrArg Neg.neg hxs)
  rw [hg]
  congr 1
  change e ((h : K) * (x : K) / ((s * A : R) : K)) = _
  exact linear_phase_eq R (s * A) (mul_ne_zero hs hA) e he x y h hxy

private theorem phase_split (R : Subring K) (s A h d v j : R)
    (hs : s ≠ 0) (hA : A ≠ 0) (e : AddChar K ℂ) :
    e ((-(v + A * j : R) : K) * (d : K) / (s : K)) *
      e ((h : K) * ((v + A * j : R) : K) / ((s : K) * (A : K))) =
    e (((h : K) - (A : K) * (d : K)) * (v : K) / ((s : K) * (A : K))) *
      e (((h - A * d : R) : K) * (j : K) / (s : K)) := by
  rw [← e.map_add_eq_mul, ← e.map_add_eq_mul]
  congr 1
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs
  have hA' : (A : K) ≠ 0 := by exact_mod_cast hA
  push_cast
  field_simp
  <;> ring

private theorem rawRowTerm_decomposed (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0) [Fintype (Residue R s)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (ds : ResidueLifts R s) (vA : ResidueLifts R A)
    (v : Residue R A) (j : Residue R s) :
    rawRowTerm R s A h χs χA e ds (vA.val v + A * ds.val j) =
      ∑ d : Residue R s, χs d * χA v *
        e (((h : K) - (A : K) * (ds.val d : K)) * (vA.val v : K) /
          ((s : K) * (A : K))) *
        e (((h - A * ds.val d : R) : K) * (ds.val j : K) / (s : K)) := by
  have hA0 : residueMap R A A = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  unfold rawRowTerm gaussSumWithLifts
  simp only [map_add, map_mul, hA0, zero_mul, add_zero, vA.property]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Subring.coe_neg]
  apply Finset.sum_congr rfl
  intro d _
  have ht := phase_split R s A h (ds.val d) (vA.val v) (ds.val j) hs hA e
  calc
    _ = χs d * χA v *
        (e ((-(vA.val v + A * ds.val j : R) : K) * (ds.val d : K) / (s : K)) *
          e ((h : K) * ((vA.val v + A * ds.val j : R) : K) / ((s : K) * (A : K)))) := by ring
    _ = _ := by rw [ht]; ring

private theorem raw_transform (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    [Fintype (Residue R (s * A))]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (hp : IsPrimitiveAt R s e)
    (ds : ResidueLifts R s) (vA : ResidueLifts R A) :
    (∑ m : Residue R (s * A),
      rawRowTerm R s A h χs χA e ds ((canonicalLifts R (s * A)).val m)) =
    (exteriorNorm R s : ℂ) * finiteCoefficientWithLifts R s A h χs χA e ds vA := by
  rw [← Fintype.sum_bijective (residueDecomposition R s A ds vA)
    (residueDecomposition_bijective R s A hA ds vA)
    (fun p => rawRowTerm R s A h χs χA e ds (vA.val p.1 + A * ds.val p.2))
    (fun m => rawRowTerm R s A h χs χA e ds ((canonicalLifts R (s * A)).val m))
    (fun p => rawRowTerm_eq R s A h _ _ hs hA χs χA e he ds
      (by rw [(canonicalLifts R (s * A)).property]; rfl))]
  rw [Fintype.sum_prod_type]
  simp_rw [rawRowTerm_decomposed R s A h hs hA χs χA e ds vA]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, residue_orthogonality R s _ hs e he hp ds]
  unfold finiteCoefficientWithLifts
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hc : residueMap R s (h - A * ds.val d) = 0 ↔
      residueMap R s h = residueMap R s A * d := by
    rw [map_sub, map_mul, ds.property, sub_eq_zero]
  simp only [hc]
  split_ifs with hd
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  · simp

theorem exact_finite_transform (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    [Fintype (Residue R (s * A))]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (hprimitive : IsPrimitiveAt R s e) :
    rowTransform R s A h χs χA e =
      (Real.sqrt (exteriorNorm R s) : ℂ) * finiteCoefficient R s A h χs χA e := by
  have hn : (exteriorNorm R s : ℝ) > 0 := by
    exact_mod_cast (show 0 < exteriorNorm R s by
      simp only [exteriorNorm, Nat.card_eq_fintype_card]
      exact Fintype.card_pos)
  have hq : (Real.sqrt (exteriorNorm R s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  have hsq : (Real.sqrt (exteriorNorm R s) : ℂ) ^ 2 = (exteriorNorm R s : ℂ) := by
    exact_mod_cast Real.sq_sqrt hn.le
  unfold rowTransform rowTransformWithLifts
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  simp only [← mul_assoc]
  change (Real.sqrt (exteriorNorm R s) : ℂ)⁻¹ *
    (∑ m : Residue R (s * A), rawRowTerm R s A h χs χA e
      (canonicalLifts R s) ((canonicalLifts R (s * A)).val m)) = _
  rw [raw_transform R s A h hs hA χs χA e he hprimitive
    (canonicalLifts R s) (canonicalLifts R A)]
  change (Real.sqrt (exteriorNorm R s) : ℂ)⁻¹ *
    ((exteriorNorm R s : ℂ) * finiteCoefficient R s A h χs χA e) = _
  rw [← hsq]
  field_simp
  <;> ring

private theorem char_norm_le_one {T : Type*} [CommRing T] [Fintype T]
    (χ : MulChar T ℂ) (x : T) : ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using h.le
  · rw [χ.map_nonunit hx, norm_zero]
    exact zero_le_one

theorem finiteCoefficient_norm_le (R : Subring K) (s A h : R)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : ∀ x : K, ‖e x‖ = 1) :
    ‖finiteCoefficient R s A h χs χA e‖ ≤
      (exteriorNorm R s : ℝ) * (exteriorNorm R A : ℝ) := by
  unfold finiteCoefficient finiteCoefficientWithLifts
  calc
    _ ≤ ∑ d : Residue R s, (exteriorNorm R A : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · rw [norm_mul]
        calc
          _ ≤ 1 * (exteriorNorm R A : ℝ) := by
            apply mul_le_mul (char_norm_le_one χs d) _ (norm_nonneg _) zero_le_one
            calc
              _ ≤ ∑ v : Residue R A, (1 : ℝ) := by
                apply (norm_sum_le _ _).trans
                apply Finset.sum_le_sum
                intro v _
                rw [norm_mul, he, mul_one]
                exact char_norm_le_one χA v
              _ = (exteriorNorm R A : ℝ) := by simp [exteriorNorm, Nat.card_eq_fintype_card]
          _ = _ := one_mul _
      · simp
    _ = _ := by simp [exteriorNorm, Nat.card_eq_fintype_card]

private theorem finiteCoefficient_unit_invariant (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (c : Rˣ)
    (hcs : χs (residueMap R s (c : R)) = 1)
    (hcA : χA (residueMap R A ((c⁻¹ : Rˣ) : R)) = 1) :
    finiteCoefficient R s A ((c : R) * h) χs χA e =
      finiteCoefficient R s A h χs χA e := by
  let cs : (Residue R s)ˣ := Units.map (residueMap R s).toMonoidHom c
  let cA : (Residue R A)ˣ := Units.map (residueMap R A).toMonoidHom c⁻¹
  have hcs' : χs (cs : Residue R s) = 1 := hcs
  have hcA' : χA (cA : Residue R A) = 1 := hcA
  unfold finiteCoefficient finiteCoefficientWithLifts
  symm
  apply Fintype.sum_equiv cs.mulLeft
  intro d
  change (if residueMap R s h = residueMap R s A * d then _ else _) =
    (if residueMap R s ((c : R) * h) = residueMap R s A * ((cs : Residue R s) * d)
      then _ else _)
  have hcond : residueMap R s ((c : R) * h) =
      residueMap R s A * ((cs : Residue R s) * d) ↔
      residueMap R s h = residueMap R s A * d := by
    change (residueMap R s (c : R)) * residueMap R s h =
      residueMap R s A * ((cs : Residue R s) * d) ↔ _
    change (cs : Residue R s) * residueMap R s h =
      residueMap R s A * ((cs : Residue R s) * d) ↔ _
    rw [mul_left_comm]
    simpa only [Units.mulLeft_apply] using
      cs.mulLeft.injective.eq_iff (a := residueMap R s h) (b := residueMap R s A * d)
  by_cases hd : residueMap R s h = residueMap R s A * d
  · rw [if_pos hd, if_pos (hcond.mpr hd)]
    simp only [Units.mulLeft_apply]
    rw [map_mul, hcs', one_mul]
    congr 1
    apply Fintype.sum_equiv cA.mulLeft
    intro v
    change χA v * e _ = χA ((cA : Residue R A) * v) * e _
    rw [map_mul, hcA', one_mul]
    congr 1
    symm
    calc
      _ = e (((((c : R) * h : R) : K) - (A : K) *
          (((c : R) * (canonicalLifts R s).val d : R) : K)) *
          ((((c⁻¹ : Rˣ) : R) * (canonicalLifts R A).val v : R) : K) /
          ((s : K) * (A : K))) := by
        apply double_phase_eq R s A ((c : R) * h) _ _ _ _ hs hA e he
        · rw [(canonicalLifts R s).property, map_mul, (canonicalLifts R s).property]
          rfl
        · rw [(canonicalLifts R A).property, map_mul, (canonicalLifts R A).property]
          rfl
        · simpa only [map_mul, (canonicalLifts R s).property, mul_left_comm] using
            congrArg (fun x => residueMap R s (c : R) * x) hd
      _ = _ := by
        congr 1
        push_cast
        have hu : (c : R).val * (((c⁻¹ : Rˣ) : R) : K) = 1 := by
          exact_mod_cast c.mul_inv
        congr 1
        calc
          _ = ((c : R) : K) * (((c⁻¹ : Rˣ) : R) : K) *
              (((h : K) - (A : K) * ((canonicalLifts R s).val d : K)) *
                ((canonicalLifts R A).val v : K)) := by ring
          _ = _ := by rw [hu, one_mul]
  · rw [if_neg hd, if_neg (fun hn => hd (hcond.mp hn))]

private theorem sixth_unit_character {T : Type*} [CommRing T]
    (χ : MulChar T ℂ) (hχ : χ ^ 6 = 1) (u : Tˣ) : χ ((u ^ 6 : Tˣ) : T) = 1 := by
  rw [Units.val_pow_eq_pow_val, map_pow, ← χ.pow_apply_coe 6 u, hχ,
    MulChar.one_apply_coe]

theorem finiteCoefficient_sixth_unit_invariant (R : Subring K) (s A h : R)
    (hs : s ≠ 0) (hA : A ≠ 0)
    [Fintype (Residue R s)] [Fintype (Residue R A)]
    (χs : MulChar (Residue R s) ℂ) (χA : MulChar (Residue R A) ℂ)
    (hχs : χs ^ 6 = 1) (hχA : χA ^ 6 = 1)
    (e : AddChar K ℂ) (he : IsTrivialOn R e) (u : Rˣ) :
    finiteCoefficient R s A (((u ^ 6 : Rˣ) : R) * h) χs χA e =
      finiteCoefficient R s A h χs χA e := by
  apply finiteCoefficient_unit_invariant R s A h hs hA χs χA e he (u ^ 6)
  · have H := sixth_unit_character χs hχs (Units.map (residueMap R s).toMonoidHom u)
    rw [Units.val_pow_eq_pow_val, map_pow] at H ⊢
    rw [map_pow]
    exact H
  · have H := sixth_unit_character χA hχA (Units.map (residueMap R A).toMonoidHom u⁻¹)
    rw [← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    rw [Units.val_pow_eq_pow_val, map_pow] at H
    rw [map_pow]
    exact H

end

end DedekindZetaZeroFree.FiniteTransform
