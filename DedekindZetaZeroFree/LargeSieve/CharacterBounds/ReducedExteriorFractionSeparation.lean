module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain

namespace ProbeSeparation

variable (F : Type) [Field F] [NumberField F]

abbrev Integers (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (S : Set (HeightOneSpectrum (𝓞 F))).integer F

def productNorm (S : Finset (HeightOneSpectrum (𝓞 F))) (x : F) : ℝ :=
  (∏ v : NumberField.InfinitePlace F, v x ^ v.mult) *
    ∏ v ∈ S, NumberField.FinitePlace.mk v x

structure Presentation (S : Finset (HeightOneSpectrum (𝓞 F))) where
  generator : (I : Ideal (Integers F S)) → I ≠ ⊥ → Integers F S
  generator_nonzero : ∀ I hI, generator I hI ≠ 0
  generator_span : ∀ I hI, Ideal.span {generator I hI} = I
  lift : (I : Ideal (Integers F S)) → ((Integers F S) ⧸ I)ˣ → Integers F S
  lift_spec : ∀ I d, Ideal.Quotient.mk I (lift I d) = (d : (Integers F S) ⧸ I)

abbrev ReducedPair (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (I : {I : Ideal (Integers F S) // I ≠ ⊥}) × ((Integers F S) ⧸ I.val)ˣ

def value {S : Finset (HeightOneSpectrum (𝓞 F))}
    (p : Presentation F S) (α : ReducedPair F S) : F :=
  (p.lift α.1.val α.2 : F) / (p.generator α.1.val α.1.property : F)

def fractionClass {S : Finset (HeightOneSpectrum (𝓞 F))}
    (p : Presentation F S) (α : ReducedPair F S) : F ⧸ (Integers F S).toSubring.toAddSubgroup :=
  QuotientAddGroup.mk' (Integers F S).toSubring.toAddSubgroup (value F p α)

def denominatorNorm {S : Finset (HeightOneSpectrum (𝓞 F))}
    (α : ReducedPair F S) : ℝ :=
  Nat.card ((Integers F S) ⧸ α.1.val)

end ProbeSeparation

open ProbeSeparation in
private theorem probeDenominatorLe (F : Type) [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (p : Presentation F S)
    (a b : ReducedPair F S) (r : Integers F S)
    (h : value F p a + (r : F) = value F p b) : b.1.val ≤ a.1.val := by
  let s := p.generator a.1.val a.1.property
  let t := p.generator b.1.val b.1.property
  let d := p.lift a.1.val a.2
  let e := p.lift b.1.val b.2
  have hs : (s : F) ≠ 0 := by exact_mod_cast p.generator_nonzero a.1.val a.1.property
  have ht : (t : F) ≠ 0 := by exact_mod_cast p.generator_nonzero b.1.val b.1.property
  change (d : F) / (s : F) + (r : F) = (e : F) / (t : F) at h
  have hc : d * t + r * s * t = e * s := by
    apply Subtype.val_injective
    change (d : F) * (t : F) + (r : F) * (s : F) * (t : F) = (e : F) * (s : F)
    field_simp at h
    linear_combination h
  have hqs : Ideal.Quotient.mk a.1.val s = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← p.generator_span a.1.val a.1.property]
    exact Ideal.subset_span (Set.mem_singleton s)
  have hqt : Ideal.Quotient.mk a.1.val t = 0 := by
    have hcq := congrArg (Ideal.Quotient.mk a.1.val) hc
    simp only [map_add, map_mul, hqs, mul_zero, zero_mul, add_zero, p.lift_spec] at hcq
    rw [show Ideal.Quotient.mk a.1.val d = (a.2 : (Integers F S) ⧸ a.1.val) from
      p.lift_spec _ _] at hcq
    have hcancel := congrArg (fun x => (↑a.2⁻¹ : (Integers F S) ⧸ a.1.val) * x) hcq
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using hcancel
  rw [← p.generator_span b.1.val b.1.property]
  exact Ideal.span_le.mpr (by simpa using Ideal.Quotient.eq_zero_iff_mem.mp hqt)

open ProbeSeparation in

theorem probe_reduced_fraction_injective (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : ProbeSeparation.Presentation F S) :
    Function.Injective (ProbeSeparation.fractionClass F p) := by
  letI := Classical.decEq F
  intro a b hab
  obtain ⟨r, hr, h⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp hab
  let r' : Integers F S := ⟨r, hr⟩
  have h' : value F p a + (r' : F) = value F p b := h
  have hI : a.1 = b.1 := by
    apply Subtype.ext
    apply le_antisymm
    · apply probeDenominatorLe F p b a (-r')
      change value F p b + -(r' : F) = value F p a
      linear_combination -h'
    · exact probeDenominatorLe F p a b r' h'
  cases a with
  | mk I d =>
    cases b with
    | mk J e =>
      dsimp only at hI
      subst J
      congr 1
      apply Units.ext
      rw [← p.lift_spec, ← p.lift_spec]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      have hmem : p.lift I.val d - p.lift I.val e ∈
          Ideal.span {p.generator I.val I.property} := by
        rw [Ideal.mem_span_singleton]
        refine ⟨-r', ?_⟩
        apply Subtype.val_injective
        change (p.lift I.val d : F) - (p.lift I.val e : F) =
          (p.generator I.val I.property : F) * -(r' : F)
        change (p.lift I.val d : F) / (p.generator I.val I.property : F) + (r' : F) =
          (p.lift I.val e : F) / (p.generator I.val I.property : F) at h'
        have hs : (p.generator I.val I.property : F) ≠ 0 := by
          exact_mod_cast p.generator_nonzero I.val I.property
        field_simp at h'
        linear_combination h'
      exact SetLike.le_def.mp (le_of_eq (p.generator_span I.val I.property)) hmem

theorem probe_sinteger_product_norm_lower_bound (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : ProbeSeparation.Integers F S) (hr : r ≠ 0) :
    1 ≤ ProbeSeparation.productNorm F S (r : F) := by
  classical
  have hrF : (r : F) ≠ 0 := by exact_mod_cast hr
  let f : NumberField.FinitePlace F → ℝ :=
    fun w => if w.maximalIdeal ∈ S then w (r : F) else 1
  have hf : Function.HasFiniteMulSupport f := by
    apply (S.finite_toSet.preimage
      NumberField.FinitePlace.maximalIdeal_injective.injOn).subset
    intro w hw
    simp only [Function.mem_mulSupport, f] at hw
    by_contra h
    exact hw (if_neg h)
  have hle : (∏ᶠ w : NumberField.FinitePlace F, w (r : F)) ≤ ∏ᶠ w, f w := by
    apply finprod_le_finprod₀ (NumberField.FinitePlace.hasFiniteMulSupport hrF)
      (fun w => apply_nonneg w _) hf
    intro w
    dsimp [f]
    split_ifs with hw
    · exact le_rfl
    · rw [← NumberField.FinitePlace.mk_maximalIdeal w,
        NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_embedding']
      change ((WithZeroMulInt.toNNReal _ _) : ℝ) ≤ 1
      norm_cast
      apply (WithZeroMulInt.toNNReal_le_one_iff
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w.maximalIdeal)).2
      exact Set.integer_valuation_le_one _ F r hw
  have heq : (∏ᶠ w, f w) = ∏ v ∈ S, NumberField.FinitePlace.mk v (r : F) := by
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
    simp only [f, NumberField.FinitePlace.equivHeightOneSpectrum,
      Equiv.coe_fn_symm_mk, NumberField.FinitePlace.maximalIdeal_mk]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · exact Finset.prod_congr rfl fun v hv => if_pos hv
    · intro v hv
      simp only [Function.mem_mulSupport] at hv
      by_contra h
      exact hv (if_neg h)
  rw [heq] at hle
  have hnonneg : 0 ≤ ∏ w : NumberField.InfinitePlace F, w (r : F) ^ w.mult := by
    positivity
  rw [← NumberField.prod_abs_eq_one hrF]
  exact mul_le_mul_of_nonneg_left hle hnonneg

open ProbeSeparation in
private theorem probeProductNormMul (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x y : F) :
    productNorm F S (x*y) = productNorm F S x * productNorm F S y := by
  simp only [productNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  ring

open ProbeSeparation in

theorem probe_reduced_fraction_separation (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : ProbeSeparation.Presentation F S)
    (V : ℝ) (hV : 1 ≤ V) (P : Finset (ProbeSeparation.ReducedPair F S))
    (hP : ∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V)
    (α β : ProbeSeparation.ReducedPair F S) (hα : α ∈ P) (hβ : β ∈ P)
    (hne : α ≠ β) (r : ProbeSeparation.Integers F S) :
    V ^ (-2 : ℝ) ≤ ProbeSeparation.productNorm F S
      (ProbeSeparation.value F p α - ProbeSeparation.value F p β + (r : F)) := by
  let s := p.generator α.1.val α.1.property
  let t := p.generator β.1.val β.1.property
  let x := value F p α - value F p β + (r : F)
  let n : Integers F S :=
    p.lift α.1.val α.2 * t - p.lift β.1.val β.2 * s + r * s * t
  have hs : s ≠ 0 := p.generator_nonzero _ _
  have ht : t ≠ 0 := p.generator_nonzero _ _
  have hsF : (s : F) ≠ 0 := by exact_mod_cast hs
  have htF : (t : F) ≠ 0 := by exact_mod_cast ht
  have hx : x ≠ 0 := by
    intro hx
    apply hne
    apply probe_reduced_fraction_injective F S p
    apply (QuotientAddGroup.mk'_eq_mk' _).mpr
    refine ⟨r, r.property, ?_⟩
    dsimp [x] at hx
    linear_combination hx
  have hnx : (n : F) = x * (s : F) * (t : F) := by
    change (p.lift α.1.val α.2 : F) * (t : F) -
      (p.lift β.1.val β.2 : F) * (s : F) + (r : F) * (s : F) * (t : F) =
      ((p.lift α.1.val α.2 : F) / (s : F) -
        (p.lift β.1.val β.2 : F) / (t : F) + (r : F)) * (s : F) * (t : F)
    field_simp [hsF, htF]
    <;> ring
  have hn : n ≠ 0 := by
    intro hn
    have hnF : (n : F) = 0 := by exact_mod_cast hn
    rw [hnx] at hnF
    exact mul_ne_zero (mul_ne_zero hx hsF) htF hnF
  have hnlow := probe_sinteger_product_norm_lower_bound F S n hn
  have hsNorm : productNorm F S (s : F) = denominatorNorm F α := by
    have h := (sProductModulus_eq_principalIdeal_index F S s hs).2
    change productNorm F S (s : F) = _ at h
    simpa only [s, p.generator_span, denominatorNorm] using h
  have htNorm : productNorm F S (t : F) = denominatorNorm F β := by
    have h := (sProductModulus_eq_principalIdeal_index F S t ht).2
    change productNorm F S (t : F) = _ at h
    simpa only [t, p.generator_span, denominatorNorm] using h
  rw [hnx, probeProductNormMul, probeProductNormMul, hsNorm, htNorm] at hnlow
  have hapos : 0 ≤ denominatorNorm F α := Nat.cast_nonneg _
  have hbpos : 0 ≤ denominatorNorm F β := Nat.cast_nonneg _
  have hxpos : 0 ≤ productNorm F S x := by dsimp [productNorm]; positivity
  have hprod : denominatorNorm F α * denominatorNorm F β ≤ V * V :=
    mul_le_mul (hP α hα) (hP β hβ) hbpos (by linarith)
  have hl : 1 ≤ productNorm F S x * (V*V) := by
    calc
      1 ≤ productNorm F S x * (denominatorNorm F α * denominatorNorm F β) := by
        nlinarith [hnlow]
      _ ≤ productNorm F S x * (V*V) := mul_le_mul_of_nonneg_left hprod hxpos
  have hVpos : 0 < V := by linarith
  rw [Real.rpow_neg (by linarith : 0 ≤ V), Real.rpow_two]
  apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < V^2)).mpr
  nlinarith [hl]

end
end DedekindZetaZeroFree
