module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.CodifferentTraceDuality
public import DedekindZetaZeroFree.ZeroDetection.Conductors.BalancedIdealSections

@[expose] public section

namespace DedekindZetaZeroFree.CodifferentResidueSieve
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]
private theorem reduction (A : SArithmeticData F) [IsPrincipalIdealRing A.R]
    (p : ProbeSeparation.Presentation F A.Sf) (x : F) :
    ∃ α : ProbeSeparation.ReducedPair F A.Sf,
      (∃ r : A.R, x = ProbeSeparation.value F p α + (r : F)) ∧
      α.1.val = Ideal.span {(IsFractionRing.den A.R x : A.R)} := by
  let b : A.R := IsFractionRing.den A.R x
  let n : A.R := IsFractionRing.num A.R x
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den A.R x).property
  have hI : Ideal.span {b} ≠ ⊥ := by simpa using hb
  let t : A.R := p.generator (Ideal.span {b}) hI
  have hass : Associated t b := Ideal.span_singleton_eq_span_singleton.mp (p.generator_span _ _)
  obtain ⟨u, hu⟩ := hass
  let e : A.R := n * (u⁻¹ : A.Rˣ)
  have ht : t = b * (u⁻¹ : A.Rˣ) := by
    rw [← hu]
    simp
  have hcop : IsCoprime e t := by
    have hc := (IsFractionRing.num_den_reduced A.R x).isCoprime
    change IsCoprime n b at hc
    rw [ht]
    simpa only [e, isCoprime_mul_unit_right (Units.isUnit (u⁻¹))] using hc
  have htq : Ideal.Quotient.mk (Ideal.span {b}) t = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← p.generator_span _ hI]
    exact Ideal.subset_span (Set.mem_singleton _)
  have heq : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) e) := by
    have hc := hcop.map (Ideal.Quotient.mk (Ideal.span {b}))
    rw [htq, isCoprime_zero_right] at hc
    exact hc
  let d := heq.unit
  let α : ProbeSeparation.ReducedPair F A.Sf := ⟨⟨Ideal.span {b}, hI⟩, d⟩
  have hmem : e - p.lift (Ideal.span {b}) d ∈ Ideal.span {t} := by
    rw [p.generator_span]
    apply Ideal.Quotient.eq.mp
    rw [p.lift_spec]
    exact heq.unit_spec.symm
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  have hx : x = (e : F) / (t : F) := by
    have hn := IsFractionRing.mk'_num_den' A.R x
    change (n : F) / (b : F) = x at hn
    rw [← hn, ht]
    simp only [e, Subalgebra.coe_mul]
    have huF : ((u⁻¹ : A.Rˣ) : F) ≠ 0 := by exact_mod_cast Units.ne_zero (u⁻¹)
    field_simp
  refine ⟨α, ⟨r, ?_⟩, rfl⟩
  change x = (p.lift (Ideal.span {b}) d : F) / (t : F) + (r : F)
  rw [hx]
  have htF : (t : F) ≠ 0 := by exact_mod_cast p.generator_nonzero _ hI
  have hrF := congrArg (fun z : A.R => (z : F)) hr
  simp only [Subalgebra.coe_mul, Subalgebra.coe_sub] at hrF
  field_simp
  linear_combination hrF

private theorem den_dvd (A : SArithmeticData F) [IsPrincipalIdealRing A.R]
    (n b : A.R) (hb : b ≠ 0) :
    (IsFractionRing.den A.R ((n : F) / (b : F)) : A.R) ∣ b := by
  let x := (n : F) / (b : F)
  have h := IsFractionRing.mk'_num_den' A.R x
  change (IsFractionRing.num A.R x : F) / (IsFractionRing.den A.R x : F) =
    (n : F) / (b : F) at h
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb
  have hdF : (IsFractionRing.den A.R x : F) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (IsFractionRing.den A.R x).property
  have he : IsFractionRing.num A.R x * b = n * (IsFractionRing.den A.R x : A.R) := by
    apply Subtype.val_injective
    change (IsFractionRing.num A.R x : F) * (b : F) =
      (n : F) * (IsFractionRing.den A.R x : F)
    field_simp at h
    linear_combination h
  apply (IsFractionRing.num_den_reduced A.R x).symm.dvd_of_dvd_mul_left
  rw [he]
  exact dvd_mul_left _ _

private theorem phase_shift (A : SArithmeticData F) (htrace : TraceDualData A)
    (x : F) (r : A.R) : phase A (x + (r : F)) = phase A x := by
  unfold phase
  rw [map_add, ProbeAdditive.phase_add]
  have hr := htrace.compatible r
  change ProbeAdditive.phase F A.Sf (finiteTrace A)
    (sLocalDiagonal F A.Sf (r : F)) = 1 at hr
  rw [hr, mul_one]

theorem scaled_reduced_pair_adapter
    {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (htrace : TraceDualData A)
    (K_bal : Set A.G) (B : Subgroup A.V)
    (s : A.BalancedIdealSection B K_bal)
    (V : ℝ) (hV : 1 ≤ V)
    (Q : Type) [Fintype Q] (q : Q → Ideal A.R)
    [∀ j, Fintype (A.R ⧸ q j)]
    (hinj : Function.Injective q) (hq : ∀ j, q j ≠ ⊥)
    (hnorm : ∀ j, (Nat.card (A.R ⧸ q j) : ℝ) ≤ V) :
    ∃ (p : ProbeSeparation.Presentation F A.Sf)
      (rho : (Σ j, (A.R ⧸ q j)ˣ) → ProbeSeparation.ReducedPair F A.Sf),
      Function.Injective rho ∧
      (∀ jd, ProbeSeparation.denominatorNorm F (rho jd) ≤ denominatorScale A * V) ∧
      ∃ psi : ∀ j, AddChar (A.R ⧸ q j) ℂ,
        (∀ j, (psi j).IsPrimitive) ∧
        ∀ j (d : (A.R ⧸ q j)ˣ) (m : A.R),
          psi j (Ideal.Quotient.mk (q j) m * (d : A.R ⧸ q j)) =
            ProbeAdditive.phase F A.Sf (finiteTrace A) (sLocalDiagonal F A.Sf
              (-((m : F) * ProbeSeparation.value F p (rho ⟨j, d⟩)))) := by
  let p : ProbeSeparation.Presentation F A.Sf := {
    generator I hI := s.generator (A.exteriorIdealEquiv.symm ⟨I, hI⟩)
    generator_nonzero I hI := (s.generates _).1
    generator_span I hI := by
      have h := (s.generates (A.exteriorIdealEquiv.symm ⟨I, hI⟩)).2
      have he := congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨I, hI⟩)
      rw [A.exteriorIdealEquiv_apply] at he
      exact h.trans he
    lift I d := Classical.choose (Ideal.Quotient.mk_surjective (I := I) (d : A.R ⧸ I))
    lift_spec I d := Classical.choose_spec (Ideal.Quotient.mk_surjective (I := I) (d : A.R ⧸ I)) }
  letI : IsPrincipalIdealRing A.R := ⟨fun I => by
    by_cases hI : I = ⊥
    · subst I; infer_instance
    · exact ⟨⟨p.generator I hI, (p.generator_span I hI).symm⟩⟩⟩
  let δ : A.R := p.generator (different A) htrace.different_nonzero
  have hδ : δ ≠ 0 := p.generator_nonzero _ _
  have hδspan : Ideal.span {δ} = different A := p.generator_span _ _
  let a : Q → A.R := fun j => p.generator (q j) (hq j)
  have ha : ∀ j, a j ≠ 0 := fun j => p.generator_nonzero _ _
  have haspan : ∀ j, Ideal.span {a j} = q j := fun j => p.generator_span _ _
  let x : (Σ j, (A.R ⧸ q j)ˣ) → F :=
    fun jd => (p.lift (q jd.1) jd.2 : F) / ((δ : F) * (a jd.1 : F))
  choose rho hrepr hden using fun jd => reduction A p (x jd)
  choose r hr using hrepr
  have hpairinj : Function.Injective
      (fun jd : (Σ j, (A.R ⧸ q j)ˣ) =>
        (⟨⟨q jd.1, hq jd.1⟩, jd.2⟩ : ProbeSeparation.ReducedPair F A.Sf)) := by
    apply Function.Injective.sigma_map
      (β₂ := fun I : {I : Ideal A.R // I ≠ ⊥} => (A.R ⧸ I.val)ˣ)
      (f₁ := fun j => (⟨q j, hq j⟩ : {I : Ideal A.R // I ≠ ⊥}))
      (f₂ := fun _ d => d)
    · intro j k hjk; exact hinj (congrArg Subtype.val hjk)
    · intro j d e h; exact h
  have hx : ∀ jd, (δ : F) * x jd =
      ProbeSeparation.value F p ⟨⟨q jd.1, hq jd.1⟩, jd.2⟩ := by
    intro jd
    dsimp [x, ProbeSeparation.value, a]
    have hdF : (δ : F) ≠ 0 := by exact_mod_cast hδ
    field_simp
  refine ⟨p, rho, ?_, ?_, ?_⟩
  · intro jd kd heq
    apply hpairinj
    apply probe_reduced_fraction_injective F A.Sf p
    apply (QuotientAddGroup.mk'_eq_mk' _).mpr
    refine ⟨(δ * (r kd - r jd) : A.R), (δ * (r kd - r jd)).property, ?_⟩
    have hj := hr jd
    have hk := hr kd
    rw [heq] at hj
    have hj' := congrArg (fun z : F => (δ : F) * z) hj
    have hk' := congrArg (fun z : F => (δ : F) * z) hk
    rw [hx jd] at hj'
    rw [hx kd] at hk'
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub]
    linear_combination hj' - hk'
  · intro jd
    have hdvd := den_dvd A (p.lift (q jd.1) jd.2) (δ * a jd.1) (mul_ne_zero hδ (ha _))
    change (IsFractionRing.den A.R (x jd) : A.R) ∣ δ * a jd.1 at hdvd
    have hle : Ideal.span {δ * a jd.1} ≤ (rho jd).1.val := by
      rw [hden jd]
      exact Ideal.span_singleton_le_span_singleton.mpr hdvd
    have hfin := (sProductModulus_eq_principalIdeal_index F A.Sf
      (δ * a jd.1) (mul_ne_zero hδ (ha _))).1
    letI := hfin
    have hcard := Nat.card_le_card_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)
    have hmul : Nat.card (A.R ⧸ Ideal.span {δ * a jd.1}) =
        Nat.card (A.R ⧸ different A) * Nat.card (A.R ⧸ q jd.1) := by
      rw [← Submodule.cardQuot_apply, ← Ideal.span_singleton_mul_span_singleton,
        hδspan, haspan, cardQuot_mul]
      rfl
    have hc : ProbeSeparation.denominatorNorm F (rho jd) ≤
        (Nat.card (A.R ⧸ different A) : ℝ) * (Nat.card (A.R ⧸ q jd.1) : ℝ) := by
      unfold ProbeSeparation.denominatorNorm
      exact_mod_cast hcard.trans_eq hmul
    exact hc.trans (mul_le_mul (le_max_right _ _) (hnorm jd.1)
      (Nat.cast_nonneg _) (le_trans (by norm_num) (le_max_left _ _)))
  · have hres := fun j => htrace.residue δ hδ hδspan (q j) (a j) (ha j) (haspan j)
    choose psi hprim hpsi using hres
    refine ⟨psi, hprim, ?_⟩
    intro j d m
    rw [← p.lift_spec (q j) d, ← map_mul, hpsi]
    change phase A (-((m : F) * (p.lift (q j) d : F) /
      ((δ : F) * (a j : F)))) = phase A _
    have hj := hr ⟨j, d⟩
    have harg : -((m : F) * (p.lift (q j) d : F) /
        ((δ : F) * (a j : F))) =
        -((m : F) * ProbeSeparation.value F p (rho ⟨j, d⟩)) +
          ((-(m * r ⟨j, d⟩) : A.R) : F) := by
      change (p.lift (q j) d : F) / ((δ : F) * (a j : F)) = _ at hj
      simp only [Subalgebra.coe_neg, Subalgebra.coe_mul]
      rw [mul_div_assoc, hj]
      ring
    rw [harg, phase_shift A htrace]

end
end DedekindZetaZeroFree.CodifferentResidueSieve
