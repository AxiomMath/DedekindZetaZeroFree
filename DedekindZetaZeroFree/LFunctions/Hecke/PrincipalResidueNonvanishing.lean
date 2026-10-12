module

public import DedekindZetaZeroFree.LFunctions.Hecke.RayContinuationData
public import DedekindZetaZeroFree.LFunctions.Hecke.ExteriorIdealEulerProducts

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

open scoped NumberField Topology
open Filter ExteriorIdealEuler

private theorem full_sum_eq_zeta
    (F : Type) [Field F] [NumberField F] (s : ℂ) (hs : 1 < s.re) :
    (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)), summand (fun _ => 1) s I) =
      NumberField.dedekindZeta F s := by
  classical
  have hsum := (summable_norm_summand (fun _ : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => 1)
    (constant_one_isCoefficient _) s hs).of_norm
  have hg := hsum.hasSum.tsum_fiberwise (fun I => Ideal.absNorm I.val)
  have hf (n : ℕ) :
      (∑' I : {I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) // Ideal.absNorm I.val = n},
        summand (fun _ => 1) s I.val) =
      LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      have hnone : IsEmpty {I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) // Ideal.absNorm I.val = 0} :=
        ⟨fun I => I.val.property.1 (Ideal.absNorm_eq_zero_iff.mp I.property)⟩
      letI := hnone
      simp [LSeries.term]
    · let e : {I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) // Ideal.absNorm I.val = n} ≃
          {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
        { toFun := fun I => ⟨I.val.val, I.property⟩
          invFun := fun I => ⟨⟨I.val, by
            constructor
            · intro h
              apply hn
              simpa [h] using I.property.symm
            · simp⟩, I.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have ht (I : {I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) // Ideal.absNorm I.val = n}) :
          summand (fun _ => 1) s I.val = (n : ℂ) ^ (-s) := by
        simp [summand, I.property]
      simp_rw [ht]
      rw [tsum_const, nsmul_eq_mul, Nat.card_congr e, LSeries.term_of_ne_zero hn]
      simp [Complex.cpow_neg, div_eq_mul_inv]
  change HasSum (fun n => ∑' I : {I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) //
    Ideal.absNorm I.val = n}, summand (fun _ => 1) s I.val) _ at hg
  simpa only [hf, NumberField.dedekindZeta, LSeries] using hg.tsum_eq.symm

theorem principal_regularization_ne_zero
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (η : RayClassCharacter F m) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F m η) : P.R 1 ≠ 0 := by
  classical
  let Q := PrimeIndex (⊤ : Ideal (𝓞 F))
  let bad : Set Q := {p | p.val.val ⊔ m ≠ ⊤}
  have hbad_le (p : Q) (hp : p ∈ bad) : m ≤ p.val.val := by
    have hmax := (Ideal.isPrime_of_prime p.property).isMaximal p.val.property.1
    have heq := hmax.eq_of_le hp le_sup_left
    rw [heq]
    exact le_sup_right
  have hbad_fin : bad.Finite := by
    have hinj : Function.Injective (fun p : Q => p.val.val) := by
      intro p q h
      exact Subtype.ext (Subtype.ext h)
    apply ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm m)).preimage
      hinj.injOn).subset
    intro p hp
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm))
      (Ideal.absNorm_dvd_absNorm_of_le (hbad_le p hp))
  let B : Finset Q := hbad_fin.toFinset
  let e : ℂ → ℂ := fun s => ∏ p ∈ B, (1 - (Ideal.absNorm p.val.val : ℂ) ^ (-s))
  have hc : IsCoefficient (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => η I.val) := by
    have hc' := zeroMaskedRay_isCoefficient (cS := (⊤ : Ideal (𝓞 F))) m hm η ⊤
    have hf : zeroMaskedRayCoefficient (cS := (⊤ : Ideal (𝓞 F))) η ⊤ =
        (fun I => η I.val) := by
      funext I
      simp [zeroMaskedRayCoefficient]
    rw [hf] at hc'
    exact hc'
  have hseries (s : ℂ) (hs : 1 < s.re) :
      (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)), summand (fun I => η I.val) s I) = P.L s := by
    rw [show (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)), summand (fun I => η I.val) s I) =
      ∑' I : Ideal (𝓞 F), η I * (Ideal.absNorm I : ℂ) ^ (-s) from ?_]
    · exact (P.series s hs).tsum_eq
    · unfold summand ExteriorIdeal
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤})
        (f := fun I => η I * (Ideal.absNorm I : ℂ) ^ (-s))
      intro I hI
      constructor
      · intro h
        apply hI
        simp [h, (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)]
      · simp
  have heq (s : ℂ) (hs : 1 < s.re) : P.L s = NumberField.dedekindZeta F s * e s := by
    have hmprod := (exterior_ideal_euler (fun I : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => η I.val)
      hc s hs).2.2.2
    rw [hseries s hs] at hmprod
    have hzprod := (exterior_ideal_euler (fun _ : ExteriorIdeal (⊤ : Ideal (𝓞 F)) => 1)
      (constant_one_isCoefficient _) s hs).2.2.2
    rw [full_sum_eq_zeta F s hs] at hzprod
    let f : Q → ℂ := fun p => if p ∈ B then 1 - (Ideal.absNorm p.val.val : ℂ) ^ (-s) else 1
    have hf : HasProd f (e s) := by
      simpa [f, e] using (hasProd_prod_of_ne_finset_one (s := B)
        (f := f) (fun p hp => by simp [f, hp]))
    have hmul : (fun p : Q => (1 - primeTerm (fun I => η I.val) s p) * f p) =
        (fun p : Q => 1 - primeTerm (fun _ => 1) s p) := by
      funext p
      by_cases hp : p ∈ B
      · have hp' : p.val.val ⊔ m ≠ ⊤ := hbad_fin.mem_toFinset.mp hp
        have hzero := (η.eq_zero_iff' p.val.val).mpr (Or.inr hp')
        simp [primeTerm, summand, f, hp, hzero]
      · have hp' : p.val.val ⊔ m = ⊤ := by
          by_contra h
          exact hp (hbad_fin.mem_toFinset.mpr h)
        simp [primeTerm, summand, f, hp, hη _ p.val.property.1 hp']
    have hi := hmprod.mul hf
    rw [hmul] at hi
    have h := hi.unique hzprod
    have hn : P.L s ≠ 0 := by
      rw [← hseries s hs]
      exact (exterior_ideal_euler _ hc s hs).2.2.1
    have hzn : NumberField.dedekindZeta F s ≠ 0 := by
      rw [← full_sum_eq_zeta F s hs]
      exact (exterior_ideal_euler _ (constant_one_isCoefficient _) s hs).2.2.1
    field_simp at h
    linear_combination -h
  have hecont : Continuous e := by
    apply continuous_finset_prod
    intro p hp
    apply continuous_const.sub
    apply Continuous.const_cpow continuous_id.neg
    left
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.val.property.1)
  have hlim : Tendsto (fun x : ℝ => P.R (x : ℂ)) (𝓝[>] 1) (𝓝 (P.R 1)) := by
    have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h := (P.R_holo.continuousOn.continuousAt (ho.mem_nhds (by norm_num :
      (1 : ℂ) ∈ {s : ℂ | 0 < s.re}))).tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto
    simpa only [Function.comp_def, Complex.ofReal_one] using h.mono_left nhdsWithin_le_nhds
  have hr := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).mul
    ((hecont.comp Complex.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hv : P.R 1 = (NumberField.dedekindZeta_residue F : ℂ) * e 1 := by
    apply tendsto_nhds_unique hlim
    simp only [Function.comp_def, Complex.ofReal_one] at hr
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    rw [P.regularized _ (zero_lt_one.trans hx') (by
      intro h; rw [h] at hx'; norm_num at hx'), heq _ hx']
    ring
  rw [hv]
  apply mul_ne_zero
  · exact_mod_cast NumberField.dedekindZeta_residue_ne_zero F
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hnorm : (1 : ℝ) < Ideal.absNorm p.val.val := by
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
        (idealNorm_prime_ge_two p.val.val p.property)
    have hn : (Ideal.absNorm p.val.val : ℂ) ≠ 1 := by
      exact_mod_cast hnorm.ne'
    simp only [Complex.cpow_neg, Complex.cpow_one, sub_ne_zero]
    intro h
    apply hn
    have hh := congrArg Inv.inv h
    simpa using hh.symm

end DedekindZetaZeroFree.PrincipalMellinComparison
