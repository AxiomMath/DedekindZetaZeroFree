module

public import DedekindZetaZeroFree.Adeles.Characters.RationalPadicCharacter

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

instance instFactPrimeRationalPadicProductNatPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem rationalPadicCharacter_rational_ne_one_iff (p : Nat.Primes) (q : ℚ) :
    rationalPadicCharacter p (q : ℚ_[p]) ≠ 1 ↔ p.1 ∣ q.den := by
  rw [ne_eq, rationalPadicCharacter_eq_one_iff]
  have h : (q : ℚ_[p]) ∈ Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) ↔
      ¬p.1 ∣ q.den := by
    constructor
    · rintro ⟨z, hz⟩
      have hn : ‖(q : ℚ_[p])‖ ≤ 1 := hz ▸ z.2
      have hu := PadicInt.isUnit_den q hn
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
        p.2.coprime_iff_not_dvd] at hu
      exact hu
    · intro h
      exact ⟨⟨(q : ℚ_[p]), Padic.norm_rat_le_one h⟩, rfl⟩
  simpa only [h, not_not]

theorem rationalPadicCharacter_finprod_eq_denominator_prod (q : ℚ) :
    (∏ᶠ p : Nat.Primes, rationalPadicCharacter p (q : ℚ_[p])) =
      (q.den.primeFactors.subtype Nat.Prime : Finset Nat.Primes).prod
        (fun p : Nat.Primes => rationalPadicCharacter p (q : ℚ_[p])) := by
  classical
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  exact Finset.mem_subtype.mpr
    (Nat.mem_primeFactors.mpr ⟨p.2,
      (rationalPadicCharacter_rational_ne_one_iff p q).mp hp, q.den_ne_zero⟩)

private theorem rationalPInverted_integral_at_other (p l : Nat.Primes)
    (h : l ≠ p) (q : ℚ) (hq : q ∈ rationalPInverted p) :
    (q : ℚ_[l]) ∈ PadicInt.subring l := by
  have hc : rationalPInverted p ≤
      (PadicInt.subring l).comap (Rat.castHom ℚ_[l]) := by
    apply Subring.closure_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change ‖(((p.1 : ℚ)⁻¹ : ℚ) : ℚ_[l])‖ ≤ 1
    have hnd : ¬ l.1 ∣ p.1 := by
      intro hd
      apply h
      apply Subtype.ext
      exact (Nat.prime_dvd_prime_iff_eq l.2 p.2).mp hd
    have hn : ‖(p.1 : ℚ_[l])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff, l.2.coprime_iff_not_dvd]
      exact hnd
    simpa [norm_inv, hn]
  exact hc hq

private theorem rational_character_prod_exp (q : ℚ) (s : Finset Nat.Primes) :
    s.prod (fun p => rationalPadicCharacter p (q : ℚ_[p])) =
      Circle.exp (-(2 * Real.pi * ((∑ p ∈ s, padicFractionalPart p (q : ℚ_[p]) : ℚ) : ℝ))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.sum_insert hp, ih]
    change Circle.exp (-(2 * Real.pi * (padicFractionalPart p (q : ℚ_[p]) : ℝ))) *
      Circle.exp (-(2 * Real.pi * ((∑ p ∈ s, padicFractionalPart p (q : ℚ_[p]) : ℚ) : ℝ))) = _
    rw [← Circle.exp_add]
    congr 1
    push_cast
    ring

private theorem rational_fractional_parts_difference_integral (q : ℚ) :
    (q - (q.den.primeFactors.subtype Nat.Prime : Finset Nat.Primes).sum
      (fun p : Nat.Primes =>
      padicFractionalPart p (q : ℚ_[p]))).den = 1 := by
  classical
  let s : Finset Nat.Primes := q.den.primeFactors.subtype Nat.Prime
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro l hl
  let p : Nat.Primes := ⟨l, hl⟩
  letI : Fact l.Prime := ⟨hl⟩
  have hi : ((q - ∑ a ∈ s, padicFractionalPart a (q : ℚ_[a]) : ℚ) : ℚ_[p]) ∈
      PadicInt.subring p := by
    by_cases hp : p ∈ s
    · have hs : ((∑ a ∈ s.erase p, padicFractionalPart a (q : ℚ_[a]) : ℚ) : ℚ_[p]) ∈
          PadicInt.subring p := by
        push_cast
        apply (PadicInt.subring p).sum_mem
        intro a ha
        exact rationalPInverted_integral_at_other a p
          (Ne.symm (Finset.mem_erase.mp ha).1) _
          (padicFractionalPart_spec a _).1
      obtain ⟨z, hz⟩ := (padicFractionalPart_spec p (q : ℚ_[p])).2.2.2
      have hz' : (q : ℚ_[p]) - (padicFractionalPart p (q : ℚ_[p]) : ℚ_[p]) ∈
          PadicInt.subring p := hz ▸ z.2
      rw [← Finset.add_sum_erase s _ hp]
      push_cast
      convert (PadicInt.subring p).sub_mem hz' hs using 1
      push_cast
      ring
    · have hq : (q : ℚ_[p]) ∈ PadicInt.subring p := by
        apply Padic.norm_rat_le_one
        intro hd
        apply hp
        exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨hl, hd, q.den_ne_zero⟩)
      have hs : ((∑ a ∈ s, padicFractionalPart a (q : ℚ_[a]) : ℚ) : ℚ_[p]) ∈
          PadicInt.subring p := by
        push_cast
        apply (PadicInt.subring p).sum_mem
        intro a ha
        apply rationalPInverted_integral_at_other a p
        · intro h
          exact hp (h.symm ▸ ha)
        · exact (padicFractionalPart_spec a _).1
      simpa only [Rat.cast_sub] using (PadicInt.subring p).sub_mem hq hs
  have hu := PadicInt.isUnit_den
    (q - ∑ a ∈ s, padicFractionalPart a (q : ℚ_[a])) hi
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    hl.coprime_iff_not_dvd] at hu
  exact hu

theorem rational_diagonal_additive_product (q : ℚ) :
    Circle.exp (2 * Real.pi * (q : ℝ)) *
      (∏ᶠ p : Nat.Primes, rationalPadicCharacter p (q : ℚ_[p])) = 1 := by
  classical
  rw [rationalPadicCharacter_finprod_eq_denominator_prod]
  change Circle.exp (2 * Real.pi * (q : ℝ)) *
    (q.den.primeFactors.subtype Nat.Prime : Finset Nat.Primes).prod
      (fun p : Nat.Primes => rationalPadicCharacter p (q : ℚ_[p])) = 1
  erw [rational_character_prod_exp q (q.den.primeFactors.subtype Nat.Prime)]
  rw [← Circle.exp_add]
  let r : ℚ := q - (q.den.primeFactors.subtype Nat.Prime : Finset Nat.Primes).sum
    (fun p : Nat.Primes => padicFractionalPart p (q : ℚ_[p]))
  have hr : (r.num : ℚ) = r :=
    Rat.coe_int_num_of_den_eq_one (rational_fractional_parts_difference_integral q)
  have he : 2 * Real.pi * (q : ℝ) +
      -(2 * Real.pi * (((q.den.primeFactors.subtype Nat.Prime : Finset Nat.Primes).sum
        (fun p : Nat.Primes => padicFractionalPart p (q : ℚ_[p])) : ℚ) : ℝ)) =
      (r.num : ℝ) * (2 * Real.pi) := by
    have hrc : (r.num : ℝ) = (r : ℝ) := by exact_mod_cast hr
    rw [hrc]
    dsimp [r]
    push_cast
    ring
  erw [he]
  exact Circle.exp_int_mul_two_pi r.num

end DedekindZetaZeroFree

end
