module

public import DedekindZetaZeroFree.CharacterSums.Gauss.LocalQuotientSums
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.LocalCharacterCompatibility

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.CompatiblePrimeRawLocal
open LocalFiniteSums LocalFiniteSumCompatibility
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem localReduction_exists_unique (p : ExteriorPrime A) :
    ∃! ρ : LocalIntegers p →+* (A.R ⧸ A.extendIdeal (primeIdeal p)),
      ∀ x : A.R,
        ρ ⟨algebraMap F (LocalField p) (x : F), sInteger_local_integral p x⟩ =
          Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x := by
 let e := A.exteriorLocalResidueEquiv (primeIdeal p) p.val rfl
 let i := A.exteriorIntegerMap (primeIdeal p) p.val rfl
 let res := IsLocalRing.residue (LocalIntegers p)
 let ρ := e.symm.toRingHom.comp res
 have hi (x : A.R) : i x = ⟨algebraMap F (LocalField p) (x : F), sInteger_local_integral p x⟩ := by rfl
 have hρ (x : A.R) : ρ (i x) = Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x := by
   apply e.injective
   change e (e.symm (res (i x))) = _
   rw [e.apply_symm_apply]
   exact (A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl x).symm
 refine ⟨ρ, fun x => by rw [← hi]; exact hρ x, ?_⟩
 intro τ hτ
 have hfield : IsField (A.R ⧸ A.extendIdeal (primeIdeal p)) := e.toMulEquiv.isField (Field.toIsField _)
 letI := hfield.toField
 letI : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
 have hk : RingHom.ker τ ≠ ⊥ := by
   obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp p.val.ne_bot
   let x : A.R := algebraMap (𝓞 F) A.R z
   have hx : τ (i x) = 0 := by
     rw [hi, hτ, Ideal.Quotient.eq_zero_iff_mem]
     exact Ideal.mem_map_of_mem _ hz
   intro he
   have hzero : i x = 0 := by
     rw [← Ideal.mem_bot, ← he]
     exact hx
   have hi0 := congrArg (fun y : LocalIntegers p => (y : LocalField p)) hzero
   have hzF : (z : F) = 0 := by
     apply (algebraMap F (LocalField p)).injective
     simpa [i, x, SArithmeticData.exteriorIntegerMap] using hi0
   exact hz0 (RingOfIntegers.ext hzF)
 have hmax : RingHom.ker τ = IsLocalRing.maximalIdeal (LocalIntegers p) := by
   letI : (RingHom.ker τ).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hk inferInstance
   exact IsLocalRing.eq_maximalIdeal inferInstance
 apply RingHom.ext
 intro x
 obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e.symm (res x))
 have hr : res (i z) = res x := by
   have he := A.exteriorLocalResidueEquiv_apply (primeIdeal p) p.val rfl z
   change e (Ideal.Quotient.mk _ z) = res (i z) at he
   rw [hz, e.apply_symm_apply] at he
   exact he.symm
 have hd : x - i z ∈ RingHom.ker τ := by
   rw [hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, hr, sub_self]
 have ht : τ x = τ (i z) := by
   have hh : τ (x - i z) = 0 := hd
   simpa only [map_sub, sub_eq_zero] using hh
 rw [ht, hi, hτ]
 change Ideal.Quotient.mk _ z = e.symm (res x)
 exact hz

def localReduction (p : ExteriorPrime A) :
    LocalIntegers p →+* (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Classical.choose (localReduction_exists_unique p)

theorem localReduction_sInteger (p : ExteriorPrime A) (x : A.R) :
    localReduction p
      ⟨algebraMap F (LocalField p) (x : F), sInteger_local_integral p x⟩ =
        Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x := by
  exact (Classical.choose_spec (localReduction_exists_unique p)).1 x

def chiOnUnits (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) : ℂ :=
  chi (σ := σ) p (localReduction p u.val)

theorem chiOnUnits_ne_zero (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) :
    chiOnUnits (σ := σ) p u ≠ 0 := by
  exact MulChar.apply_ne_zero_iff.mpr (u.isUnit.map (localReduction p))

theorem chiOnUnits_pow_six (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) :
    chiOnUnits (σ := σ) p u ^ (6 : ℕ) = 1 := by
  let v := Units.map (localReduction p).toMonoidHom u
  change (A.sexticResiduePowerChar σ (primeIdeal p) 1) (v : _) ^ 6 = 1
  have he : SArithmeticData.sexticExponent 1 = 1 := by decide
  rw [SArithmeticData.sexticResiduePowerChar, he, pow_one, MulChar.ofUnitHom_coe]
  change σ ((A.sexticResidueFamily (primeIdeal p) v : Fˣ) : F) ^ 6 = 1
  rw [← map_pow]
  have h := congrArg (fun x : Fˣ => (x : F))
    (A.sexticResidueFamily_normalized.1 (primeIdeal p) v)
  simpa using congrArg σ h

 def quo (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) : LocalIntegers p →+* Residue C p n :=
  (residueEquiv C p n).symm.toRingHom.comp (Ideal.Quotient.mk _)
private lemma quo_integer (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
 quo C p n (integerMap p x) = residueMap C p n x := by
  apply (residueEquiv C p n).injective
  change (residueEquiv C p n) ((residueEquiv C p n).symm (Ideal.Quotient.mk _ (integerMap p x))) = _
  rw [RingEquiv.apply_symm_apply]
  exact (residueEquiv_mk C p n x).symm
private lemma quo_eq_iff (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) (x y : LocalIntegers p) :
 quo C p n x = quo C p n y ↔ Congruent C p n (x : LocalField p) (y : LocalField p) := by
  change (residueEquiv C p n).symm (Ideal.Quotient.mk _ x) = (residueEquiv C p n).symm (Ideal.Quotient.mk _ y) ↔ _
  rw [(residueEquiv C p n).symm.injective.eq_iff, Ideal.Quotient.eq]
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have hh := congrArg (fun z : LocalIntegers p => (z : LocalField p)) hr
    simpa [localUniformizer, integerMap, uniformizer, mul_comm] using hh.symm
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    simpa [localUniformizer, integerMap, uniformizer, mul_comm] using hr.symm
 lemma quo_lift (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) (x : Residue C p n) :
 quo C p n (integerMap p ((lifts C p n).val x)) = x := by
  rw [quo_integer]
  exact (lifts C p n).property x
private lemma reduction_quo (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
 (n : ℕ) (hn : n ≠ 0) (x : LocalIntegers p) :
 reduction C p n hn (quo C p n x) = localReduction p x := by
 have hh : (reduction C p n hn).comp (quo C p n) = localReduction p := by
   apply (Classical.choose_spec (localReduction_exists_unique p)).2
   intro z
   rw [← show (integerMap p z) = ⟨algebraMap F (LocalField p) (z : F), sInteger_local_integral p z⟩ from Subtype.ext rfl]
   simp only [RingHom.comp_apply, quo_integer]
   exact Ideal.Quotient.factor_mk _ z
 exact congrArg (fun f : LocalIntegers p →+* (A.R ⧸ A.extendIdeal (primeIdeal p)) => f x) hh
lemma quo_congruent (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (x : LocalIntegers p) (y : Residue C p n) :
 Congruent C p n (x : LocalField p) (canonicalLocalRepresentative C p n y) ↔ quo C p n x = y := by
 change Congruent C p n (x : LocalField p) ((integerMap p ((lifts C p n).val y) : LocalIntegers p) : LocalField p) ↔ _
 rw [← quo_eq_iff, quo_lift]
 def resUnit (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) : (Residue C p n)ˣ := Units.map (quo C p n).toMonoidHom u
private lemma chi_power_nat (p : ExteriorPrime A) (n : ℕ) (u : (LocalIntegers p)ˣ) :
 A.sexticResiduePowerChar σ (primeIdeal p) (n : ℤ) (localReduction p u.val) = chiOnUnits (σ := σ) p u ^ n := by
 rw [sexticPower_eq_chi_pow]
 rw [← show ((Units.map (localReduction p).toMonoidHom u : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ) : _) = localReduction p u.val from rfl]
 rw [MulChar.pow_apply_coe]
 change chiOnUnits (σ := σ) p u ^ SArithmeticData.sexticExponent (n : ℤ) = _
 have h : SArithmeticData.sexticExponent (n : ℤ) = n % 6 := by
   simp [SArithmeticData.sexticExponent, Int.toNat_emod (Int.natCast_nonneg n) (by decide : (0 : ℤ) ≤ 6)]
 rw [h]
 exact pow_eq_pow_mod _ (chiOnUnits_pow_six p u) |>.symm
private lemma mask_resUnit (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) (x : Residue C p n) :
 maskedPower C p n n ((resUnit C p n u : Residue C p n) * x) =
 chiOnUnits (σ := σ) p u ^ n * maskedPower C p n n x := by
 by_cases hn : n = 0
 · subst n; simp [maskedPower]
 · have hu : IsUnit (resUnit C p n u : Residue C p n) := Units.isUnit _
   have hux : IsUnit ((resUnit C p n u : Residue C p n) * x) ↔ IsUnit x := by rw [IsUnit.mul_iff]; simp [hu]
   simp only [maskedPower, dif_neg hn, hux]
   by_cases hx : IsUnit x
   · simp only [if_pos hx]
     rw [map_mul, map_mul]
     have hh : reduction C p n hn (resUnit C p n u : Residue C p n) = localReduction p u.val := reduction_quo C p n hn u.val
     rw [hh, chi_power_nat]
   · simp [hx]
 def perm (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) : Equiv.Perm (Residue C p n) := (resUnit C p n u).mulLeft
 def scaledLifts (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) : LocalLifts C p n where
 val x := (u.val : LocalField p) * canonicalLocalRepresentative C p n ((perm C p n u).symm x)
 integral x := (LocalIntegers p).mul_mem _ _ u.val.property (sInteger_local_integral p _)
 congruent x := by
   let z := u.val * integerMap p ((lifts C p n).val ((perm C p n u).symm x))
   change Congruent C p n (z : LocalField p) _
   rw [quo_congruent]
   change quo C p n (u.val * _) = _
   rw [map_mul, quo_lift]
   exact (perm C p n u).apply_symm_apply x
private lemma scaledLifts_apply (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) (x : Residue C p n) :
 (scaledLifts C p n u).val (perm C p n u x) =
 (u.val : LocalField p) * canonicalLocalRepresentative C p n x := by
 simp [scaledLifts]
private lemma congruent_mul_unit (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
 (u : (LocalIntegers p)ˣ) (x y : LocalField p) :
 Congruent C p n ((u.val : LocalField p) * x) ((u.val : LocalField p) * y) ↔ Congruent C p n x y := by
 constructor
 · rintro ⟨r, hr⟩
   refine ⟨u.inv * r, ?_⟩
   have hu : (u.inv : LocalField p) * (u.val : LocalField p) = 1 := by
     exact_mod_cast u.inv_val
   have hh := congrArg (fun z => (u.inv : LocalField p) * z) hr
   calc
    x - y = (u.inv : LocalField p) * ((u.val : LocalField p) * x - (u.val : LocalField p) * y) := by rw [← mul_sub, ← mul_assoc, hu, one_mul]
    _ = _ := by simpa [mul_assoc, mul_left_comm, mul_comm] using hh
 · rintro ⟨r, hr⟩
   refine ⟨u.val * r, ?_⟩
   calc
    (u.val : LocalField p) * x - (u.val : LocalField p) * y = (u.val : LocalField p) * (x-y) := (mul_sub _ _ _).symm
    _ = _ := by rw [hr]; simp [mul_assoc, mul_left_comm, mul_comm]
private lemma phase_substitute (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
 (t k J : ℕ) (s a h : (LocalIntegers p)ˣ) (d v : LocalField p) :
 rawPhase C p t k J s a h (((h / a).val : LocalField p) * d) (((s * a / h).val : LocalField p) * v) =
 rawPhase C p t k J 1 1 1 d v := by
 have ha : (a.val : LocalField p) ≠ 0 := by exact_mod_cast a.ne_zero
 have hh : (h.val : LocalField p) ≠ 0 := by exact_mod_cast h.ne_zero
 have hs : (s.val : LocalField p) ≠ 0 := by exact_mod_cast s.ne_zero
 have hi (u : (LocalIntegers p)ˣ) : (((u⁻¹).val : LocalIntegers p) : LocalField p) = (u.val : LocalField p)⁻¹ := by
   apply eq_inv_of_mul_eq_one_left
   exact_mod_cast u.inv_val
 unfold rawPhase
 congr 2
 simp only [div_eq_mul_inv, Units.val_mul]
 simp
 simp only [hi]
 field_simp
 <;> ring
private lemma numerator_substitute (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
 (t k J : ℕ) (a h : (LocalIntegers p)ˣ) (d : LocalField p) :
 numeratorCongruence C p t k J a h (((h / a).val : LocalField p) * d) ↔
 numeratorCongruence C p t k J 1 1 d := by
 have ha : (a.val : LocalField p) * (((a⁻¹).val : LocalIntegers p) : LocalField p) = 1 := by exact_mod_cast a.val_inv
 have he : (a.val : LocalField p) * uniformizer C p ^ t * (((h/a).val : LocalField p) * d) =
  (h.val : LocalField p) * (uniformizer C p ^ t * d) := by
  simp only [div_eq_mul_inv, Units.val_mul]
  simp
  calc
   (a.val : LocalField p) * uniformizer C p ^ t * ((h.val : LocalField p) * (((a⁻¹).val : LocalIntegers p) : LocalField p) * d) =
    ((a.val : LocalField p) * (((a⁻¹).val : LocalIntegers p) : LocalField p)) * ((h.val : LocalField p) * (uniformizer C p ^ t * d)) := by ring
   _ = _ := by rw [ha, one_mul]
 unfold numeratorCongruence
 rw [he, congruent_mul_unit]
 simp
private lemma chi_mul (p : ExteriorPrime A) (u v : (LocalIntegers p)ˣ) :
 chiOnUnits (σ := σ) p (u * v) = chiOnUnits (σ := σ) p u * chiOnUnits (σ := σ) p v := by
 simp only [chiOnUnits, Units.val_mul, map_mul]
private lemma chi_inv (p : ExteriorPrime A) (u : (LocalIntegers p)ˣ) :
 chiOnUnits (σ := σ) p u⁻¹ = (chiOnUnits (σ := σ) p u)⁻¹ := by
 apply eq_inv_of_mul_eq_one_left
 rw [← chi_mul, inv_mul_cancel]
 simp [chiOnUnits]
private lemma chi_div (p : ExteriorPrime A) (u v : (LocalIntegers p)ˣ) :
 chiOnUnits (σ := σ) p (u / v) = chiOnUnits (σ := σ) p u / chiOnUnits (σ := σ) p v := by
 rw [div_eq_mul_inv, chi_mul, chi_inv, div_eq_mul_inv]
set_option backward.isDefEq.respectTransparency false in
private lemma R_substitute (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
 (t k J : ℕ) (s a h : (LocalIntegers p)ˣ) :
 R C p t k J s a h = chiOnUnits (σ := σ) p (h/a) ^ k * chiOnUnits (σ := σ) p (s*a/h) ^ t * R C p t k J 1 1 1 := by
 unfold R
 rw [RWithLifts_independent C p t k J s a h (canonicalLocalLifts C p k) (scaledLifts C p k (h/a)) (canonicalLocalLifts C p t) (scaledLifts C p t (s*a/h))]
 unfold RWithLifts
 rw [← Equiv.sum_comp (perm C p k (h/a))]
 dsimp only [canonicalLocalLifts]
 simp only [scaledLifts_apply, numerator_substitute]
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro d hd
 split_ifs with hc
 · rw [← Equiv.sum_comp (perm C p t (s*a/h))]
   simp only [scaledLifts_apply, phase_substitute]
   rw [show maskedPower C p k k (perm C p k (h/a) d) = chiOnUnits (σ := σ) p (h/a) ^ k * maskedPower C p k k d from mask_resUnit C p k (h/a) d]
   have hh : (∑ v : Residue C p t, maskedPower C p t t (perm C p t (s*a/h) v) * rawPhase C p t k J 1 1 1 (canonicalLocalRepresentative C p k d) (canonicalLocalRepresentative C p t v)) =
    chiOnUnits (σ := σ) p (s*a/h) ^ t * (∑ v : Residue C p t, maskedPower C p t t v * rawPhase C p t k J 1 1 1 (canonicalLocalRepresentative C p k d) (canonicalLocalRepresentative C p t v)) := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro v hv
     rw [show maskedPower C p t t (perm C p t (s*a/h) v) = chiOnUnits (σ := σ) p (s*a/h) ^ t * maskedPower C p t t v from mask_resUnit C p t (s*a/h) v]
     ring
   rw [hh]
   ring
 · simp
private lemma factor_expand (p : ExteriorPrime A) (t k : ℕ) (s a h : (LocalIntegers p)ˣ) :
 chiOnUnits (σ := σ) p (h/a) ^ k * chiOnUnits (σ := σ) p (s*a/h) ^ t =
 chiOnUnits (σ := σ) p h ^ ((k : ℤ)-(t : ℤ)) * chiOnUnits (σ := σ) p s ^ (t : ℤ) * chiOnUnits (σ := σ) p a ^ ((t : ℤ)-(k : ℤ)) := by
 rw [chi_div, chi_div, chi_mul]
 rw [zpow_sub₀ (chiOnUnits_ne_zero p h), zpow_sub₀ (chiOnUnits_ne_zero p a)]
 simp only [zpow_natCast, div_pow, mul_pow]
 ring

theorem R_unit_rescale (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (s a h : (LocalIntegers p)ˣ) :
    R C p t k J s a h =
      chiOnUnits (σ := σ) p h ^ ((k : ℤ) - (t : ℤ)) *
        chiOnUnits (σ := σ) p s ^ (t : ℤ) *
        chiOnUnits (σ := σ) p a ^ ((t : ℤ) - (k : ℤ)) * Ctk C p t k J := by
  rw [R_substitute, factor_expand, R_one_eq_Ctk]

end DedekindZetaZeroFree.CompatiblePrimeRawLocal

end
