module

public import DedekindZetaZeroFree.CharacterSums.Gauss.Sextic.LocalTable
public import DedekindZetaZeroFree.CharacterSums.Gauss.ZeroDepthLocalSums
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums.DepthOneShell
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

open LocalFiniteSumCompatibility CanonicalLocalGaussTable
private theorem mask_unit_zpow (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (a : ℤ) (x : Residue C p n)
    (hx : IsUnit x) :
    maskedPower C p n a x = chi (σ := σ) p (reduction C p n hn x) ^ a := by
  rw [maskedPower_eq_reduction C p n hn]
  let u := (hx.map (reduction C p n hn)).unit
  have hu : (u : A.R ⧸ A.extendIdeal (primeIdeal p)) = reduction C p n hn x :=
    (hx.map (reduction C p n hn)).unit_spec
  rw [← hu, MulChar.pow_apply_coe]
  let v := (chi (σ := σ) p).toUnitHom u
  have hv : v ^ (6 : ℕ) = 1 := by
    apply Units.ext
    exact chi_unit_sixth (σ := σ) p u u.isUnit
  have h := zpow_eq_zpow_emod' a hv
  have he : (SArithmeticData.sexticExponent a : ℤ) = a % 6 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  change v ^ a = v ^ (a % 6) at h
  rw [← he, zpow_natCast] at h
  have hh := congrArg (fun z : ℂˣ => (z : ℂ)) h
  simpa [v] using hh.symm

private theorem psi_mk_global (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    psi C p n (residueMap C p n x) =
      (A.fieldTraceCharacter ((x : F) / (generator C p : F) ^ n) : ℂ) := by
  unfold psi
  rw [quotientTrace_mk, ← fieldTrace_eq_negative_localTrace]

private theorem reduction_lift (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : Residue C p n) :
    reduction C p n hn x = Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) ((lifts C p n).val x) := by
  conv_lhs => rw [← (lifts C p n).property x]
  rfl

private theorem phase_split (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (hJ : 1 ≤ J)
    (d : Residue C p 1) (v : Residue C p t) :
    psi C p (1 + t) (residueMap C p (1 + t)
      ((generator C p ^ J - generator C p ^ t * (lifts C p 1).val d) * (lifts C p t).val v)) =
    psi C p t (residueMap C p t (generator C p ^ (J - 1)) * v) *
      psi C p 1 (-(residueMap C p 1 ((lifts C p t).val v)) * d) := by
  have hd : residueMap C p 1 ((lifts C p 1).val d) = d := (lifts C p 1).property d
  have hv : residueMap C p t ((lifts C p t).val v) = v := (lifts C p t).property v
  conv_rhs => rw [← hv, ← hd, ← map_mul, ← map_neg, ← map_mul]
  rw [psi_mk_global, psi_mk_global, psi_mk_global]
  rw [hv]
  have hg : (generator C p : F) ≠ 0 := by
    exact_mod_cast (generator_generates C p).1
  have he : (((generator C p ^ J - generator C p ^ t * (lifts C p 1).val d) *
      (lifts C p t).val v : A.R) : F) / (generator C p : F) ^ (1 + t) =
      (((generator C p ^ (J - 1) * (lifts C p t).val v : A.R) : F) / (generator C p : F) ^ t) +
      (((-((lifts C p t).val v) * (lifts C p 1).val d : A.R) : F) / (generator C p : F) ^ 1) := by
    have hj : J = (J - 1) + 1 := by omega
    change (((generator C p : F) ^ J - (generator C p : F) ^ t * ((lifts C p 1).val d : F)) *
      ((lifts C p t).val v : F)) / (generator C p : F) ^ (1 + t) =
      (generator C p : F) ^ (J - 1) * ((lifts C p t).val v : F) / (generator C p : F) ^ t +
        (-((lifts C p t).val v : F) * ((lifts C p 1).val d : F)) / (generator C p : F) ^ 1
    generalize ((lifts C p 1).val d : F) = b
    generalize ((lifts C p t).val v : F) = c
    conv_lhs => rw [hj, pow_add, pow_one]
    rw [pow_add, pow_one]
    field_simp
    <;> ring
  rw [he, AddChar.map_add_eq_mul]
  simp

local instance (p : ExteriorPrime A) : Field (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Ideal.Quotient.field _

private theorem inner_transform (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t : ℕ) (ht : 0 < t) (v : Residue C p t) :
    maskedPower C p t t v * T C p 1 (-residueMap C p 1 ((lifts C p t).val v)) =
      tau C p 1 * maskedPower C p t ((t : ℤ) - 1) v := by
  by_cases hv : IsUnit v
  · let r := reduction C p t (Nat.ne_of_gt ht) v
    have hr : IsUnit r := hv.map (reduction C p t (Nat.ne_of_gt ht))
    have he : depthOneEquiv C p (-residueMap C p 1 ((lifts C p t).val v)) = -r := by
      rw [(depthOneEquiv C p).map_neg]
      change -Ideal.Quotient.mk _ ((lifts C p t).val v) = -r
      exact congrArg Neg.neg (reduction_lift C p t (Nat.ne_of_gt ht) v).symm
    have hy : -residueMap C p 1 ((lifts C p t).val v) ≠ 0 := by
      intro h
      have hh := congrArg (depthOneEquiv C p) h
      rw [he, map_zero, neg_eq_zero] at hh
      exact (isUnit_iff_ne_zero.mp hr) hh
    rw [T_ne_zero C p 1 _ hy, he]
    have hc : chi (σ := σ) p (-r) = chi (σ := σ) p r := by
      rw [neg_eq_neg_one_mul, map_mul, chi_neg_one, one_mul]
    rw [hc, zpow_one, mask_unit_zpow C p t (Nat.ne_of_gt ht) _ _ hv,
      mask_unit_zpow C p t (Nat.ne_of_gt ht) _ _ hv]
    have hn : chi (σ := σ) p r ≠ 0 := (hr.map (chi (σ := σ) p)).ne_zero
    rw [zpow_sub₀ hn, zpow_one, div_eq_mul_inv]
    dsimp [r]
    ring
  · rw [maskedPower_nonunit C p t (Nat.ne_of_gt ht) _ v hv,
      maskedPower_nonunit C p t (Nat.ne_of_gt ht) _ v hv]
    simp

private theorem generator_residue_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n) :
    residueMap C p 1 (generator C p ^ n) = 0 := by
  have hg : residueMap C p 1 (generator C p) = 0 := by
    change Ideal.Quotient.mk (Ideal.span {generator C p ^ 1}) (generator C p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa using Ideal.subset_span (Set.mem_singleton (generator C p))
  rw [map_pow, hg, zero_pow (Nat.ne_of_gt hn)]

theorem regroup (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (ht : 0 < t) :
    Ctk C p t 1 J =
      if 1 ≤ J then
        tau C p 1 *
          ∑ v : Residue C p t, maskedPower C p t ((t : ℤ) - 1) v *
            psi C p t (residueMap C p t (generator C p ^ (J - 1)) * v)
      else 0 := by
  by_cases hJ : 1 ≤ J
  · rw [if_pos hJ]
    unfold Ctk
    have hcond (d : Residue C p 1) :
        residueMap C p 1 (generator C p ^ J) = residueMap C p 1 (generator C p ^ t) * d := by
      rw [generator_residue_zero C p J hJ, generator_residue_zero C p t ht, zero_mul]
    conv_lhs =>
      arg 2
      ext d
      rw [if_pos (hcond d)]
    simp_rw [phase_split C p t J hJ]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ v : Residue C p t,
          (maskedPower C p t t v * T C p 1 (-residueMap C p 1 ((lifts C p t).val v))) *
            psi C p t (residueMap C p t (generator C p ^ (J - 1)) * v) := by
        apply Finset.sum_congr rfl
        intro v _
        unfold T
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _
        norm_num only [Nat.cast_one]
        ring
      _ = _ := by
        simp_rw [inner_transform C p t ht]
        apply Finset.sum_congr rfl
        intro v _
        ring
  · rw [if_neg hJ]
    have hj : J = 0 := by omega
    subst J
    unfold Ctk
    have hne : (1 : Residue C p 1) ≠ 0 := by
      intro h
      have hh := congrArg (depthOneEquiv C p) h
      simpa using hh
    simp [generator_residue_zero C p t ht, hne]

end DedekindZetaZeroFree.LocalFiniteSums.DepthOneShell

end

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums.HigherTranslationCancellation
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

open LocalFiniteSumCompatibility

private theorem map_deep_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n m : ℕ) (hnm : n ≤ m) (r : A.R) :
    residueMap C p n (generator C p ^ m * r) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨generator C p ^ (m-n) * r, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hnm]
private theorem lift_difference (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x y : A.R)
    (h : residueMap C p n x = residueMap C p n y) :
    ∃ r : A.R, x - y = generator C p ^ n * r := by
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
private theorem generator_not_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ¬ IsUnit (generator C p) := by
  letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    (cftResidueEquiv p).toEquiv.nontrivial
  intro h
  have hz : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hu := h.map (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)))
  rw [hz] at hu
  exact not_isUnit_zero hu
private theorem penultimate_ne_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    residueMap C p (n+1) (generator C p ^ n) ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have he : generator C p ^ n * 1 = generator C p ^ n * (generator C p * r) := by
    simpa [pow_succ, mul_assoc] using hr
  have hi : 1 = generator C p * r := mul_left_cancel₀ (pow_ne_zero _ (generator_generates C p).1) he
  apply generator_not_unit C p
  exact isUnit_iff_exists_inv.mpr ⟨r, hi.symm⟩
private theorem lifted_unit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t n : ℕ) (ht : t ≠ 0) (hn : n ≠ 0)
    (v : Residue C p t) (hv : IsUnit v) :
    IsUnit (residueMap C p n ((lifts C p t).val v)) := by
  apply (reduction_isUnit C p n hn _).mp
  have he : reduction C p n hn (residueMap C p n ((lifts C p t).val v)) =
      reduction C p t ht v := by
    change Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) ((lifts C p t).val v) = _
    have hx : residueMap C p t ((lifts C p t).val v) = v := (lifts C p t).property v
    exact congrArg (reduction C p t ht) hx
  rw [he]
  exact hv.map (reduction C p t ht)
private theorem masked_translate (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (k : ℕ) (hk : 2 ≤ k) (b : ℤ)
    (d : Residue C p k) (r : A.R) :
    maskedPower C p k b (d + residueMap C p k (generator C p ^ (k-1) * r)) =
      maskedPower C p k b d := by
  rw [maskedPower_eq_reduction C p k (by omega), maskedPower_eq_reduction C p k (by omega)]
  apply congrArg (chi (σ := σ) p ^ SArithmeticData.sexticExponent b)
  rw [(reduction C p k (by omega)).map_add]
  have hz : reduction C p k (by omega) (residueMap C p k (generator C p ^ (k-1) * r)) = 0 := by
    change Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) _ = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    apply Ideal.mem_span_singleton.mpr
    refine ⟨generator C p ^ (k-2) * r, ?_⟩
    rw [← mul_assoc, ← pow_succ']
    congr 1
    congr 1
    omega
  rw [hz, add_zero]
private theorem phase_translate (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k : ℕ) (a r : A.R) (d : Residue C p k)
    (v : Residue C p t) :
    psi C p (k+t) (residueMap C p (k+t)
      ((a - generator C p ^ t * (lifts C p k).val
        (d + residueMap C p k (generator C p ^ (k-1) * r))) * (lifts C p t).val v)) =
    psi C p (k+t) (residueMap C p (k+t)
      ((a - generator C p ^ t * (lifts C p k).val d) * (lifts C p t).val v)) *
    psi C p (k+t) (residueMap C p (k+t)
      (-(generator C p ^ t * (generator C p ^ (k-1) * r) * (lifts C p t).val v))) := by
  obtain ⟨z, hz⟩ := lift_difference C p k
    ((lifts C p k).val (d + residueMap C p k (generator C p ^ (k-1) * r)))
    ((lifts C p k).val d + generator C p ^ (k-1) * r) (by
      rw [map_add]
      change (FiniteTransform.residueMap A.R.toSubring (generator C p ^ k))
        ((lifts C p k).val (d + residueMap C p k (generator C p ^ (k-1) * r))) =
        (FiniteTransform.residueMap A.R.toSubring (generator C p ^ k)) ((lifts C p k).val d) + _
      rw [(lifts C p k).property, (lifts C p k).property])
  have he := eq_add_of_sub_eq hz
  have hraw :
      (a - generator C p ^ t * (lifts C p k).val (d + residueMap C p k (generator C p ^ (k-1) * r))) * (lifts C p t).val v =
      ((a - generator C p ^ t * (lifts C p k).val d) * (lifts C p t).val v) +
      (-(generator C p ^ t * (generator C p ^ (k-1) * r) * (lifts C p t).val v)) -
      generator C p ^ (k+t) * (z * (lifts C p t).val v) := by
    rw [he, pow_add]
    ring
  rw [hraw, map_sub, map_add, map_deep_zero C p (k+t) (k+t) le_rfl, sub_zero]
  exact congrArg (fun z : Circle => (z : ℂ)) ((quotientTrace C p (k+t)).map_add_eq_mul _ _)
private theorem nontrivial_translation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k : ℕ) (ht : 0 < t) (hk : 2 ≤ k)
    (v : Residue C p t) (hv : IsUnit v) :
    ∃ r : A.R, psi C p (k+t) (residueMap C p (k+t)
      (-(generator C p ^ t * (generator C p ^ (k-1) * r) * (lifts C p t).val v))) ≠ 1 := by
  let n := t + (k-1)
  have hn : n+1 = k+t := by dsimp [n]; omega
  have hx : residueMap C p (k+t)
      (generator C p ^ n * (lifts C p t).val v) ≠ 0 := by
    rw [map_mul]
    intro h
    have hu := lifted_unit C p t (k+t) (by omega) (by omega) v hv
    apply penultimate_ne_zero C p n
    rw [hn]
    exact hu.mul_right_cancel (by simpa using h)
  obtain ⟨y, hy⟩ := quotientTrace_primitive C p (k+t) _ hx
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r, ?_⟩
  have he : -(generator C p ^ t * (generator C p ^ (k-1) * r) * (lifts C p t).val v) =
      -(generator C p ^ n * (lifts C p t).val v * r) := by
    dsimp [n]
    rw [pow_add]
    ring
  rw [he, map_neg, map_mul]
  unfold psi
  rw [AddChar.map_neg_eq_inv]
  intro h
  apply hy
  have hh : (quotientTrace C p (k+t)) (residueMap C p (k+t)
      (generator C p ^ n * (lifts C p t).val v) * residueMap C p (k+t) r) = 1 := by
    apply inv_eq_one.mp
    apply Circle.coe_injective
    exact h
  rw [← hr]
  exact hh

theorem unit_column_eq_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k : ℕ) (ht : 0 < t) (hk : 2 ≤ k)
    (a : A.R) (b : ℤ) (v : Residue C p t) (hv : IsUnit v) :
    (∑ d : Residue C p k,
      if residueMap C p k a = residueMap C p k (generator C p ^ t) * d then
        maskedPower C p k b d *
          psi C p (k + t) (residueMap C p (k + t)
            ((a - generator C p ^ t * (lifts C p k).val d) * (lifts C p t).val v))
      else 0) = 0 := by
  obtain ⟨r, hr⟩ := nontrivial_translation C p t k ht hk v hv
  let δ := residueMap C p k (generator C p ^ (k-1) * r)
  let c := psi C p (k+t) (residueMap C p (k+t)
    (-(generator C p ^ t * (generator C p ^ (k-1) * r) * (lifts C p t).val v)))
  let f := fun d : Residue C p k =>
    if residueMap C p k a = residueMap C p k (generator C p ^ t) * d then
      maskedPower C p k b d * psi C p (k+t) (residueMap C p (k+t)
        ((a - generator C p ^ t * (lifts C p k).val d) * (lifts C p t).val v))
    else 0
  change (∑ d, f d) = 0
  have hδ : residueMap C p k (generator C p ^ t) * δ = 0 := by
    dsimp [δ]
    rw [← map_mul]
    have he : generator C p ^ t * (generator C p ^ (k-1) * r) = generator C p ^ (t+(k-1)) * r := by
      rw [pow_add, mul_assoc]
    rw [he]
    exact map_deep_zero C p k (t+(k-1)) (by omega) r
  have hf (d : Residue C p k) : f (d + δ) = f d * c := by
    have hc : residueMap C p k (generator C p ^ t) * (d + δ) =
        residueMap C p k (generator C p ^ t) * d := by rw [mul_add, hδ, add_zero]
    dsimp [f]
    rw [hc]
    split_ifs with hd
    · dsimp [δ, c]
      rw [masked_translate C p k hk b d r, phase_translate C p t k a r d v]
      ring
    · simp
  have hs : (∑ d, f d) = (∑ d, f d) * c := by
    calc
      (∑ d, f d) = ∑ d, f (d + δ) := (Fintype.sum_equiv (Equiv.addRight δ) _ _ (fun _ => rfl)).symm
      _ = ∑ d, f d * c := Finset.sum_congr rfl (fun d _ => hf d)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hz : (∑ d, f d) * (c-1) = 0 := by
    rw [mul_sub, mul_one, ← hs, sub_self]
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hr)

end DedekindZetaZeroFree.LocalFiniteSums.HigherTranslationCancellation

end

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain
noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums.PrimePowerFourier
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

 noncomputable def fiberMap (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ) :
    Residue C p 1 × Residue C p n → Residue C p (n+1) :=
  fun v => residueMap C p (n+1) ((lifts C p 1).val v.1 + generator C p * (lifts C p n).val v.2)
private lemma difference (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (x y : A.R) (h : residueMap C p n x = residueMap C p n y) :
    ∃ r : A.R, x-y = generator C p ^ n * r := by
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
private theorem fiberMap_bijective (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : Function.Bijective (fiberMap C p n) := by
  have hg := (generator_generates C p).1
  have hl (m : ℕ) (v : Residue C p m) : residueMap C p m ((lifts C p m).val v) = v :=
    (lifts C p m).property v
  constructor
  · intro v w h
    obtain ⟨r, hr⟩ := difference C p (n+1) _ _ h
    have hv : v.1 = w.1 := by
      have hv' : residueMap C p 1 ((lifts C p 1).val v.1) =
          residueMap C p 1 ((lifts C p 1).val w.1) := by
        apply Ideal.Quotient.eq.mpr
        apply Ideal.mem_span_singleton.mpr
        refine ⟨generator C p ^ n * r - (lifts C p n).val v.2 + (lifts C p n).val w.2, ?_⟩
        calc
          _ = generator C p ^ (n+1) * r - generator C p *
              ((lifts C p n).val v.2 - (lifts C p n).val w.2) := by linear_combination hr
          _ = _ := by rw [pow_succ]; ring
      simpa only [hl] using hv'
    apply Prod.ext hv
    have hh : (lifts C p 1).val v.1 = (lifts C p 1).val w.1 := congrArg _ hv
    have hj : (lifts C p n).val v.2 - (lifts C p n).val w.2 = generator C p ^ n * r := by
      apply mul_left_cancel₀ hg
      calc
        _ = generator C p ^ (n+1) * r := by linear_combination hr - hh
        _ = _ := by rw [pow_succ]; ring
    have he : residueMap C p n ((lifts C p n).val v.2) =
        residueMap C p n ((lifts C p n).val w.2) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr ⟨r, hj⟩)
    simpa only [hl] using he
  · intro m
    let x := (lifts C p (n+1)).val m
    let v := residueMap C p 1 x
    obtain ⟨j, hj⟩ := difference C p 1 x ((lifts C p 1).val v) (by rw [hl])
    refine ⟨(v, residueMap C p n j), ?_⟩
    change residueMap C p (n+1) ((lifts C p 1).val v + generator C p *
      (lifts C p n).val (residueMap C p n j)) = m
    rw [← hl (n+1) m]
    obtain ⟨r, hr⟩ := difference C p n ((lifts C p n).val (residueMap C p n j)) j (hl n _)
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    change (lifts C p 1).val v + generator C p *
      (lifts C p n).val (residueMap C p n j) - x = generator C p ^ (n+1) * r
    simp only [pow_one] at hj
    calc
      _ = generator C p * (generator C p ^ n * r) := by
        linear_combination generator C p * hr - hj
      _ = _ := by rw [pow_succ]; ring

private lemma unit_power_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    IsUnit (residueMap C p (n+1) x) ↔ IsUnit (residueMap C p 1 x) := by
  change IsUnit (Ideal.Quotient.mk (Ideal.span {generator C p ^ (n+1)}) x) ↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {generator C p ^ 1}) x)
  rw [pow_one, ← Ideal.span_singleton_pow]
  exact Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk _ (by omega)
private lemma fiber_mask (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (x : Residue C p 1) (y : Residue C p n) :
    maskedPower C p (n+1) a (fiberMap C p n (x,y)) = maskedPower C p 1 a x := by
  have hl (m : ℕ) (v : Residue C p m) : residueMap C p m ((lifts C p m).val v) = v :=
    (lifts C p m).property v
  have hg : residueMap C p 1 (generator C p) = 0 := by
    change Ideal.Quotient.mk (Ideal.span {generator C p ^ 1}) _ = 0
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hu : IsUnit (fiberMap C p n (x,y)) ↔ IsUnit x := by
    rw [fiberMap, unit_power_iff]
    simp only [map_add, map_mul, hg, zero_mul, add_zero, hl]
  have hred : reduction C p (n+1) (by omega) (fiberMap C p n (x,y)) =
      reduction C p 1 (by omega) x := by
    have hr (m : ℕ) (hm : m ≠ 0) (r : A.R) :
        reduction C p m hm (residueMap C p m r) =
          Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) r := rfl
    rw [fiberMap, hr]
    conv_rhs => rw [← hl 1 x, hr]
    change Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
      ((lifts C p 1).val x + generator C p * (lifts C p n).val y) =
      Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) ((lifts C p 1).val x)
    have hg' : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← (generator_generates C p).2]
      exact Ideal.subset_span (by simp)
    simp only [map_add, map_mul, hg', zero_mul, add_zero]
  simp only [maskedPower, Nat.succ_ne_zero, dif_neg, hu, hred, one_ne_zero]

private lemma fiber_phase (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (x : Residue C p 1) (y : Residue C p n) :
    psi C p (n+1) (residueMap C p (n+1) (generator C p ^ J) * fiberMap C p n (x,y)) =
      psi C p (n+1) (residueMap C p (n+1)
        (generator C p ^ J * (lifts C p 1).val x)) *
      psi C p n (residueMap C p n (generator C p ^ J) * y) := by
  have hg : (generator C p : F) ≠ 0 := by exact_mod_cast (generator_generates C p).1
  have hl : residueMap C p n ((lifts C p n).val y) = y := (lifts C p n).property y
  rw [fiberMap, ← map_mul, psi_residueMap]
  conv_rhs => arg 2; rw [← hl, ← map_mul, psi_residueMap]
  rw [psi_residueMap]
  simp only [Prod.fst, Prod.snd]
  have heq : ((generator C p ^ J * ((lifts C p 1).val x + generator C p *
      (lifts C p n).val y) : A.R) : F) / (generator C p ^ (n+1) : A.R) =
      ((generator C p ^ J * (lifts C p 1).val x : A.R) : F) / (generator C p ^ (n+1) : A.R) +
      ((generator C p ^ J * (lifts C p n).val y : A.R) : F) / (generator C p ^ n : A.R) := by
    push_cast
    generalize ((lifts C p 1).val x : F) = X
    generalize ((lifts C p n).val y : F) = Y
    rw [pow_succ]
    field_simp
    <;> ring
  rw [heq, AddChar.map_add_eq_mul]
  rfl
private lemma phase_descend (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) (hJ : n ≤ J) (x : Residue C p 1) :
    psi C p (n+1) (residueMap C p (n+1) (generator C p ^ J * (lifts C p 1).val x)) =
      psi C p 1 (residueMap C p 1 (generator C p ^ (J-n)) * x) := by
  have hl : residueMap C p 1 ((lifts C p 1).val x) = x := (lifts C p 1).property x
  have hg : (generator C p : F) ≠ 0 := by exact_mod_cast (generator_generates C p).1
  conv_rhs => rw [← hl, ← map_mul, psi_residueMap]
  rw [psi_residueMap]
  congr 2
  push_cast
  generalize ((lifts C p 1).val x : F) = X
  have he : (generator C p : F) ^ J = (generator C p : F) ^ (J-n) *
      (generator C p : F) ^ n := by rw [← pow_add, Nat.sub_add_cancel hJ]
  rw [he, pow_succ, pow_one]
  field_simp

private lemma generator_nonunit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ¬ IsUnit (generator C p) := by
  have hI : A.extendIdeal (primeIdeal p) ≠ ⊤ :=
    A.residue_extendIdeal_ne_top (primeIdeal p) p.val.isPrime.ne_top
  letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    Ideal.Quotient.nontrivial_iff.mpr hI
  intro hu
  have hh := hu.map (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)))
  have hg : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.subset_span (by simp)
  rw [hg] at hh
  exact not_isUnit_zero hh
private lemma residue_pow_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) :
    residueMap C p n (generator C p ^ J) = 0 ↔ n ≤ J := by
  change Ideal.Quotient.mk (Ideal.span {generator C p ^ n}) (generator C p ^ J) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow_iff (generator_generates C p).1 (generator_nonunit C p)
private lemma residue_card (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    (Fintype.card (Residue C p n) : ℂ) = (Q p : ℂ) ^ n := by
  have hgen : A.Generates (powerIdeal p n) (generator C p ^ n) := by
    refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
    rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
    exact (Ideal.map_pow _ _ _).symm
  have he : Nat.card (Residue C p n) = Ideal.absNorm (p.val.asIdeal ^ n) := by
    change Nat.card (A.R ⧸ Ideal.span {generator C p ^ n}) = _
    rw [hgen.2]
    exact A.exteriorResidue_card (powerIdeal p n)
  rw [Nat.card_eq_fintype_card] at he
  rw [he]
  simp [Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal, map_pow]

theorem masked_fourier_prime_power (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n M : ℕ) (hn : 0 < n) (a : ℤ) :
    (∑ v : Residue C p n, maskedPower C p n a v *
      psi C p n (residueMap C p n (generator C p ^ M) * v)) =
      if n - 1 ≤ M then
        (Q p : ℂ) ^ (n - 1) * T C p a
          (residueMap C p 1 (generator C p ^ (M - (n - 1))))
      else 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [← Fintype.sum_bijective (fiberMap C p r) (fiberMap_bijective C p r)
    (fun z => maskedPower C p (r+1) a (fiberMap C p r z) *
      psi C p (r+1) (residueMap C p (r+1) (generator C p ^ M) * fiberMap C p r z))
    (fun v => maskedPower C p (r+1) a v *
      psi C p (r+1) (residueMap C p (r+1) (generator C p ^ M) * v)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp_rw [fiber_mask, fiber_phase, ← mul_assoc, ← Finset.mul_sum]
  have hs : (∑ y : Residue C p r, psi C p r (residueMap C p r (generator C p ^ M) * y)) =
      if r ≤ M then (Fintype.card (Residue C p r) : ℂ) else 0 := by
    simp_rw [mul_comm]
    rw [psi_sum_mul, residue_pow_zero]
    split_ifs <;> rfl
  simp_rw [hs]
  by_cases hM : r ≤ M
  · simp only [hM, if_true]
    simp_rw [phase_descend C p r M hM]
    rw [residue_card]
    unfold T
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp [hM]

end DedekindZetaZeroFree.LocalFiniteSums.PrimePowerFourier

end

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private theorem norm_char_le {R : Type*} [CommRing R] [Finite R]
    (χ : MulChar R ℂ) (x : R) : ‖χ x‖ ≤ 1 := by
  classical
  letI := Fintype.ofFinite Rˣ
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using h.le
  · simp [MulChar.map_nonunit χ hx]
private theorem norm_mask_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (a : ℤ) (x : Residue C p n) :
    ‖maskedPower C p n a x‖ ≤ 1 := by
  unfold maskedPower
  split_ifs with hn hx
  · simp
  · letI := A.exteriorResidue_finite (primeIdeal p)
    exact norm_char_le _ _
  · simp
private theorem card_residue (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : (Fintype.card (Residue C p n) : ℝ) = Q p ^ n := by
  have hg : A.Generates (powerIdeal p n) (generator C p ^ n) := by
    refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
    rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
    exact (Ideal.map_pow _ _ _).symm
  have hc := A.exteriorResidue_card (powerIdeal p n)
  rw [← hg.2] at hc
  change Nat.card (Residue C p n) = _ at hc
  rw [Nat.card_eq_fintype_card] at hc
  rw [hc]
  simp [Q, SArithmeticData.exteriorNorm, powerIdeal, ExteriorIdealEuler.pow, idealNorm]

private theorem tau_norm_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) : ‖tau C p 1‖ ≤ Real.sqrt (Q p) := by
  have h := NormalizedProbe.PrincipalData.norm_idealGauss_le_one A σ hS (primeIdeal p)
    (generator C p) (generator_generates C p) 1
  have hg : A.Generates (primeIdeal p) (generator C p) := generator_generates C p
  have he : powerIdeal p 1 = primeIdeal p := by apply Subtype.ext; simp [powerIdeal, ExteriorIdealEuler.pow]
  have hq : Ideal.span ({generator C p} : Set A.R) = A.extendIdeal (primeIdeal p) := hg.2
  let e : Residue C p 1 ≃+* (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
    Ideal.quotientEquivAlgOfEq ℤ (by
      change Ideal.span ({generator C p ^ 1} : Set A.R) = A.extendIdeal (primeIdeal p)
      simpa only [pow_one] using hq) |>.toRingEquiv
  letI := A.exteriorResidue_finite (primeIdeal p)
  letI := Fintype.ofFinite (A.R ⧸ A.extendIdeal (primeIdeal p))
  have hm (x : Residue C p 1) : maskedPower C p 1 1 x =
      A.sexticResiduePowerChar σ (primeIdeal p) 1 (e x) := by
    unfold maskedPower
    simp only [Nat.one_ne_zero, ↓reduceDIte]
    split_ifs with hx
    · congr 1
    · apply (MulChar.map_nonunit _ _).symm
      intro h
      apply hx
      have h' : IsUnit (e.symm (e x)) := h.map e.symm.toMonoidHom
      simpa only [e.symm_apply_apply] using h'
  have hp (x : Residue C p 1) : psi C p 1 x =
      (A.residueTraceCharacter hS (primeIdeal p) (generator C p) hg (e x) : ℂ) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change psi C p 1 (residueMap C p 1 x) = _
    have cast_mk (I J : Ideal A.R) (h : I = J)
        (h' : AddChar (A.R ⧸ I) Circle = AddChar (A.R ⧸ J) Circle)
        (ψ : AddChar (A.R ⧸ I) Circle) (r : A.R) :
        h'.mp ψ (Ideal.Quotient.mk J r) = ψ (Ideal.Quotient.mk I r) := by
      subst J
      rfl
    have hg1 : A.Generates (powerIdeal p 1) (generator C p ^ 1) := by
      simpa only [he, pow_one] using hg
    have hc : quotientTrace C p 1 (residueMap C p 1 x) =
        (A.residueTraceCharacter hS (powerIdeal p 1) (generator C p ^ 1) hg1)
          (Ideal.Quotient.mk _ x) := by
      unfold quotientTrace residueMap FiniteTransform.residueMap
      apply cast_mk _ _ hg1.2.symm
    have hl : quotientTrace C p 1 (residueMap C p 1 x) =
        A.fieldTraceCharacter ((x : F) / (generator C p : F) ^ 1) := by
      rw [hc, A.residueTraceCharacter_apply]
      simp
    change (quotientTrace C p 1 (residueMap C p 1 x) : ℂ) = _
    rw [hl]
    change _ = (A.residueTraceCharacter hS (primeIdeal p) (generator C p) hg
      (Ideal.Quotient.mk _ x) : ℂ)
    rw [A.residueTraceCharacter_apply]
    simp
  have hs : tau C p 1 = ∑ x : A.R ⧸ A.extendIdeal (primeIdeal p),
      A.sexticResiduePowerChar σ (primeIdeal p) 1 x *
        (A.residueTraceCharacter hS (primeIdeal p) (generator C p) hg x : ℂ) := by
    unfold tau T
    simp only [one_mul]
    exact Fintype.sum_equiv e.toEquiv _ _ (fun x => by rw [hm, hp]; rfl)
  rw [hs]
  unfold SArithmeticData.idealGauss at h
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hpos : 0 < Q p := by
    change 0 < (Ideal.absNorm (primeIdeal p).val : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => (primeIdeal p).property.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := (inv_mul_le_iff₀ (Real.sqrt_pos.mpr hpos)).mp h
  simpa only [mul_one] using hh
private theorem norm_T_le_test (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (a : ℤ) (y : Residue C p 1) : ‖T C p a y‖ ≤ Q p := by
  unfold T
  calc
    _ ≤ ∑ x : Residue C p 1, ‖maskedPower C p 1 a x * psi C p 1 (y * x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue C p 1, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul, psi, Circle.norm_coe, mul_one] using norm_mask_le C p 1 a x
    _ = Q p := by simp [card_residue C p 1]

theorem Ctk_one (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (ht : 0 < t) :
    Ctk C p t 1 J =
      if t ≤ J then
        tau C p 1 * (Q p : ℂ) ^ (t - 1) *
          T C p ((t : ℤ) - 1)
            (residueMap C p 1 (generator C p ^ (J - t)))
      else 0 := by
  rw [DepthOneShell.regroup C p t J ht]
  by_cases hJ : 1 ≤ J
  · rw [if_pos hJ, PrimePowerFourier.masked_fourier_prime_power C p t (J - 1) ht]
    have hdepth : t - 1 ≤ J - 1 ↔ t ≤ J := by omega
    have hexp : J - 1 - (t - 1) = J - t := by omega
    simp only [hdepth, hexp]
    split_ifs
    · exact (mul_assoc _ _ _).symm
    · simp
  · have hnot : ¬t ≤ J := by omega
    rw [if_neg hJ, if_neg hnot]

theorem Ctk_eq_zero_of_two_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t k J : ℕ) (ht : 0 < t) (hk : 2 ≤ k) :
    Ctk C p t k J = 0 := by
  classical
  unfold Ctk
  calc
    _ = ∑ d : Residue C p k, ∑ v : Residue C p t,
        maskedPower C p t t v *
          (if residueMap C p k (generator C p ^ J) =
              residueMap C p k (generator C p ^ t) * d then
            maskedPower C p k k d *
              psi C p (k + t) (residueMap C p (k + t)
                ((generator C p ^ J - generator C p ^ t * (lifts C p k).val d) *
                  (lifts C p t).val v))
          else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with hc
      · simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      · simp
    _ = ∑ v : Residue C p t, maskedPower C p t t v *
        ∑ d : Residue C p k,
          (if residueMap C p k (generator C p ^ J) =
              residueMap C p k (generator C p ^ t) * d then
            maskedPower C p k k d *
              psi C p (k + t) (residueMap C p (k + t)
                ((generator C p ^ J - generator C p ^ t * (lifts C p k).val d) *
                  (lifts C p t).val v))
          else 0) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      by_cases hu : IsUnit v
      · rw [HigherTranslationCancellation.unit_column_eq_zero C p t k ht hk
          (generator C p ^ J) k v hu, mul_zero]
      · have hm : maskedPower C p t t v = 0 := by
          simp [maskedPower, Nat.ne_of_gt ht, hu]
        rw [hm, zero_mul]

theorem norm_Ctk_zero_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (ht : 0 < t) :
    ‖Ctk C p t 0 J‖ ≤ Q p ^ t := by
  classical
  unfold Ctk
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _d : Residue C p 0, (Q p ^ t) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · calc
          _ ≤ 1 * (∑ _v : Residue C p t, (1 : ℝ)) := by
            apply (norm_mul _ _).le.trans
            apply mul_le_mul (norm_mask_le C p 0 0 d) _ (norm_nonneg _) (by norm_num)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
            intro v hv
            calc
              _ = ‖maskedPower C p t t v‖ * 1 := by simp only [norm_mul, psi, Circle.norm_coe]
              _ ≤ 1 := by simpa using norm_mask_le C p t t v
          _ = Q p ^ t := by simp [card_residue C p t]
      · simp only [norm_zero]
        exact pow_nonneg (by simp [Q, SArithmeticData.exteriorNorm, idealNorm]) _
    _ = Q p ^ t := by simp [card_residue C p 0]

theorem norm_Ctk_one_le (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (ht : 0 < t) :
    ‖Ctk C p t 1 J‖ ≤ Real.rpow (Q p) ((t : ℝ) + 1 / 2) := by
  have hpos : 0 < Q p := by
    change 0 < (Ideal.absNorm (primeIdeal p).val : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => (primeIdeal p).property.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  rw [Ctk_one C p t J ht]
  split_ifs with hJ
  · rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    calc
      _ ≤ Real.sqrt (Q p) * Q p ^ (t - 1) * Q p := by
        apply mul_le_mul _ (norm_T_le_test C p _ _) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (tau_norm_le C p) (pow_nonneg hpos.le _)
      _ = Real.rpow (Q p) ((t : ℝ) + 1 / 2) := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel ht, Real.sqrt_eq_rpow,
          ← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        ring
  · simp only [norm_zero]
    exact Real.rpow_nonneg hpos.le _

end DedekindZetaZeroFree.LocalFiniteSums

end

end
