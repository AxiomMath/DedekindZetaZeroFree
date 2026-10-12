module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LocalFiniteSums
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem Ctk_zero_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (J : ℕ) :
    Ctk C p 0 0 J = 1 := by
  classical
  have hI : Ideal.span ({generator C p ^ 0} : Set A.R) = ⊤ := by simp
  letI : Subsingleton (Residue C p 0) := by
    change Subsingleton (A.R ⧸ Ideal.span {generator C p ^ 0})
    rw [hI]
    infer_instance
  have hz (x : Residue C p 0) : x = 0 := Subsingleton.elim _ _
  letI : Unique (Residue C p 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  simp [Ctk, maskedPower, psi, hz, Fintype.card_unique]

theorem Ctk_zero_pos (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (k J : ℕ) (hk : 0 < k) :
    Ctk C p 0 k J = if J = 0 then 1 else 0 := by
  classical
  letI : Subsingleton (Residue C p 0) := by
    change Subsingleton (A.R ⧸ Ideal.span {generator C p ^ 0})
    simp only [pow_zero, Ideal.span_singleton_one]
    infer_instance
  letI : Unique (Residue C p 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have hz (x : Residue C p 0) : x = 0 := Subsingleton.elim _ _
  have hphase (v : Residue C p 0) :
      psi C p k (residueMap C p k
        ((generator C p ^ J - (lifts C p k).val (residueMap C p k (generator C p ^ J))) *
          (lifts C p 0).val v)) = 1 := by
    have hl := (lifts C p k).property (residueMap C p k (generator C p ^ J))
    change residueMap C p k _ = _ at hl
    simp only [map_mul, map_sub, hl, sub_self, zero_mul, psi,
      AddChar.map_zero_eq_one]
    rfl
  simp only [Ctk, pow_zero, map_one, one_mul, Nat.add_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, hphase, maskedPower, dif_pos rfl,
    one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul, mul_one]
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  simp only [hk0, dif_neg, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_smul, mul_one]
  by_cases hJ : J = 0
  · subst J
    simp
  · have hI : A.extendIdeal (primeIdeal p) ≠ ⊤ :=
      A.residue_extendIdeal_ne_top (primeIdeal p) p.val.isPrime.ne_top
    letI : Nontrivial (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
      Ideal.Quotient.nontrivial_iff.mpr hI
    have hg : reduction C p k hk0 (residueMap C p k (generator C p)) = 0 := by
      change Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← (generator_generates C p).2]
      exact Ideal.subset_span (by simp)
    have hnu : ¬ IsUnit (residueMap C p k (generator C p ^ J)) := by
      intro hu
      have hu' := hu.map (reduction C p k hk0)
      have hz' : reduction C p k hk0 (residueMap C p k (generator C p ^ J)) = 0 := by
        rw [map_pow, map_pow, hg, zero_pow hJ]
      rw [hz'] at hu'
      exact not_isUnit_zero hu'
    simp only [hnu, hJ]
    simp

private lemma cast_trace_character {R : Type*} [CommRing R]
    (I K : Ideal R) (h : I = K) (χ : AddChar (R ⧸ I) Circle) (x : R) :
    (cast (congrArg (fun I : Ideal R => AddChar (R ⧸ I) Circle) h) χ)
      (Ideal.Quotient.mk K x) = χ (Ideal.Quotient.mk I x) := by
  cases h
  rfl

theorem psi_residueMap (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    psi C p n (residueMap C p n x) =
      (A.fieldTraceCharacter ((x : F) / (generator C p ^ n : A.R)) : ℂ) := by
  unfold psi quotientTrace
  generalize_proofs h1 h2 hc heq
  have hcast := cast_trace_character (A.extendIdeal (powerIdeal p n))
    (Ideal.span {generator C p ^ n}) hc.2.symm
    (A.residueTraceCharacter hS (powerIdeal p n) (generator C p ^ n) hc) x
  change ((cast heq (A.residueTraceCharacter hS (powerIdeal p n)
    (generator C p ^ n) hc))
    (Ideal.Quotient.mk (Ideal.span {generator C p ^ n}) x) : ℂ) = _
  rw [hcast, A.residueTraceCharacter_apply]

theorem quotientTrace_isPrimitive (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) : (quotientTrace C p n).IsPrimitive := by
  intro x hx heq
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hgen : A.Generates (powerIdeal p n) (generator C p ^ n) := by
    refine ⟨pow_ne_zero _ (generator_generates C p).1, ?_⟩
    rw [← Ideal.span_singleton_pow, (generator_generates C p).2]
    exact (Ideal.map_pow _ _ _).symm
  have hxI : x ∉ A.extendIdeal (powerIdeal p n) := by
    rw [← hgen.2]
    exact fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  obtain ⟨y, hy⟩ := ResidueTraceFactorProductFormula.principalResidue_separation
    ResidueTrace.baseEmbedding
    (fun v => (ResidueTrace.baseEmbedding_spec v).1)
    (fun v => (ResidueTrace.baseEmbedding_spec v).2) A hS
    (powerIdeal p n) (generator C p ^ n) hgen x hxI
  have h := congrArg (fun χ : AddChar (Residue C p n) Circle =>
    χ (residueMap C p n y)) heq
  rw [AddChar.mulShift_apply] at h
  have hcomplex := congrArg (fun z : Circle => (z : ℂ)) h
  change psi C p n (residueMap C p n x * residueMap C p n y) = 1 at hcomplex
  rw [← map_mul, psi_residueMap] at hcomplex
  have hone : A.fieldTraceCharacter ((x : F) * (y : F) /
      (generator C p ^ n : A.R)) = 1 := by
    apply Subtype.ext
    exact hcomplex
  apply hy
  change A.fieldTraceCharacter ((x : F) * (y : F) /
      (generator C p ^ n : A.R)) = 1
  exact hone

theorem psi_sum_mul (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (b : Residue C p n) :
    (∑ x : Residue C p n, psi C p n (x * b)) =
      if b = 0 then (Fintype.card (Residue C p n) : ℂ) else 0 := by
  classical
  let χ : AddChar (Residue C p n) ℂ :=
    Circle.coeHom.compAddChar (quotientTrace C p n)
  have hp : χ.IsPrimitive := by
    intro b hb h
    apply quotientTrace_isPrimitive C p n hb
    ext x
    exact congrArg (fun f : AddChar (Residue C p n) ℂ => f x) h
  have hh := AddChar.sum_mulShift b hp
  change (∑ x, psi C p n (x * b)) =
    (↑(if b = 0 then Fintype.card (Residue C p n) else 0) : ℂ) at hh
  simpa only [Nat.cast_ite, Nat.cast_zero] using hh

theorem Ctk_kzero_sum (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) :
    Ctk C p t 0 J =
      ∑ v : Residue C p t, maskedPower C p t t v *
        psi C p t (residueMap C p t (generator C p ^ J) * v) := by
  classical
  letI : Subsingleton (Residue C p 0) := by
    change Subsingleton (A.R ⧸ Ideal.span {generator C p ^ 0})
    simp only [pow_zero, Ideal.span_singleton_one]
    infer_instance
  letI : Unique (Residue C p 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  have hpow : residueMap C p t (generator C p ^ t) = 0 := by
    change Ideal.Quotient.mk (Ideal.span {generator C p ^ t}) _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hl (v : Residue C p t) : residueMap C p t ((lifts C p t).val v) = v :=
    (lifts C p t).property v
  unfold Ctk
  simp only [Nat.zero_add, Nat.cast_zero]
  rw [Fintype.sum_unique]
  have hm : maskedPower C p 0 (0 : ℤ) default = 1 := by
    simp [maskedPower]
  rw [hm, one_mul]
  have hcond : residueMap C p 0 (generator C p ^ J) =
      residueMap C p 0 (generator C p ^ t) * default := Subsingleton.elim _ _
  rw [if_pos hcond]
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  · omega
  · rw [Nat.zero_add]
    apply heq_of_eq
    simp only [map_mul, map_sub, hpow, zero_mul, sub_zero, hl]

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
private theorem Ctk_succ_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n J : ℕ) :
    Ctk C p (n+1) 0 J =
      if n ≤ J then (Q p : ℂ) ^ n *
        T C p (n+1 : ℕ) (residueMap C p 1 (generator C p ^ (J-n))) else 0 := by
  rw [Ctk_kzero_sum]
  rw [← Fintype.sum_bijective (fiberMap C p n) (fiberMap_bijective C p n)
    (fun z => maskedPower C p (n+1) (n+1 : ℕ) (fiberMap C p n z) *
      psi C p (n+1) (residueMap C p (n+1) (generator C p ^ J) * fiberMap C p n z))
    (fun v => maskedPower C p (n+1) (n+1 : ℕ) v *
      psi C p (n+1) (residueMap C p (n+1) (generator C p ^ J) * v)) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp_rw [fiber_mask, fiber_phase, ← mul_assoc, ← Finset.mul_sum]
  have hs : (∑ y : Residue C p n, psi C p n (residueMap C p n (generator C p ^ J) * y)) =
      if n ≤ J then (Fintype.card (Residue C p n) : ℂ) else 0 := by
    simp_rw [mul_comm]
    rw [psi_sum_mul, residue_pow_zero]
    split_ifs <;> rfl
  simp_rw [hs]
  by_cases hJ : n ≤ J
  · simp only [hJ, if_true]
    simp_rw [phase_descend C p n J hJ]
    rw [residue_card]
    unfold T
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp [hJ]

theorem Ctk_pos_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (t J : ℕ) (ht : 0 < t) :
    Ctk C p t 0 J =
      if t - 1 ≤ J then
        (Q p : ℂ) ^ (t - 1) *
          T C p (t : ℤ) (residueMap C p 1 (generator C p ^ (J - (t - 1))))
      else 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using Ctk_succ_zero C p n J

end DedekindZetaZeroFree.LocalFiniteSums
