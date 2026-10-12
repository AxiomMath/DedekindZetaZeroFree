module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.PrimeHilbertPerfectPairing
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SixthPowerChineseRemainder

@[expose] public section

open scoped NumberField Classical
namespace DedekindZetaZeroFree.SArithmeticData
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]

def VnLocalEquiv (A : SArithmeticData F) (n : ℕ) :
    Vn F A n ≃* A.LocalPowerClasses n where
  toFun x := (fun w => x (Sum.inl w), fun v => x (Sum.inr v))
  invFun x v := match v with
    | Sum.inl w => x.1 w
    | Sum.inr w => x.2 w
  left_inv := by intro x; funext v; cases v <;> rfl
  right_inv := by intro x; rfl
  map_mul' := by intro x y; rfl

def VnSixthCRT (A : SArithmeticData F) : A.V ≃* Vn F A 2 × Vn F A 3 :=
  A.localSixthPowerCRT.trans
    ((A.VnLocalEquiv 2).symm.prodCongr (A.VnLocalEquiv 3).symm)

def VnSixthEquiv (A : SArithmeticData F) : A.V ≃* Vn F A 6 :=
  (A.localPowerQuotientEquiv 6).trans (A.VnLocalEquiv 6).symm

def H_S6 (A : SArithmeticData F) : A.V →* A.V →* rootsOfUnity 6 F where
  toFun x := (A.H_Sn 6 (Or.inr (Or.inr rfl)) (A.VnSixthEquiv x)).comp
    A.VnSixthEquiv.toMonoidHom
  map_one' := by
    apply MonoidHom.ext
    intro y
    change A.H_Sn 6 (Or.inr (Or.inr rfl)) (A.VnSixthEquiv 1) (A.VnSixthEquiv y) = 1
    rw [map_one, map_one, MonoidHom.one_apply]
  map_mul' := by
    intro x z
    apply MonoidHom.ext
    intro y
    change A.H_Sn 6 (Or.inr (Or.inr rfl)) (A.VnSixthEquiv (x * z))
      (A.VnSixthEquiv y) = _
    rw [map_mul, H_Sn_mul_left]
    rfl

theorem H_S6_on_representatives (A : SArithmeticData F) (x y : A.G) :
    A.H_S6 (QuotientGroup.mk' A.sixthPowers x)
      (QuotientGroup.mk' A.sixthPowers y) = A.H_S x y := by
  rfl

theorem H_S6_cube_eq_quadratic (A : SArithmeticData F) (x y : A.V) :
    (A.H_S6 x y : Fˣ) ^ 3 =
      (A.H_Sn 2 (Or.inl rfl) (A.VnSixthCRT x).1 (A.VnSixthCRT y).1 : Fˣ) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change (A.H_S6 (QuotientGroup.mk' A.sixthPowers x)
    (QuotientGroup.mk' A.sixthPowers y) : Fˣ) ^ 3 = _
  rw [H_S6_on_representatives]
  change (A.H_S x y : Fˣ) ^ 3 =
    (A.H_Sn 2 (Or.inl rfl)
      ((A.VnLocalEquiv 2).symm (A.localSixthPowerCRT (QuotientGroup.mk' A.sixthPowers x)).1)
      ((A.VnLocalEquiv 2).symm (A.localSixthPowerCRT (QuotientGroup.mk' A.sixthPowers y)).1) : Fˣ)
  rw [localSixthPowerCRT_apply, localSixthPowerCRT_apply]
  rw [H_Sn_apply]
  unfold H_S
  simp only [SubmonoidClass.coe_finsetProd]
  rw [← Finset.prod_pow]
  change (∏ v : {v // v ∈ A.Sf},
    (A.actualLocalSymbol v.val 6 (Or.inr (Or.inr rfl)) (x.2 v) (y.2 v) : Fˣ) ^ 3) =
    ∏ v : {v // v ∈ A.Sf},
    (A.actualLocalSymbol v.val 2 (Or.inl rfl) (x.2 v) (y.2 v) : Fˣ)
  apply Finset.prod_congr rfl
  intro v hv
  apply Units.ext
  apply (algebraMap F (v.val.adicCompletion F)).injective
  have h := congrArg Units.val (A.actualLocalSymbol_two_six v.val (x.2 v) (y.2 v))
  simpa only [Units.val_pow_eq_pow_val, A.finiteRootsEquiv_apply, map_pow] using h.symm

theorem H_S6_square_eq_cubic (A : SArithmeticData F) (x y : A.V) :
    (A.H_S6 x y : Fˣ) ^ 2 =
      (A.H_Sn 3 (Or.inr (Or.inl rfl)) (A.VnSixthCRT x).2
        (A.VnSixthCRT y).2 : Fˣ) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change (A.H_S6 (QuotientGroup.mk' A.sixthPowers x)
    (QuotientGroup.mk' A.sixthPowers y) : Fˣ) ^ 2 = _
  rw [H_S6_on_representatives]
  change (A.H_S x y : Fˣ) ^ 2 =
    (A.H_Sn 3 (Or.inr (Or.inl rfl))
      ((A.VnLocalEquiv 3).symm (A.localSixthPowerCRT (QuotientGroup.mk' A.sixthPowers x)).2)
      ((A.VnLocalEquiv 3).symm (A.localSixthPowerCRT (QuotientGroup.mk' A.sixthPowers y)).2) : Fˣ)
  rw [localSixthPowerCRT_apply, localSixthPowerCRT_apply]
  rw [H_Sn_apply]
  unfold H_S
  simp only [SubmonoidClass.coe_finsetProd]
  rw [← Finset.prod_pow]
  change (∏ v : {v // v ∈ A.Sf},
    (A.actualLocalSymbol v.val 6 (Or.inr (Or.inr rfl)) (x.2 v) (y.2 v) : Fˣ) ^ 2) =
    ∏ v : {v // v ∈ A.Sf},
    (A.actualLocalSymbol v.val 3 (Or.inr (Or.inl rfl)) (x.2 v) (y.2 v) : Fˣ)
  apply Finset.prod_congr rfl
  intro v hv
  apply Units.ext
  apply (algebraMap F (v.val.adicCompletion F)).injective
  have h := congrArg Units.val (A.actualLocalSymbol_three_six v.val (x.2 v) (y.2 v))
  simpa only [Units.val_pow_eq_pow_val, A.finiteRootsEquiv_apply, map_pow] using h.symm

def hilbertRootsSixthCRT : rootsOfUnity 6 F ≃*
    rootsOfUnity 2 F × rootsOfUnity 3 F where
  toFun z :=
    (⟨z.val ^ 3, by
      apply (mem_rootsOfUnity 2 _).2
      rw [← pow_mul]
      exact (mem_rootsOfUnity 6 z.val).1 z.property⟩,
     ⟨z.val ^ 2, by
      apply (mem_rootsOfUnity 3 _).2
      rw [← pow_mul]
      exact (mem_rootsOfUnity 6 z.val).1 z.property⟩)
  invFun z := ⟨z.1.val * z.2.val⁻¹, by
    apply (mem_rootsOfUnity 6 _).2
    have h2 := (mem_rootsOfUnity 2 z.1.val).1 z.1.property
    have h3 := (mem_rootsOfUnity 3 z.2.val).1 z.2.property
    rw [mul_pow, inv_pow, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2,
      one_pow, show (2 * 3 : ℕ) = 3 * 2 from rfl, pow_mul, h3]
    simp⟩
  left_inv := by
    intro z
    apply Subtype.ext
    change z.val ^ 3 * (z.val ^ 2)⁻¹ = z.val
    group
  right_inv := by
    intro z
    have h2 := (mem_rootsOfUnity 2 z.1.val).1 z.1.property
    have h3 := (mem_rootsOfUnity 3 z.2.val).1 z.2.property
    apply Prod.ext <;> apply Subtype.ext
    · change (z.1.val * z.2.val⁻¹) ^ 3 = z.1.val
      rw [mul_pow, inv_pow, h3, inv_one, mul_one, pow_succ, h2, one_mul]
    · change (z.1.val * z.2.val⁻¹) ^ 2 = z.2.val
      rw [mul_pow, h2, one_mul]
      have h : z.2.val ^ 2 * z.2.val = 1 := by rw [← pow_succ, h3]
      rw [inv_pow]
      exact inv_eq_of_mul_eq_one_right h
  map_mul' := by
    intro x y
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_pow]

theorem H_S6_coefficientCRT (A : SArithmeticData F) (x y : A.V) :
    hilbertRootsSixthCRT (A.H_S6 x y) =
      (A.H_Sn 2 (Or.inl rfl) (A.VnSixthCRT x).1 (A.VnSixthCRT y).1,
       A.H_Sn 3 (Or.inr (Or.inl rfl)) (A.VnSixthCRT x).2 (A.VnSixthCRT y).2) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact A.H_S6_cube_eq_quadratic x y
  · exact A.H_S6_square_eq_cubic x y

theorem V_finite (A : SArithmeticData F) : Finite A.V := by
  haveI (v : A.Place) : Finite (PowerQuotient (A.Completion v)ˣ 6) := by
    cases v with
    | inl w =>
      letI := A.infinite_power_quotient_subsingleton w 6 (Or.inr (Or.inr rfl))
      infer_instance
    | inr v =>
      letI : ValuativeRel (v.val.adicCompletion F) :=
        ClassFieldTheory.finitePlaceCompletionValuativeRel F v.val
      letI : IsNonarchimedeanLocalField (v.val.adicCompletion F) :=
        ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v.val
      exact ClassFieldTheory.powerClassGroup_finite _ 6
        (A.finite_natCast_ne_zero v.val 6 (Or.inr (Or.inr rfl)))
  exact Finite.of_equiv (Vn F A 6) A.VnSixthEquiv.toEquiv.symm

theorem H_S6_alternating (A : SArithmeticData F) (x : A.V) : A.H_S6 x x = 1 := by
  apply hilbertRootsSixthCRT.injective
  rw [H_S6_coefficientCRT, map_one]
  apply Prod.ext
  · exact A.H_Sn_alternating 2 (Or.inl rfl) _
  · exact A.H_Sn_alternating 3 (Or.inr rfl) _

theorem H_S6_perfect (A : SArithmeticData F) : Function.Bijective A.H_S6 := by
  letI := A.V_finite
  have hinj : Function.Injective A.H_S6 := by
    intro x y hxy
    apply A.VnSixthCRT.injective
    apply Prod.ext
    · apply (A.H_Sn_perfect 2 (Or.inl rfl)).1
      apply MonoidHom.ext
      intro z
      have h := congrArg (fun f => (hilbertRootsSixthCRT
        (f (A.VnSixthCRT.symm (z, 1)))).1) hxy
      simpa only [H_S6_coefficientCRT, MulEquiv.apply_symm_apply] using h
    · apply (A.H_Sn_perfect 3 (Or.inr rfl)).1
      apply MonoidHom.ext
      intro z
      have h := congrArg (fun f => (hilbertRootsSixthCRT
        (f (A.VnSixthCRT.symm (1, z)))).2) hxy
      simpa only [H_S6_coefficientCRT, MulEquiv.apply_symm_apply] using h
  letI : HasEnoughRootsOfUnity F 6 :=
    { prim := ⟨_, A.primitive_root 6 (Or.inr (Or.inr rfl))⟩
      cyc := inferInstance }
  have hexp : Monoid.exponent A.V ∣ 6 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (powerQuotient_pow_eq_one A.G 6)
  letI : HasEnoughRootsOfUnity F (Monoid.exponent A.V) :=
    HasEnoughRootsOfUnity.of_dvd F hexp
  let e : (A.V →* rootsOfUnity 6 F) ≃ (A.V →* Fˣ) :=
    { toFun := fun f => (rootsOfUnity 6 F).subtype.comp f
      invFun := fun f => f.codRestrict (rootsOfUnity 6 F) (by
        intro a
        apply (mem_rootsOfUnity 6 _).2
        rw [← map_pow, powerQuotient_pow_eq_one A.G 6, map_one])
      left_inv := by intro f; ext a; rfl
      right_inv := by intro f; ext a; rfl }
  have hcard : Nat.card A.V = Nat.card (A.V →* rootsOfUnity 6 F) := by
    calc
      Nat.card A.V = Nat.card (A.V →* Fˣ) :=
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A.V F).symm
      _ = Nat.card (A.V →* rootsOfUnity 6 F) := (Nat.card_congr e).symm
  letI : Finite (A.V →* rootsOfUnity 6 F) :=
    Nat.finite_of_card_ne_zero (by
      rw [← hcard]
      exact (Nat.card_pos (α := A.V)).ne')
  exact (Nat.bijective_iff_injective_and_card A.H_S6).2 ⟨hinj, hcard⟩

end
end DedekindZetaZeroFree.SArithmeticData
