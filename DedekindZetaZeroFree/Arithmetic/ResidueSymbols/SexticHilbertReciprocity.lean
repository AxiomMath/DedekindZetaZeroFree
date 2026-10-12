module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.Reciprocity

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private theorem coprime_of_residue_unit {R : Type*} [CommRing R]
    (M : Ideal R) (x : R) (hx : IsUnit (Ideal.Quotient.mk M x)) :
    Ideal.span {x} ⊔ M = ⊤ := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ M)
  have hxy : Ideal.Quotient.mk M (x * y - 1) = 0 := by
    simp only [map_sub, map_mul, map_one, hy, ← hu, Units.mul_inv]
    exact sub_self _
  have hmem : x * y - 1 ∈ M := Ideal.Quotient.eq_zero_iff_mem.mp hxy
  apply (Ideal.eq_top_iff_one _).mpr
  have hxmem : x * y ∈ Ideal.span {x} :=
    Ideal.mul_mem_right y _ (Ideal.subset_span (Set.mem_singleton x))
  have hm1 : x * y ∈ Ideal.span {x} ⊔ M :=
    (show Ideal.span {x} ≤ Ideal.span {x} ⊔ M from le_sup_left) hxmem
  have hm2 : x * y - 1 ∈ Ideal.span {x} ⊔ M :=
    (show M ≤ Ideal.span {x} ⊔ M from le_sup_right) hmem
  have := (Ideal.span {x} ⊔ M).sub_mem hm1 hm2
  simpa only [sub_sub_cancel] using this

private theorem extended_sup_ne_top (A : SArithmeticData F) (I J : A.Exterior)
    (h : I.val ⊔ J.val ≠ ⊤) : A.extendIdeal I ⊔ A.extendIdeal J ≠ ⊤ := by
  let K : A.Exterior := ⟨I.val ⊔ J.val, by
    constructor
    · intro he
      have hl : I.val ≤ (⊥ : Ideal (𝓞 F)) := le_sup_left.trans he.le
      exact I.property.1 (le_bot_iff.mp hl)
    · apply top_unique
      exact I.property.2.ge.trans (sup_le_sup_right le_sup_left _)⟩
  have hcon : (A.extendIdeal K).comap (algebraMap (𝓞 F) A.R) ≤ K.val := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply ArithGaussCRT.exteriorQuotientMap_injective A K
    rw [map_zero, Ideal.quotientMap_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  intro he
  have hk : A.extendIdeal K = ⊤ := by
    simpa only [SArithmeticData.extendIdeal, K, Ideal.map_sup] using he
  rw [hk, Ideal.comap_top] at hcon
  exact h (top_unique hcon)

theorem actual_sextic_noncoprime_vanishing (A : SArithmeticData F)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (h : I.val ⊔ J.val ≠ ⊤) :
    A.sexticResidue I b = 0 ∧ A.sexticResidue J a = 0 := by
  have hmap := extended_sup_ne_top A I J h
  constructor
  · apply MulChar.map_nonunit
    intro hunit
    apply hmap
    rw [← hb.2, sup_comm]
    exact coprime_of_residue_unit _ _ hunit
  · apply MulChar.map_nonunit
    intro hunit
    apply hmap
    rw [← ha.2]
    exact coprime_of_residue_unit _ _ hunit

theorem actual_sextic_unit_twisted_of_coprime_law (A : SArithmeticData F)
    (B : Subgroup A.V)
    (hrec : ∀ (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ),
      A.Generates I a → A.Generates J b →
      (ua : F) = (a : F) → (ub : F) = (b : F) →
      A.IsAllowed B ua → A.IsAllowed B ub → I.val ⊔ J.val = ⊤ →
      A.sexticResidue I b = A.sexticResidue J a)
    (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ) (ε : A.U)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (hua : (ua : F) = (a : F)) (hub : (ub : F) = (b : F))
    (hBa : A.IsAllowed B ua) (hBb : A.IsAllowed B ub) :
    A.sexticResidue I ((A.unitEquiv ε : A.R) * b) =
      A.sexticResidue I (A.unitEquiv ε : A.R) * A.sexticResidue J a := by
  have he : A.sexticResidue I b = A.sexticResidue J a := by
    by_cases hc : I.val ⊔ J.val = ⊤
    · exact hrec I J a b ua ub ha hb hua hub hBa hBb hc
    · obtain ⟨hi, hj⟩ := actual_sextic_noncoprime_vanishing A I J a b ha hb hc
      exact hi.trans hj.symm
  change MulChar.ofUnitHom (A.sexticResidueFamily I)
    (Ideal.Quotient.mk (A.extendIdeal I) ((A.unitEquiv ε : A.R) * b)) = _
  rw [map_mul, map_mul]
  change A.sexticResidue I (A.unitEquiv ε : A.R) * A.sexticResidue I b = _
  rw [he]

theorem actual_hilbert_sextic_reciprocity (A : SArithmeticData F)
    (H : A.V → A.V → Fˣ) (B : Subgroup A.V)
    (hActual : ∀ x y : A.G,
      H (QuotientGroup.mk' A.sixthPowers x) (QuotientGroup.mk' A.sixthPowers y) =
        (A.H_S x y : Fˣ))
    (hB : A.IsSUnitIsotropicComplement H B) :
    A.SexticReciprocitySpec B H := by
  have hrec : ∀ (I J : A.Exterior) (a b : A.R) (ua ub : Fˣ),
      A.Generates I a → A.Generates J b →
      (ua : F) = (a : F) → (ub : F) = (b : F) →
      A.IsAllowed B ua → A.IsAllowed B ub → I.val ⊔ J.val = ⊤ →
      A.sexticResidue I b = A.sexticResidue J a := by
    intro I J a b ua ub ha hb hua hub hBa hBb hc
    have hH : (A.H_S (A.diagonal ua) (A.diagonal ub) : Fˣ) = 1 := by
      rw [← hActual]
      exact hB.2.1 (A.sClass ua) hBa (A.sClass ub) hBb
    have hr := actual_sextic_coprime_reciprocity A I J a b ua ub ha hb hua hub hc
    simpa only [Subgroup.coe_inv, hH, inv_one, Units.val_one, one_mul] using hr
  refine ⟨hrec, ?_, ?_, actual_sextic_noncoprime_vanishing A⟩
  · intro I a ua ε ha hua _
    rw [actual_sextic_sunit_symbol A I a ua ε ha hua]
    exact congrArg (fun u : Fˣ => (u : F)) (hActual (A.diagonal ε.val) (A.diagonal ua)).symm
  · exact actual_sextic_unit_twisted_of_coprime_law A B hrec

end
end DedekindZetaZeroFree.ArithmeticContext
