module

public import DedekindZetaZeroFree.RepresentationTheory.FiniteAbelian.RegularCharacterEulerPolynomial

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped BigOperators Classical

theorem inertiaCharacterDeterminant
    {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G) (g : G) (x : ℂ) :
    let f := orderOf ((QuotientGroup.mk' H) g)
    ∏ ρ : ComplexDual G, (1 - (if H ≤ ρ.ker then (ρ g : ℂ) else 0) * x) =
      (1 - x ^ f) ^ (Nat.card (G ⧸ H) / f) := by
  dsimp only
  classical

  let e1 : {ρ : ComplexDual G // H ≤ ρ.ker} ≃ (MonoidHom.domRestrictHom H ℂˣ).ker :=
    { toFun := fun ρ => ⟨ρ.val, by
        rw [MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply, MonoidHom.domRestrict_eq_one_iff]
        intro y hy; exact ρ.property hy⟩
      invFun := fun ρ => ⟨ρ.val, by
        intro y hy
        have h := ρ.property
        rw [MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply, MonoidHom.domRestrict_eq_one_iff] at h
        exact h y hy⟩
      left_inv := fun ρ => rfl
      right_inv := fun ρ => rfl }
  let e : {ρ : ComplexDual G // H ≤ ρ.ker} ≃ ComplexDual (G ⧸ H) :=
    e1.trans (MonoidHom.domRestrictHomKerEquiv ℂˣ H).toEquiv

  have heval : ∀ (ρ : {ρ : ComplexDual G // H ≤ ρ.ker}),
      (e ρ) ((QuotientGroup.mk' H) g) = ρ.val g := by
    intro ρ
    change (MonoidHom.domRestrictHomKerEquiv ℂˣ H (e1 ρ)) (g : G ⧸ H) = ρ.val g
    rw [MonoidHom.domRestrictHomKerEquiv_apply_coe]
    rfl

  have hprod : (∏ ρ : ComplexDual G, (1 - (if H ≤ ρ.ker then (ρ g : ℂ) else 0) * x))
      = ∏ ρ : {ρ : ComplexDual G // H ≤ ρ.ker}, (1 - (ρ.val g : ℂ) * x) := by
    refine Finset.prod_congr_set {ρ : ComplexDual G | H ≤ ρ.ker}
      (fun ρ : ComplexDual G => (1 - (if H ≤ ρ.ker then (ρ g : ℂ) else 0) * x))
      (fun ρ : {ρ : ComplexDual G // H ≤ ρ.ker} => (1 - (ρ.val g : ℂ) * x)) ?_ ?_
    · intro ρ hρ
      by_cases hp : H ≤ ρ.ker
      · rw [if_pos hp]
      · exact absurd (show H ≤ ρ.ker from hρ) hp
    · intro ρ hρ
      by_cases hp : H ≤ ρ.ker
      · exact absurd hp (show ¬ (H ≤ ρ.ker) from hρ)
      · rw [if_neg hp]; ring
  rw [hprod]
  have hstep : (∏ ρ : {ρ : ComplexDual G // H ≤ ρ.ker}, (1 - (ρ.val g : ℂ) * x))
      = ∏ τ : ComplexDual (G ⧸ H), (1 - (τ ((QuotientGroup.mk' H) g) : ℂ) * x) := by
    rw [← Equiv.prod_comp e (fun τ : ComplexDual (G ⧸ H) =>
        1 - (τ ((QuotientGroup.mk' H) g) : ℂ) * x)]
    apply Finset.prod_congr rfl
    intro ρ _
    rw [heval]
  rw [hstep]
  exact regularCharacterDeterminant ((QuotientGroup.mk' H) g) x

end DedekindZetaZeroFree.AbelianQuotient
