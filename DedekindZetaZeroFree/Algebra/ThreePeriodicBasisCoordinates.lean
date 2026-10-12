module

public import DedekindZetaZeroFree.Theta.Whittaker.CubicShellVectorIdentities

@[expose] public section

namespace DedekindZetaZeroFree.KPExteriorSpherical
noncomputable section
set_option autoImplicit false

theorem periodic_basis_coordinate_equiv
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℤ → V) (hperiod : ∀ j, c (j + 3) = c j)
    (hbasis : ∃ B : Module.Basis (Fin 3) ℂ V, ∀ i : Fin 3, B i = c (i.val : ℤ)) :
    ∃! E : (Fin 3 → ℂ) ≃ₗ[ℂ] V, ∀ j : ℤ, E (KPThreeShell.basis j) = c j := by
  classical
  obtain ⟨B, hB⟩ := hbasis
  have hstd (i : Fin 3) : KPThreeShell.basis (i.val : ℤ) = Pi.basisFun ℂ (Fin 3) i := by
    ext k
    have hm : (i.val : ℤ) % 3 = i.val := by omega
    simp [KPThreeShell.basis, Pi.basisFun_apply, hm, Pi.single_apply,
      Fin.ext_iff, eq_comm]
  have hcoord (i : Fin 3) :
      B.equivFun.symm (KPThreeShell.basis (i.val : ℤ)) = B i := by
    apply B.equivFun.injective
    rw [B.equivFun.apply_symm_apply]
    ext k
    have hm : (i.val : ℤ) % 3 = i.val := by omega
    simp only [KPThreeShell.basis, hm, Int.toNat_natCast,
      Module.Basis.equivFun_self]
    simp only [Fin.ext_iff, eq_comm]
  refine ⟨B.equivFun.symm, ?_, ?_⟩
  · intro j
    let i : Fin 3 := ⟨(j % 3).toNat, by omega⟩
    have hi : (i.val : ℤ) = j % 3 := by dsimp [i]; omega
    have hb : KPThreeShell.basis j = KPThreeShell.basis (i.val : ℤ) := by
      rw [hi]
      unfold KPThreeShell.basis
      rw [Int.emod_emod]
    have hc : c (i.val : ℤ) = c j := by
      rw [hi]
      have hp : Function.Periodic c 3 := hperiod
      simpa only [Int.cast_id, show j - j / 3 * 3 = j % 3 by omega] using
        hp.sub_int_mul_eq (j / 3) (x := j)
    rw [hb, hcoord, hB, hc]
  · intro E hE
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun ℂ (Fin 3)).ext
    intro i
    change E (Pi.basisFun ℂ (Fin 3) i) = B.equivFun.symm (Pi.basisFun ℂ (Fin 3) i)
    rw [← hstd, hE, hcoord, hB]
end
end DedekindZetaZeroFree.KPExteriorSpherical
