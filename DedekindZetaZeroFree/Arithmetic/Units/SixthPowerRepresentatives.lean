module

public import DedekindZetaZeroFree.Moments.Reflected.BalancedDyadicRowTransfer
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitStructureAndLogarithmicRank

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinGrowth

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem exists_sixth_unit_representatives (A : SArithmeticData F) :
    ∃ U : Finset A.Rˣ, ActualRowTransfer.UnitRepresentatives A U := by

  haveI : Group.FG A.Rˣ := (isMulFG_congr A.unitStructure).mpr inferInstance

  let H : Subgroup A.Rˣ := (powMonoidHom (α := A.Rˣ) 6).range
  have hfin : H.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg A.Rˣ (by norm_num)
  haveI : Finite (A.Rˣ ⧸ H) := Subgroup.finiteIndex_iff_finite_quotient.mp hfin
  letI : Fintype (A.Rˣ ⧸ H) := Fintype.ofFinite _

  refine ⟨Finset.univ.image (fun q : A.Rˣ ⧸ H => Quotient.out q), ?_⟩
  intro v
  refine ⟨⟨Quotient.out (Quotient.mk'' v), Finset.mem_image.mpr
      ⟨Quotient.mk'' v, Finset.mem_univ _, rfl⟩⟩, ?_, ?_⟩
  ·
    have hrel : (QuotientGroup.leftRel H) (Quotient.out (Quotient.mk'' v)) v :=
      Quotient.mk_out v
    rw [QuotientGroup.leftRel_apply] at hrel
    obtain ⟨w, hw⟩ := hrel
    refine ⟨w, ?_⟩
    rw [powMonoidHom_apply] at hw
    rw [hw]; group
  ·
    rintro ⟨u, hu⟩ ⟨w, hw⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨q, rfl⟩ := hu
    apply Subtype.ext
    have hw' : v = Quotient.out q * w ^ 6 := hw
    have hw6 : (Quotient.out q)⁻¹ * v = w ^ 6 := by rw [hw']; group
    have hrel : (QuotientGroup.leftRel H) (Quotient.out q) v := by
      rw [QuotientGroup.leftRel_apply]
      exact ⟨w, by rw [powMonoidHom_apply]; exact hw6.symm⟩
    have h1 : q = Quotient.mk'' v := (Quotient.out_eq q).symm.trans (Quotient.sound hrel)
    exact congrArg Quotient.out h1

end DedekindZetaZeroFree.PrincipalMellinGrowth
