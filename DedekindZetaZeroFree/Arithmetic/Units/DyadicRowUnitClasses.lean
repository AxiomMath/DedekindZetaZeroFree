module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitExtractionDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField ThetaExpansion.SignedExpansion
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

lemma allowed_unit_mem_gamma (e : R.A.U)
    (he : ThetaReflectionData.rationalClass R.A e.val ∈ R.probe.allowed.B) :
    e.val ∈ ThetaReflectionData.rationalGamma R.A := by
  have hE : ThetaReflectionData.rationalClass R.A e.val ∈ R.A.E :=
    ⟨R.A.diagonal e.val, ⟨e.val, e.property, rfl⟩, rfl⟩
  have hker : e.val ∈ (ThetaReflectionData.rationalClass R.A).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Subgroup.mem_bot.mp
    rw [← R.probe.allowed.complement.disjoint.eq_bot]
    exact ⟨hE, he⟩
  rw [← R.probe.allowed.unit_kernel]
  exact ⟨e.property, hker⟩

theorem dyadicRow_companion (u : R.A.Rˣ) (h d : R.A.Exterior)
    (D : ThetaBranch.RowFactorization R.A R.probe.allowed
      (ActualRowTransfer.dyadicRow R.A R.probe.coefficients u h d)) :
    QuotientGroup.mk D.epsilon = rowClass R u := by
  let e : R.A.U := D.epsilon / R.A.unitEquiv.symm u
  have heq : e.val = R.probe.allowed.generator h * R.probe.allowed.generator d /
      R.probe.allowed.generator D.rowIdeal := by
    apply Units.ext
    have hr := congrArg Units.val D.row_eq
    change (((u : R.A.R) * R.probe.coefficients.generator h *
      R.probe.coefficients.generator d : R.A.R) : F) =
      (D.epsilon.val : F) * (R.probe.allowed.generator D.rowIdeal : F) at hr
    have hrF := hr
    have hu : ((R.A.unitEquiv.symm u).val : F) = ((u : R.A.R) : F) := by
      simp [SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    change ((D.epsilon.val / (R.A.unitEquiv.symm u).val : Fˣ) : F) = _
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    rw [hu, R.probe.sameGenerator h, R.probe.sameGenerator d,
      R.probe.sameGenerator D.rowIdeal]
    have hu0 : ((u : R.A.R) : F) ≠ 0 := by exact_mod_cast u.ne_zero
    have ha0 := (R.probe.allowed.generator D.rowIdeal).ne_zero
    push_cast at hrF
    rw [R.probe.sameGenerator D.rowIdeal] at hrF
    have hg0 : ((R.probe.coefficients.generator D.rowIdeal : R.A.R) : F) ≠ 0 := by
      rw [← R.probe.sameGenerator]; exact ha0
    field_simp
    linear_combination -hrF
  have heB : ThetaReflectionData.rationalClass R.A e.val ∈ R.probe.allowed.B := by
    rw [heq, map_div, map_mul]
    exact R.probe.allowed.B.div_mem
      (R.probe.allowed.B.mul_mem (R.probe.allowed.allowed h) (R.probe.allowed.allowed d))
      (R.probe.allowed.allowed D.rowIdeal)
  have heΓ := allowed_unit_mem_gamma R e heB
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp heΓ
  have heU : e ∈ R.A.unitSixthPowers := by
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  have hclass : (QuotientGroup.mk e : R.A.UnitQuotient) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr heU
  change (QuotientGroup.mk D.epsilon : R.A.UnitQuotient) =
    QuotientGroup.mk (R.A.unitEquiv.symm u)
  change QuotientGroup.mk' _ (D.epsilon / R.A.unitEquiv.symm u) = 1 at hclass
  rw [map_div] at hclass
  exact div_eq_one.mp hclass

end DedekindZetaZeroFree.OrbitExpansion

end
