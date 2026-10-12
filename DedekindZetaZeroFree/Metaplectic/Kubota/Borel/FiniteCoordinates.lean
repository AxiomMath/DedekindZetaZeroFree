module

public import DedekindZetaZeroFree.Theta.Periods.Wild.FiniteJointKernel

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly
open MomentSources KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η}
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem raw_borel_lower10 (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : rawGlobal (R := R) a ∈ KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12)
    (p : KPHilbert.Place F) : (a p).g 1 0 = 0 := by
  obtain ⟨A, hA, h10⟩ := ha
  let M := restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 a
  change QuotientGroup.mk' (scalarSubgroup F) A = QuotientGroup.mk' (scalarSubgroup F) M at hA
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hA
  have hM : M = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = A⁻¹ * M at hz
    rw [hz]
    group
  have hm : M 1 0 = 0 := by
    rw [hM]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar, h10]
  have hh := congrArg (adeleEval F p) hm
  cases p with
  | inl w => exact hh
  | inr q => exact hh

theorem raw_borel_finite (a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12)
    (ha : rawGlobal (R := R) a ∈ KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12)
    (q : KPFinitePlace F) :
    KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (a (Sum.inr q)) ∈
      KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q := by
  refine ⟨(a (Sum.inr q)).g, ?_, raw_borel_lower10 (R := R) a ha (Sum.inr q)⟩
  rfl

theorem exists_raw_borel (b : KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12) :
    ∃ a : RestrictedCover F R.A.zeta12 R.A.primitive_zeta12,
      rawGlobal (R := R) a = b.val ∧ ∀ q : KPFinitePlace F,
      KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (a (Sum.inr q)) ∈
        KPKirillovGenuineSectionCharts.P F R.A.zeta12 R.A.primitive_zeta12 q := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective b.val
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective g
  have he : rawGlobal (R := R) a = b.val := by
    change QuotientGroup.mk (QuotientGroup.mk a) = b.val
    rw [ha, hg]
  refine ⟨a, he, ?_⟩
  intro q
  exact raw_borel_finite (R := R) a (he.symm ▸ b.property) q
end DedekindZetaZeroFree.FourierContinuation.WildFiniteExteriorAssembly

end
