module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.TransitionsAndCoordinateDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularFixedRadiusDomainSource
open KPMsActualAngularSource KPMsActualAngularDomainSource KPMsActualAngularDescentSource
open KPGlobalTorusBorelTwistCompatibility
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem root_zero : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
  (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one

private theorem rational_borel_mul (y z : Fˣ) (x v : KPGlobalTorusFunctionData.Adeles F) :
    ((KPGlobalTorusFunctionData.s F ζ hζ z).val * KPGlobalTorusFunctionData.N F ζ hζ v) *
      ((KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ x) =
      (KPGlobalTorusFunctionData.s F ζ hζ (z*y)).val *
        KPGlobalTorusFunctionData.N F ζ hζ
          ((KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y)⁻¹ :
            KPGlobalTorusFunctionData.Adeles F) * v + x) := by
  have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ
    (KPGlobalTorusFunctionData.s F ζ hζ y)⁻¹ v
  rw [KPGlobalTorusFunctionData.N_add, ← hn, map_mul]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  group

private theorem angular_relation_trans (D : KPMsActualAngularSource.Iwasawa F ζ hζ) (U : KPMsActualAngularSource.Level F ζ hζ)
    (a b c : KPMsActualAngularSource.NormOne F ζ hζ D)
    (hab : KPMsActualAngularSource.angularRelation F ζ hζ D U a b)
    (hbc : KPMsActualAngularSource.angularRelation F ζ hζ D U b c) :
    KPMsActualAngularSource.angularRelation F ζ hζ D U a c := by
  obtain ⟨y,x,u,he⟩ := hab
  obtain ⟨z,v,w,hf⟩ := hbc
  refine ⟨z*y, (KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y)⁻¹ :
      KPGlobalTorusFunctionData.Adeles F) * v + x, u*w, ?_⟩
  rw [hf,he]
  have hmul := rational_borel_mul (ζ := ζ) (hζ := hζ) y z x v
  simp only [Subgroup.coe_mul]
  rw [← hmul]
  group

private theorem angular_relation_symm (D : KPMsActualAngularSource.Iwasawa F ζ hζ) (U : KPMsActualAngularSource.Level F ζ hζ)
    (a b : KPMsActualAngularSource.NormOne F ζ hζ D) (hab : KPMsActualAngularSource.angularRelation F ζ hζ D U a b) :
    KPMsActualAngularSource.angularRelation F ζ hζ D U b a := by
  obtain ⟨y,x,u,he⟩ := hab
  let v : KPGlobalTorusFunctionData.Adeles F :=
    -(KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y) :
      KPGlobalTorusFunctionData.Adeles F) * x
  have hmul := rational_borel_mul (ζ := ζ) (hζ := hζ) y y⁻¹ x v
  have hprod : (KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ y)⁻¹ :
      KPGlobalTorusFunctionData.Adeles F) * v + x = 0 := by
    dsimp [v]
    simp [map_inv]
  rw [hprod, inv_mul_cancel, map_one, root_zero] at hmul
  simp only [Subgroup.coe_one, one_mul] at hmul
  refine ⟨y⁻¹,v,u⁻¹,?_⟩
  rw [he]
  simp only [Subgroup.coe_inv]
  calc
    _ = (((KPGlobalTorusFunctionData.s F ζ hζ y⁻¹).val * KPGlobalTorusFunctionData.N F ζ hζ v) *
      ((KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ x)) * a.val := by rw [hmul]; simp
    _ = _ := by simp only [map_inv, Subgroup.coe_inv]; group

theorem angular_eqvgen_iff (D : KPMsActualAngularSource.Iwasawa F ζ hζ) (U : KPMsActualAngularSource.Level F ζ hζ)
    (a b : KPMsActualAngularSource.NormOne F ζ hζ D) :
    (KPMsActualAngularSource.angularSetoid F ζ hζ D U).r a b ↔ KPMsActualAngularSource.angularRelation F ζ hζ D U a b := by
  constructor
  · intro h
    induction h with
    | rel a b h => exact h
    | refl a => exact ⟨1,0,1,by simp [root_zero]⟩
    | symm a b h ih => exact angular_relation_symm D U a b ih
    | trans a b c h k ih ik => exact angular_relation_trans D U a b c ih ik
  · exact Relation.EqvGen.rel _ _

end DedekindZetaZeroFree.KPMsActualAngularFixedRadiusDomainSource

end
