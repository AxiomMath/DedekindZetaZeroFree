module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.CrossLevelFrameTransport
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPMsRationalCompactCrossPairing
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

section Normalization
variable (D : Iwasawa F ζ hζ) (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
variable (σ : KPMsRationalCompactCrossPairing.G F ζ hζ)

local instance : IsTopologicalGroup (KPMsRationalCompactCrossPairing.G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

 def framedRadius (g : KPMsRationalCompactCrossPairing.G F ζ hζ) : KPMsFixedHaarDisintegration.Radius :=
  ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) : ℝ≥0) : ℝ),
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩

private theorem framedRadius_continuous : Continuous (framedRadius F ζ hζ D σ) := by
  apply Continuous.subtype_mk
  exact (fullCusp_iwasawaNorm_continuous F ζ hζ D).comp (continuous_const.mul continuous_id)

 def framedNormOne (g : KPMsRationalCompactCrossPairing.G F ζ hζ) : NormOne F ζ hζ D :=
  ⟨(KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
    (framedRadius F ζ hζ D σ g))⁻¹ * (σ⁻¹ * g), by
    let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (KPMsFixedHaarDisintegration.positiveSlots F B.slot (framedRadius F ζ hζ D σ g))
    have hd : KPGlobalTorusFunctionData.delta F ζ hζ t =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) := by
      apply Units.ext
      apply NNReal.eq
      exact KPMsRationalCompactCrossPairing.compact_radialSection_delta B (framedRadius F ζ hζ D σ g)
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D ((t⁻¹).val * _) = 1
    rw [KPMsClearedTruncationL2.iwasawaNorm_torus_mul (D := D), map_inv, hd, inv_mul_cancel]⟩

private theorem framedNormOne_continuous : Continuous (framedNormOne F ζ hζ D B σ) := by
  apply Continuous.subtype_mk
  exact (B.continuous_section.comp (framedRadius_continuous F ζ hζ D σ)).inv.mul
    (continuous_const.mul continuous_id)

 def framedFullAngular (g : KPMsRationalCompactCrossPairing.G F ζ hζ) : FullOmega F ζ hζ D :=
  Quotient.mk _ (framedNormOne F ζ hζ D B σ g)

 theorem framedFullAngular_continuous : Continuous (framedFullAngular F ζ hζ D B σ) :=
  continuous_quotient_mk'.comp (framedNormOne_continuous F ζ hζ D B σ)

 theorem framedFullAngular_upper_transition (g h : KPMsRationalCompactCrossPairing.G F ζ hζ)
    (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F)
    (hh : σ⁻¹ * h = (KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x * (σ⁻¹ * g)) :
    framedFullAngular F ζ hζ D B σ h = framedFullAngular F ζ hζ D B σ g := by
  have hr : framedRadius F ζ hζ D σ h = framedRadius F ζ hζ D σ g := by
    apply Subtype.ext
    exact congrArg (fun r : (ℝ≥0)ˣ => ((r : ℝ≥0) : ℝ))
      (KPMsActualAngularCrossLevelFrameSource.framed_iwasawaNorm_eq_of_delta_one D σ g h _ x hh
        (KPGlobalTorusBorelNormTwistTransport.delta_rational F ζ hζ y))
  let r := framedRadius F ζ hζ D σ g
  let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
  have ht : t.val = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r := rfl
  obtain ⟨z,hz⟩ := KPMsActualAngularDescentSource.radialSection_mem_center F ζ hζ B r
  have hzt : z.val = t := Subtype.ext (hz.trans ht.symm)
  have hc : Commute t (KPGlobalTorusFunctionData.s F ζ hζ y) := by
    rw [← hzt]
    exact (Subgroup.mem_center_iff.mp z.property _).symm
  have hcc : t.val⁻¹ * (KPGlobalTorusFunctionData.s F ζ hζ y).val =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val * t.val⁻¹ := by
    exact congrArg (fun u : KPGlobalTorusFunctionData.E F ζ hζ => u.val) hc.inv_left.eq
  have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ t⁻¹ x
  apply Eq.symm
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨y, (KPGlobalTorusFunctionData.p F ζ hζ t⁻¹ : KPGlobalTorusFunctionData.Adeles F) * x, ?_⟩
  change (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
    (framedRadius F ζ hζ D σ h))⁻¹ * (σ⁻¹ * h) = _
  rw [hr, hh]
  change t.val⁻¹ * ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
    KPGlobalTorusFunctionData.N F ζ hζ x * (σ⁻¹ * g)) =
    ((KPGlobalTorusFunctionData.s F ζ hζ y).val * _) * (t.val⁻¹ * (σ⁻¹ * g))
  rw [← hn]
  simp only [Subgroup.coe_inv, inv_inv]
  simp only [← mul_assoc]
  rw [hcc]
  group

open KPMsResidualTailRestoration.SharpConstantTerm

 theorem rational_upper_literal_factorization (g : KPCuspArithmetic.PGL2 F)
    (hg : KPCuspArithmetic.IsUpperTriangular F g) :
    ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F),
      KPMsClearedTruncationL2.rationalLift F ζ hζ g =
        (KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  obtain ⟨M, rfl, hM⟩ := hg
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero M
  rw [Matrix.det_fin_two, hM, mul_zero, sub_zero] at hdet
  obtain ⟨ha, hd⟩ := mul_ne_zero_iff.mp hdet
  let a : Fˣ := Units.mk0 ((M : Matrix (Fin 2) (Fin 2) F) 0 0) ha
  let d : Fˣ := Units.mk0 ((M : Matrix (Fin 2) (Fin 2) F) 1 1) hd
  let y : Fˣ := a / d
  let b : F := (M : Matrix (Fin 2) (Fin 2) F) 0 1 / (a : F)
  have heq : M = Matrix.GeneralLinearGroup.scalar (Fin 2) d *
      KubotaRankTwo.d F y 1 * KubotaRankTwo.n F b := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, a, d, y, b, hM]
    all_goals field_simp [ha, hd] <;> ring
  have hs : KPMsClearedTruncationL2.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk M) =
      KPMsClearedTruncationL2.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F y 1)) *
        KPMsClearedTruncationL2.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n F b)) := by
    have hmul : ∀ (g h : KPCuspArithmetic.PGL2 F),
        KPMsClearedTruncationL2.rationalLift F ζ hζ (g * h) =
          KPMsClearedTruncationL2.rationalLift F ζ hζ g *
            KPMsClearedTruncationL2.rationalLift F ζ hζ h :=
      KPMsActualAngularTransitionSource.rationalLift_mul F ζ hζ
    rw [heq, map_mul, map_mul, hmul, hmul]
    have hz : KPMsClearedTruncationL2.rationalLift F ζ hζ
        (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) = 1 := by
      rw [KPMsClearedTruncationL2.rationalLift_mk]
      exact KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨d, rfl⟩
    rw [hz, one_mul]
  refine ⟨y, algebraMap F (KPGlobalTorusFunctionData.Adeles F) b, ?_⟩
  rw [hs, KPMsClearedTruncationL2.rationalLift_mk, KPMsClearedTruncationL2.rationalLift_mk]
  congr 1
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPRationalAdelicSplitting.N_rational F ζ hζ b).symm

end Normalization

section CuspDescent
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
variable {C : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {A : RawCompactComparison F ζ hζ C D R P H}
variable {U : KPMsRationalCompactCrossPairing.Level F ζ hζ}
open KPMsClearedTruncationL2
open KPMsResidualTailRestoration.SharpConstantTerm

include C D U

end CuspDescent

section Patch
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}
variable {C : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
open KPMsClearedTruncationL2

end Patch

end DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof

noncomputable section
open scoped NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.FullAngularHaar.Constructor

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : KPMsRationalCompactCrossPairing.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

end DedekindZetaZeroFree.FullAngularHaar.Constructor

end
end
