module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.RadialComparison.SphericalModulus.NormalForm

open KPMsClearedTruncationL2

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
variable {U : Level F ζ hζ}

private theorem chart_projection_aux (j : Cusp (A := A) (U := U))
    (a : KPSmoothActualFlowData.GInfinity F) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
    P.projection (A.atlasLevel U) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
        ((Atlas (A := A) (U := U)).representative j.1).val *
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) =
      Quotient.mk _ (KPMsFixedHaarDisintegration.archBasepoint F a,
        (Atlas (A := A) (U := U)).representative j.1) := by
  have hu := u.property
  simp only [A.level_matching U] at hu
  obtain ⟨uf, huf, heq⟩ := hu
  let uf' : (A.atlasLevel U).toOpenSubgroup := ⟨uf, huf⟩
  have heq' : uf'.val.val = u.val := heq
  have hcentre : (KPCuspGenuineMonodromy.central F ζ hζ ε).val =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε := rfl
  rw [← heq', ← hcentre]
  simp only [mul_assoc]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, P.formula]
  apply Quotient.sound
  change (KPFiniteCuspAtlas.sphericalRelation F ζ hζ (A.atlasLevel U)).r _ _
  refine ⟨1, ε⁻¹, uf'⁻¹, by simp, ?_⟩
  simp only [map_one, one_mul, mul_assoc]
  have hc : KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
      (Atlas (A := A) (U := U)).representative j.1 =
      (Atlas (A := A) (U := U)).representative j.1 *
        KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ := by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
        ⟨ε⁻¹, rfl⟩) _).symm
  rw [← mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹), hc]
  simp [map_inv, mul_assoc]

theorem spherical_modulus_of_cusp_basepoint
    (j : Cusp (A := A) (U := U)) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (Atlas (A := A) (U := U)) Y)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U)
    (ht : KPMsFixedHaarDisintegration.logHeight (F := F) Y < t)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((Atlas (A := A) (U := U)).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t))) :
    (H.disintegration (A.atlasLevel U)).modulus
      (P.projection (A.atlasLevel U)
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((Atlas (A := A) (U := U)).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val))) =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  have hd : (0 : ℝ) < (KPCuspLogShape.dimension F : ℝ) := by
    exact_mod_cast KPCuspLogShape.dimension_pos F H.totallyComplex
  have hd2 : (0 : ℝ) < 2 * (KPCuspLogShape.dimension F : ℝ) := by linarith
  have hlog : Real.log Y < 2 * (KPCuspLogShape.dimension F : ℝ) * t := by
    have h1 : Real.log Y < t * (2 * (KPCuspLogShape.dimension F : ℝ)) :=
      (div_lt_iff₀ hd2).mp ht
    linarith [mul_comm t (2 * (KPCuspLogShape.dimension F : ℝ))]
  have hYexp : Y < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) :=
    (Real.log_lt_iff_lt_exp hY.1).mp hlog
  let r : Set.Ioi Y := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), hYexp⟩
  have hrval : r.val = Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := rfl
  have hlh : KPMsFixedHaarDisintegration.logHeight (F := F) r.val = t := by
    rw [KPMsFixedHaarDisintegration.logHeight, hrval, Real.log_exp]
    exact mul_div_cancel_left₀ t (ne_of_gt hd2)
  have hproj := chart_projection_aux (A := A) (U := U) j a ε u
  rw [hproj, ha]
  set S : KPCuspCharts.Shape F :=
    KPMsFixedHaarDisintegration.sectionShape F H.totallyComplex
      ((H.disintegration (A.atlasLevel U)).radial.slot)
      ⟨r.val, lt_trans hY.1 r.property⟩ with hS
  let p₀ : KPCuspCharts.Cross F := (p.1, p.2 - S)
  have hcross : (p₀.1, p₀.2 + S) = p := by
    apply Prod.ext
    · rfl
    · dsimp only [p₀]; exact sub_add_cancel p.2 S
  have hcoord : ((p₀.1, p₀.2 + S),
      KPMsFixedHaarDisintegration.logHeight (F := F) r.val) = (p, t) := by
    rw [hcross, hlh]
  have hchart : (H.disintegration (A.atlasLevel U)).chart Y hY
      (⟨j, Quotient.mk _ p₀⟩, r) =
      Quotient.mk _ (KPCuspSiegel.action F
        (((Atlas (A := A) (U := U)).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)),
        (Atlas (A := A) (U := U)).representative j.1) := by
    rw [(H.disintegration (A.atlasLevel U)).chart_formula Y hY j p₀ r]
    simp only [KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection,
      Quotient.lift_mk]
    rw [← hS, hcoord]
    rfl
  rw [← hchart, (H.disintegration (A.atlasLevel U)).chart_modulus Y hY _ r]

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.RadialComparison.SphericalModulus.NormalForm

end
