module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShells.WeightedShapeProbabilities

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.FrameNorm
open KPMsNativeOffsetMass KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem central_right_norm
    (g : KPMsAngularSourceRecipe.G F ζ hζ) (ε : rootsOfUnity 3 F) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (KPMsAngularSourceRecipe.D F ζ hζ)
      (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) =
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (KPMsAngularSourceRecipe.D F ζ hζ) g := by
  have hπ : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel]
    exact ⟨ε, rfl⟩
  let z : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε, by
      change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ _ ∈
        KPGlobalTorusFunctionData.ordinaryTorus F
      rw [hπ]
      exact one_mem _⟩
  have hp : KPGlobalTorusFunctionData.p F ζ hζ z = 1 := by
    change KPGlobalTorusFunctionData.torusRatio F
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val, z.property⟩ = 1
    have hz : (⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val, z.property⟩ :
        KPGlobalTorusFunctionData.ordinaryTorus F) = 1 := by
      apply Subtype.ext
      exact hπ
    rw [hz, map_one]
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ z = 1 := by
    change KPGlobalTorusFunctionData.ideleAbs F (KPGlobalTorusFunctionData.p F ζ hζ z) = 1
    rw [hp, map_one]
  have hc := Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) g
  rw [hc]
  have hn := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul F ζ hζ
    (KPMsAngularSourceRecipe.D F ζ hζ) z 0 g
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simpa only [hN, mul_one, hd, one_mul] using hn

theorem actual_frame_norm_coherent
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (S : NativeRecipe F ζ hζ R P) (V : Level F ζ hζ)
    (j : NativeCusp F ζ hζ R P S V)
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F) (t : ℝ)
    (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V))
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t))) :
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (nativeDatum F ζ hζ)
      ((KPMsActualCuspSource.rationalLift F ζ hζ
        (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2))⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
            KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) : ℝ≥0) : ℝ) =
      (cuspOffset F ζ hζ R P S V j).val *
        Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  have hn := S.height_normalized (cofinalLevel F ζ hζ V) j a p t 1 1 ha
  simp only [map_one, OneMemClass.coe_one, mul_one,
    KPMsAngularSourceRecipe.frame] at hn
  simp only [← mul_assoc]
  rw [KPShift81CoherentLevel.norm_right_level F ζ hζ V]
  rw [central_right_norm F ζ hζ]
  simpa only [mul_assoc, cuspOffset] using hn

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.FrameNorm

end
