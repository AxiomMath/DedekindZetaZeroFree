module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspShapes.IntrinsicShapeDescent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeFramePin
open KPMsActualAngularSource KPMsNativeOffsetMass

theorem shaped_fullCoordinate_on_cuspShell
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (S : NativeRecipe F ζ hζ R P)
    (shape : ∀ V : Level F ζ hζ,
      Omega F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) →
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hshape : ∀ V, Measurable (shape V))
    (hframe : ∀ (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V) (Y : ℝ),
      OffsetAdmissible F ζ hζ R P S V Y →
      ∀ (x : KPSmoothLocalQuotientCharts.X F ζ hζ),
        x ∈ cuspShell F ζ hζ R P S V j Y →
      ∀ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
        (t : ℝ) (ε : rootsOfUnity 3 F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (cofinalLevel F ζ hζ V)),
        actualFrame F ζ hζ R P S V j Y x =
          KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
            ((nativeAtlas F ζ hζ R P S V).representative j.1).val *
              KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val →
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((nativeAtlas F ζ hζ R P S V).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t)) →
        shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
          (fullCoordinate F ζ hζ R P S V j Y x)) =
          (⟨j, QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
            (nativeFamily F ζ hζ R P).totallyComplex
            (nativeDisintegration F ζ hζ R P S V).radial.slot
            ⟨(cuspOffset F ζ hζ R P S V j).val *
                Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),
              mul_pos (cuspOffset F ζ hζ R P S V j).property (Real.exp_pos _)⟩)⟩ :
            KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)))
    (V : Level F ζ hζ) (j : NativeCusp F ζ hζ R P S V) (Y : ℝ)
    (hY : OffsetAdmissible F ζ hζ R P S V Y)
    (s : KPMsFixedHaarDisintegration.Spherical F ζ hζ
      (S.atlasLevel (cofinalLevel F ζ hζ V)) →
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V))
    (hsc : ∀ z r, s ((nativeDisintegration F ζ hζ R P S V).chart
      (Y / (cuspOffset F ζ hζ R P S V j).val) (hY j) (z,r)) =
      KPMsFixedHaarDisintegration.angularProjection (nativeAtlas F ζ hζ R P S V) z)
    (x : KPSmoothLocalQuotientCharts.X F ζ hζ)
    (hx : x ∈ cuspShell F ζ hζ R P S V j Y) :
    ∃ b : KPCuspCharts.Base F (nativeFamily F ζ hζ R P).totallyComplex
      (KPMsFixedHaarDisintegration.Parabolic (nativeAtlas F ζ hζ R P S V) j).E
      (KPMsFixedHaarDisintegration.Parabolic (nativeAtlas F ζ hζ R P S V) j).integralUnits,
      s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) = ⟨j,b⟩ ∧
      shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V)
        (fullCoordinate F ζ hζ R P S V j Y x)) =
      ⟨j, b - QuotientAddGroup.mk (KPMsFixedHaarDisintegration.sectionShape F
        (nativeFamily F ζ hζ R P).totallyComplex
        (nativeDisintegration F ζ hζ R P S V).radial.slot
        (cuspOffset F ζ hζ R P S V j))⟩ := by
  have hg : KPMsActualCuspSource.AdmissibleFrame
      (H := nativeFamily F ζ hζ R P) (U := cofinalLevel F ζ hζ V)
      (S.atlasLevel (cofinalLevel F ζ hζ V)) j
      (Y / (cuspOffset F ζ hζ R P S V j).val) x
      (actualFrame F ζ hζ R P S V j Y x) := by
    rw [actualFrame, dif_pos hx.1]
    exact (Classical.choose_spec (KPMsActualCuspSource.cusp_lift_exists
      (H := nativeFamily F ζ hζ R P)
      (S.atlasLevel (cofinalLevel F ζ hζ V))
      (S.level_matching (cofinalLevel F ζ hζ V)) j _ x hx.1)).2
  obtain ⟨hq,a,p,t,ε,u,ht,ha,he⟩ := hg
  have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F
      (nativeFamily F ζ hζ R P).totallyComplex))
  have hr : Y / (cuspOffset F ζ hζ R P S V j).val <
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
    apply (Real.log_lt_iff_lt_exp (hY j).1).mp
    exact (mul_comm t _ ▸ (div_lt_iff₀ hd).mp ht)
  let r : Set.Ioi (Y / (cuspOffset F ζ hζ R P S V j).val) :=
    ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t),hr⟩
  have hl : KPMsFixedHaarDisintegration.logHeight (F := F) r.val = t := by
    change Real.log (Real.exp _) / _ = _
    rw [Real.log_exp, mul_div_cancel_left₀ _ hd.ne']
  let B := KPMsFixedHaarDisintegration.sectionShape F
    (nativeFamily F ζ hζ R P).totallyComplex
    (nativeDisintegration F ζ hζ R P S V).radial.slot
    ⟨r.val, lt_trans (hY j).1 r.property⟩
  let p₀ : KPCuspCharts.Cross F := (p.1, p.2 - B)
  have hcross : (p₀.1, p₀.2 + B) = p := by
    apply Prod.ext
    · rfl
    · exact sub_add_cancel _ _
  have hproj := FullSupportGeometry.chart_projection S V j a ε u
  rw [← he, hq] at hproj
  have hchart : (nativeDisintegration F ζ hζ R P S V).chart
      (Y / (cuspOffset F ζ hζ R P S V j).val) (hY j)
      (⟨j, Quotient.mk _ p₀⟩,r) =
      P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x := by
    rw [hproj, ha]
    rw [(nativeDisintegration F ζ hζ R P S V).chart_formula _ (hY j) j p₀ r]
    simp only [KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection, Quotient.lift_mk]
    change Quotient.mk _ (_, _) = Quotient.mk _ (_, _)
    rw [hl, hcross]
    rfl
  have hs : s (P.projection (S.atlasLevel (cofinalLevel F ζ hζ V)) x) =
      (⟨j, QuotientAddGroup.mk (p.2 - B)⟩ :
        KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) := by
    rw [← hchart, hsc]
    change (⟨j, (KPMsFixedHaarDisintegration.Geometry
      (nativeAtlas F ζ hζ R P S V) j).atlas.projection (Quotient.mk _ p₀)⟩ :
      KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)) = _
    rw [(KPMsFixedHaarDisintegration.Geometry
      (nativeAtlas F ζ hζ R P S V) j).atlas.projection_formula]
  refine ⟨QuotientAddGroup.mk (p.2 - B), hs, ?_⟩
  rw [hframe V j Y hY x hx a p t ε u he ha]
  have hsplit := OffsetShapeDescent.sectionShape_intrinsic_split F ζ hζ R P S V j
    (nativeDisintegration F ζ hζ R P S V).radial.slot p.2 t
  apply congrArg (fun b => (⟨j,b⟩ :
    KPMsFixedHaarDisintegration.Omega (nativeAtlas F ζ hζ R P S V)))
  change QuotientAddGroup.mk (p.2 - KPMsFixedHaarDisintegration.sectionShape F
    (nativeFamily F ζ hζ R P).totallyComplex
    (nativeDisintegration F ζ hζ R P S V).radial.slot _) = _
  rw [hsplit]
  exact map_sub (QuotientAddGroup.mk' _) _ _

end DedekindZetaZeroFree.KPMsNativeWeightedShapeSource.OffsetShapeFramePin

end
