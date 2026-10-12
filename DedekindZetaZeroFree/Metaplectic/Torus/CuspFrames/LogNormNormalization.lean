module

public import DedekindZetaZeroFree.Eisenstein.Sections.SmoothIwasawaLogNorm
public import DedekindZetaZeroFree.Adeles.Approximation.UpperRoots.AngularAction

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace DedekindZetaZeroFree.Shift81AngularSourceRecipe
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem actual_cusp_frame_log_norm
    (σ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    KPContFlatFullProductIwasawa.alpha F ζ hζ
      ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)) =
      2 * (KPCuspLogShape.dimension F : ℝ) * t +
        KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ
          ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ *
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)) := by
  let g : KPGlobalTorusFunctionData.G F ζ hζ :=
    (KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)
  have hc : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1 := by
    funext w
    rw [KPMsActualCuspSource.projection_compare]
    have h := MonoidHom.mem_ker.mp c.property
    rw [h]
    exact map_one _
  have hg : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g =
      (KPMsActualCuspSource.archRational F σ)⁻¹ * a := by
    dsimp only [g]
    rw [map_mul, map_inv, map_mul,
      KPMsActualCuspSource.rationalLift_archProjection,
      show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ from rfl,
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion,
      hc, mul_one]
  have hb : KPMsFixedHaarDisintegration.archBasepoint F
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g) =
      KPCuspCharts.toArch F (p,t) := by
    rw [hg, KPMsActualAngularRootAlgebraSource.archBasepoint_mul]
    rw [← KPMsActualAngularRootAlgebraSource.archRational_action σ] at ha
    funext i
    change KPArch.action
      ((KPMsActualAngularRootAlgebraSource.archRational σ
        (KPCusp.complexPlace F i))⁻¹).out
      (KPMsFixedHaarDisintegration.archBasepoint F a i) = _
    rw [ha]
    exact KPMsActualAngularRootAlgebraSource.projective_action_inv_cancel _ _
  have hl : ∀ q : Matrix.ProjGenLinGroup (Fin 2) ℂ,
      KPContFlatLogNormSmooth.complexProjectiveLogNorm q =
        2 * (KPArch.action q.out (0,0)).2 := by
    intro q
    simp [KPContFlatLogNormSmooth.complexProjectiveLogNorm,
      KPContFlatLogNormSmooth.complexMatrixLogNorm, Real.log_pow,
      KPArch.action, KPArch.actionDenominator, KPArch.height, add_comm]
  let e : InfinitePlace F ≃ Fin (KPCuspLogShape.dimension F) :=
    { toFun := fun w => Fintype.equivFin {w : InfinitePlace F // w.IsComplex}
        ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
      invFun := KPCusp.complexPlace F
      left_inv := by intro w; exact congrArg Subtype.val (Equiv.symm_apply_apply _ _)
      right_inv := by
        intro i
        exact (Fintype.equivFin {w : InfinitePlace F // w.IsComplex}).apply_symm_apply i }
  change KPContFlatFullProductIwasawa.alpha F ζ hζ g =
    2 * (KPCuspLogShape.dimension F : ℝ) * t +
      KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ g
  rw [KPContFlatLogNormSmooth.alpha_eq_arch_sum_add_finite]
  congr 1
  rw [← e.symm.sum_comp (fun w => KPContFlatLogNormSmooth.complexProjectiveLogNorm
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w))]
  simp only [hl]
  change (∑ i : Fin (KPCuspLogShape.dimension F),
    2 * (KPMsFixedHaarDisintegration.archBasepoint F
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g) i).2) = _
  rw [hb]
  have hp : ∑ i, (p.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i = 0 :=
    p.2.property
  simp only [KPCuspCharts.toArch, ← Finset.mul_sum,
    Finset.sum_add_distrib, hp, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end DedekindZetaZeroFree.Shift81AngularSourceRecipe

end
