module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.FiniteOffsetData
public import DedekindZetaZeroFree.Metaplectic.Torus.CuspFrames.LogNormNormalization

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPMsAngularSourceRecipe
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finiteComponent_mul (x y : G F ζ hζ) :
    finiteComponent F ζ hζ (x * y) =
      finiteComponent F ζ hζ x * finiteComponent F ζ hζ y := by
  have hx : finiteComponent F ζ hζ x ∈
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
    rw [MonoidHom.mem_ker]
    unfold finiteComponent
    rw [map_mul, map_inv,
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    simp
  have hc : Commute
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ y))
      (finiteComponent F ζ hζ x) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _
      ⟨_, RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ hx⟩
  have hmul : ∀ (a b : PGLComplex.AdelicSlicesRaw.ArchGroup F),
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ (a * b) =
        PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a *
          PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ b :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  calc
    finiteComponent F ζ hζ (x * y) =
        (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
          (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ y))⁻¹ *
          (finiteComponent F ζ hζ x * y) := by
      unfold finiteComponent
      rw [map_mul, hmul, mul_inv_rev]
      group
    _ = finiteComponent F ζ hζ x * finiteComponent F ζ hζ y := by
      rw [← mul_assoc, hc.inv_left.eq, mul_assoc]
      rfl

theorem actual_frame_norm_factorization
    (σ : KPCuspArithmetic.PGL2 F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (p : KPCuspCharts.Cross F) (t : ℝ)
    (ha : KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F σ (KPCuspCharts.toArch F (p,t))) :
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (D F ζ hζ)
      ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ * frame F ζ hζ a c.val) : ℝ≥0) : ℝ) =
      (finiteOffset F ζ hζ (KPMsActualCuspSource.rationalLift F ζ hζ σ) c.val).val *
        Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  have hi : finiteComponent F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = 1 := by
    unfold finiteComponent
    rw [show KPSmoothActualFlowData.archimedeanInsertion F ζ hζ =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ from rfl,
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion,
      inv_mul_cancel]
  have hf : finiteComponent F ζ hζ
      ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ * frame F ζ hζ a c.val) =
      finiteComponent F ζ hζ
        ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ * c.val) := by
    simp only [frame, finiteComponent_mul, hi, one_mul]
  have hl := Shift81AngularSourceRecipe.actual_cusp_frame_log_norm F ζ hζ σ a c p t ha
  change KPContFlatFullProductIwasawa.alpha F ζ hζ
    ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ * frame F ζ hζ a c.val) =
    2 * (KPCuspLogShape.dimension F : ℝ) * t +
      KPContFlatLogNormSmooth.finiteLogNorm F ζ hζ
        ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ * frame F ζ hζ a c.val) at hl
  change KPContFlatFullProductIwasawa.alpha F ζ hζ _ =
    2 * (KPCuspLogShape.dimension F : ℝ) * t +
      KPContFlatFullProductIwasawa.alpha F ζ hζ (finiteComponent F ζ hζ _) at hl
  rw [hf] at hl
  have hn : 0 < ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (D F ζ hζ) ((KPMsActualCuspSource.rationalLift F ζ hζ σ)⁻¹ *
        frame F ζ hζ a c.val) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have ho : 0 < (finiteOffset F ζ hζ
      (KPMsActualCuspSource.rationalLift F ζ hζ σ) c.val).val :=
    (finiteOffset F ζ hζ _ _).property
  have he := congrArg Real.exp hl
  change Real.exp (Real.log _) =
    Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t +
      Real.log (finiteOffset F ζ hζ
        (KPMsActualCuspSource.rationalLift F ζ hζ σ) c.val).val) at he
  rw [Real.exp_log hn, Real.exp_add, Real.exp_log ho, mul_comm] at he
  exact he
end DedekindZetaZeroFree.KPMsAngularSourceRecipe

end
