module

public import DedekindZetaZeroFree.Theta.Periods.KernelPeriodRealizationAndCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPWildKernelUpperBound

theorem uniqueFourierDensity
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hcont : Continuous θ)
    (hrational : ∀ (γ : KPRationalAdelicSplitting.RationalPGL2 F) g,
      θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (hfiber : ∀ b, Continuous (borelRootFiber F ζ hζ θ b))
    (hfourier : ∀ b (χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle),
      Continuous χ →
      (∫ x, borelRootFiber F ζ hζ θ b x * (χ x : ℂ) ∂quotientHaar F) = 0) :
    θ = 0 := by
  classical
  letI := (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.1
  have hroot (x : KPGlobalTorusFunctionData.Adeles F) :
      KPGlobalTorusFunctionData.N F ζ hζ x ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
    change ∃ A : KPGlobalTorusFunctionData.AdelicMatrixGroup F,
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
        KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
          (KPGlobalTorusFunctionData.N F ζ hζ x) ∧ A 1 0 = 0
    refine ⟨KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x), rfl, ?_⟩
    apply Prod.ext
    · funext w
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
    · apply RestrictedProduct.ext
      intro q
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
  have hB (b : KPGlobalTorusFunctionData.borel F ζ hζ) : θ b.val = 0 := by
    let n := KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F 0)
    let b' : KPGlobalTorusFunctionData.borel F ζ hζ :=
      ⟨n⁻¹ * b.val, (KPGlobalTorusFunctionData.borel F ζ hζ).mul_mem
        ((KPGlobalTorusFunctionData.borel F ζ hζ).inv_mem (hroot _)) b.property⟩
    have havg : (∫ x, borelRootFiber F ζ hζ θ b' x ∂quotientHaar F) = 0 := by
      simpa using hfourier b' 1 continuous_const
    have heq := kp_additive_adelic_fourier_uniqueness F (quotientHaar F)
      (borelRootFiber F ζ hζ θ b') (hfiber b') (fun χ hχ _ => hfourier b' χ hχ) 0
    rw [havg] at heq
    simpa [borelRootFiber, b', n] using heq
  have hθ : (fun g : KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ =>
      θ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ g)) = 0 := by
    apply kp_rational_adelic_cover_borel_vanishing F
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ)
      (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2.continuous
      (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.2.isOpenMap
      (KPAdelicCoverRestrictedProduct.projection_surjective F ζ hζ)
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)
      (KPRationalAdelicSplitting.rational_splitting F ζ hζ).2
    · exact hcont.comp QuotientGroup.continuous_mk
    · intro γ g
      have h := hrational (KPRationalAdelicSplitting.rationalPGLQuotient F γ)
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ g)
      rw [KPRationalAdelicSplitting.rationalPGLHom_mk] at h
      rw [map_mul]
      exact h
    · intro g hg
      apply hB ⟨KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ g, ?_⟩
      exact ⟨KPAdelicCoverRestrictedProduct.projection F ζ hζ g, rfl, hg⟩
  funext g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact congrFun hθ g

end DedekindZetaZeroFree.KPWildKernelUpperBound

end
