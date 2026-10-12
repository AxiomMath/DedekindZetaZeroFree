module

public import DedekindZetaZeroFree.Eisenstein.Sections.ArchimedeanIwasawaNorm
public import DedekindZetaZeroFree.Adeles.Quotients.CuspMeasures.StabilizerAveragesAndCoarea

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization

open KPCompactStabilizerHaarSources KPActualComponentHaarSources KPMsClearedTruncationL2
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_rational_Iwasawa_fiber → actual_rational_Iwasawa_fiber
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedFullAngular → framedFullAngular
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedFullAngular_continuous → framedFullAngular_continuous
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedRadius → framedRadius
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedNormOne → framedNormOne
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming framedFullAngular_upper_transition → framedFullAngular_upper_transition
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
open KPMsResidualTailRestoration.SharpConstantTerm
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming placeEquiv → placeEquiv
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming archEquiv → archEquiv
open _root_.DedekindZetaZeroFree.KPContFlatArchProjectionNorm renaming archDiagonalLift_eq_insertion → archDiagonalLift_eq_insertion
open _root_.DedekindZetaZeroFree.KPContFlatArchProjectionNorm renaming N_eq_insertion → N_eq_insertion
open _root_.DedekindZetaZeroFree.KPContFlatArchProjectionNorm renaming adeleOfArch → adeleOfArch

private theorem sqrt_exp_double (q : ℝ) :
    Real.sqrt (Real.exp (2*q)) = Real.exp q := by
  rw [show 2*q = q+q by ring, Real.exp_add, ← pow_two,
    Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos q)]

 def radialSlotLog (w : NumberField.InfinitePlace F) (t : ℝ) :
    NumberField.InfinitePlace F → ℝ := fun v =>
  if v = w then (KPCuspLogShape.dimension F : ℝ)*t else 0

private theorem radialSection_exponential_insertion
    (w : NumberField.InfinitePlace F) (t : ℝ) :
    KPMsFixedHaarDisintegration.radialSection F ζ hζ w
      ⟨Real.exp (2*(KPCuspLogShape.dimension F : ℝ)*t),Real.exp_pos _⟩ =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun v => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ
        (Units.mk0 (Real.exp (radialSlotLog w t v) : ℂ)
          (by exact_mod_cast Real.exp_ne_zero _)) 1)) := by
  unfold KPMsFixedHaarDisintegration.radialSection
  have h : KPMsFixedHaarDisintegration.positiveSlots F w
      ⟨Real.exp (2*(KPCuspLogShape.dimension F : ℝ)*t),Real.exp_pos _⟩ =
      fun v => ((Units.mk0 (Real.exp (radialSlotLog w t v) : ℂ)
        (by exact_mod_cast Real.exp_ne_zero _)) : ℂ) := by
    funext v
    by_cases hv : v = w
    · subst v
      simp only [KPMsFixedHaarDisintegration.positiveSlots, if_pos rfl, radialSlotLog]
      rw [show 2*(KPCuspLogShape.dimension F : ℝ)*t =
        2*((KPCuspLogShape.dimension F : ℝ)*t) by ring, sqrt_exp_double]
      rfl
    · simp [KPMsFixedHaarDisintegration.positiveSlots, radialSlotLog, hv]
  rw [h]
  exact archDiagonalLift_eq_insertion F ζ hζ _

private theorem section_diagonal_inverse (q : ℝ) (z : ℂ) (t : ℝ) :
    (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ
      (Units.mk0 (Real.exp q : ℂ) (by exact_mod_cast Real.exp_ne_zero q)) 1))⁻¹ *
        KPArithmeticAction.hyperbolicProjectiveSection (z,t) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ ((Real.exp (-q) : ℂ) * z)) *
        KPArithmeticAction.hyperbolicProjectiveSection (0,t-q) := by
  unfold KPArithmeticAction.hyperbolicProjectiveSection
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [show (KubotaRankTwo.d ℂ
    (Units.mk0 (Real.exp q : ℂ) (by exact_mod_cast Real.exp_ne_zero q)) 1)⁻¹ =
    KubotaRankTwo.d ℂ
      (Units.mk0 (Real.exp (-q) : ℂ) (by exact_mod_cast Real.exp_ne_zero (-q))) 1 from ?_]
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPArithmeticAction.hyperbolicGLSection, KPArch.height, KubotaRankTwo.n,
        KubotaRankTwo.d, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_sub,
        Real.exp_neg, Complex.ofReal_mul, Complex.ofReal_inv, mul_comm, div_eq_mul_inv]
  · apply inv_eq_of_mul_eq_one_left
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_neg,
        Complex.ofReal_inv, Real.exp_ne_zero]

 def radialShapeCorrection (w : NumberField.InfinitePlace F) (t : ℝ) :
    KPCuspCharts.Shape F :=
  ⟨fun i => t - radialSlotLog w t (KPCusp.complexPlace F i), by
    change ∑ i, (t - radialSlotLog w t (KPCusp.complexPlace F i)) = 0
    simp only [radialSlotLog, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hi : ∀ i, KPCusp.complexPlace F i = w ↔ i = placeEquiv F ζ hζ w := by
      intro i
      exact (placeEquiv F ζ hζ).symm_apply_eq
    simp only [hi]
    simp⟩

 theorem radial_inverse_section_source
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (w : NumberField.InfinitePlace F) (p : KPCuspCharts.Cross F) (t : ℝ)
    (k : K (KPCuspLogShape.dimension F)) :
    (KPMsFixedHaarDisintegration.radialSection F ζ hζ w
      ⟨Real.exp (2*(KPCuspLogShape.dimension F : ℝ)*t),Real.exp_pos _⟩)⁻¹ *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (e.symm (KPCuspCharts.toArch F (p,t),k)) =
    KPGlobalTorusFunctionData.N F ζ hζ
      (adeleOfArch F ζ hζ (fun v =>
        (Real.exp (-radialSlotLog w t v) : ℂ) * p.1 (placeEquiv F ζ hζ v))) *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (e.symm (KPCuspCharts.toArch F ((0,p.2 + radialShapeCorrection (ζ := ζ) (hζ := hζ) w t),0),k)) := by
  rw [radialSection_exponential_insertion, N_eq_insertion]
  have hinv := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  let ins : KPSmoothActualFlowData.GInfinity F →* KPMsRationalCompactCrossPairing.G F ζ hζ :=
    { toFun := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ,
      map_one' := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1,
      map_mul' := hinv }
  change (ins _)⁻¹ * ins _ = ins _ * ins _
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg ins
  funext v
  obtain ⟨i,rfl⟩ := (placeEquiv F ζ hζ).symm.surjective v
  change _ * (e.symm (KPCuspCharts.toArch F (p,t),k)) (KPCusp.complexPlace F i) =
    _ * (e.symm (KPCuspCharts.toArch F ((0,p.2 + radialShapeCorrection (ζ := ζ) (hζ := hζ) w t),0),k))
      (KPCusp.complexPlace F i)
  rw [heFiber,heFiber]
  change _ * (KPArithmeticAction.hyperbolicProjectiveSection (p.1 i,t+p.2.val i) * _) = _
  simp only [Pi.inv_apply]
  rw [← mul_assoc, section_diagonal_inverse]
  simp only [Pi.mul_apply, KPCuspCharts.toArch, radialShapeCorrection,
    AddSubgroup.coe_add, Pi.add_apply, Pi.zero_apply, Equiv.apply_symm_apply]
  change (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ
    ((Real.exp (-radialSlotLog w t (KPCusp.complexPlace F i)) : ℂ) * p.1 i)) *
      KPArithmeticAction.hyperbolicProjectiveSection
        (0,t+p.2.val i-radialSlotLog w t (KPCusp.complexPlace F i))) * (k : G _) i =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ
      ((Real.exp (-radialSlotLog w t (KPCusp.complexPlace F i)) : ℂ) * p.1 i)) *
        (KPArithmeticAction.hyperbolicProjectiveSection
          (0,0+(p.2.val i+(t-radialSlotLog w t (KPCusp.complexPlace F i)))) * (k : G _) i)
  have hi : (placeEquiv F ζ hζ) (KPCusp.complexPlace F i) = i :=
    (placeEquiv F ζ hζ).right_inv i
  have ht : t + p.2.val i - radialSlotLog w t (KPCusp.complexPlace F i) =
      0 + (p.2.val i + (t - radialSlotLog w t (KPCusp.complexPlace F i))) := by ring
  rw [ht]
  exact mul_assoc _ _ _

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming rationalArch → rationalArch
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming rationalArch_equivariant → rationalArch_equivariant

 theorem source_frame_factorization
    (σ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (b : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    (rationalLift F ζ hζ σ)⁻¹ * m F ζ hζ (rationalArch F ζ hζ σ * a,b) =
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
      ((rationalLift F ζ hζ σ)⁻¹ *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (rationalArch F ζ hζ σ) * b.val) := by
  let ins := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
  let r := rationalLift F ζ hζ σ
  let s := rationalArch F ζ hζ σ
  have hs : KPSmoothLocalQuotientCharts.archProjection F ζ hζ r = s := by
    change (KPSmoothLocalQuotientCharts.archProjection F ζ hζ) (rationalLift F ζ hζ σ) =
      (KPSmoothLocalQuotientCharts.archProjection F ζ hζ)
        (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (rationalEquiv F σ))
    congr 1
    induction σ using Matrix.ProjGenLinGroup.induction_on with
    | mk M => rw [rationalLift_mk]; rfl
  have hin : KPSmoothLocalQuotientCharts.archProjection F ζ hζ (r⁻¹ * ins s) = 1 := by
    rw [map_mul,map_inv,hs]
    change s⁻¹ * (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ)
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ s) = 1
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion,inv_mul_cancel]
  have hfin := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complex_kernel_mem
    F ζ hζ hin
  have hc := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
    F ζ hζ a ⟨r⁻¹*ins s,hfin⟩
  change r⁻¹ * (ins (s*a) * b.val) = ins a * (r⁻¹*ins s*b.val)
  change r⁻¹ * (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (s*a) * b.val) = _
  rw [(KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hc' : (r⁻¹*ins s)*ins a = ins a*(r⁻¹*ins s) := hc.eq.symm
  calc
    _ = ((r⁻¹*ins s)*ins a)*b.val := by dsimp only [ins]; group
    _ = _ := by rw [hc']; group

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming tilingLift → tilingLift

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_rational_finite_fiber → actual_rational_finite_fiber

 theorem full_fiber_test_covariance
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (V : KPMsFixedHaar.Level F ζ hζ)
    (At : KPFiniteCuspAtlas.Atlas F ζ hζ hF V) (i : Fin At.componentCount)
    (e : KPSmoothActualFlowData.GInfinity F ≃ₜ
      (X (KPCuspLogShape.dimension F) × K (KPCuspLogShape.dimension F)))
    (heBase : ∀ a, (e a).1 = KPMsFixedHaarDisintegration.archBasepoint F a)
    (heFiber : ∀ x k j, (e.symm (x,k)) (KPCusp.complexPlace F j) =
      (KPArithmeticAction.productProjectiveSection (KPCuspLogShape.dimension F) x *
        (k : G (KPCuspLogShape.dimension F))) j)
    (ν : Measure (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) [ν.IsHaarMeasure] [SFinite ν]
    (Ψ : KPMsRationalCompactCrossPairing.G F ζ hζ → ℝ≥0∞) (hΨ : Measurable Ψ)
    (γ : Gi F ζ hζ hF V At i)
    (hγ : ∀ g, Ψ (tilingLift F ζ hζ γ.val * g) = Ψ g)
    (x : X (KPCuspLogShape.dimension F)) :
    (∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      Ψ (m F ζ hζ (e.symm (γ • x,z.1),z.2))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF V At i))) =
    ∫⁻ z : K (KPCuspLogShape.dimension F) × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      Ψ (m F ζ hζ (e.symm (x,z.1),z.2))
      ∂(stabilizerHaar (KPCuspLogShape.dimension F)).prod
        (ν.restrict (B F ζ hζ hF V At i)) := by
  let d := KPCuspLogShape.dimension F
  let : BorelSpace (K d) := stabilizerBorelSpace d
  let : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  let := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  let := ActualQuotient.actual_cover_secondCountable F ζ hζ
  obtain ⟨ep,hep⟩ := actual_product_splitting F ζ hζ
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F ×
    KPFiniteCuspAtlas.FiniteCover F ζ hζ) := ep.toHomeomorph.secondCountableTopology
  let : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : KPFiniteCuspAtlas.FiniteCover F ζ hζ)).secondCountableTopology
  let : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : KPSmoothActualFlowData.GInfinity F)).secondCountableTopology
  obtain ⟨κ,hκ,htrans,hκMP⟩ := actual_rational_Iwasawa_fiber (ζ := ζ) (hζ := hζ) e heBase heFiber γ.val
  obtain ⟨b,hb,hbB,hbMP⟩ := actual_rational_finite_fiber hF V At i γ ν
  let f : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ → ℝ≥0∞ := fun z =>
    Ψ (m F ζ hζ (e.symm (γ • x,z.1),z.2))
  have hfm : Measurable f := by
    apply hΨ.comp
    exact (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (e.symm.continuous.comp (continuous_const.prodMk continuous_fst))).mul
        (continuous_subtype_val.comp continuous_snd)).measurable
  have htest : ∀ z : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      f (κ x*z.1,b*z.2) = Ψ (m F ζ hζ (e.symm (x,z.1),z.2)) := by
    intro z
    dsimp only [f]
    have hx : e.symm (γ • x,κ x*z.1) = rationalArch F ζ hζ γ.val * e.symm (x,z.1) := htrans x z.1
    rw [hx,← hb,hγ]
  have hh := ((hκMP x).prod hbMP).lintegral_comp hfm
  change (∫⁻ z : K d × KPFiniteCuspAtlas.FiniteCover F ζ hζ,
    f (κ x*z.1,b*z.2) ∂(stabilizerHaar d).prod (ν.restrict (B F ζ hζ hF V At i))) =
    ∫⁻ z, f z ∂(stabilizerHaar d).prod (ν.restrict (B F ζ hζ hF V At i)) at hh
  simp only [htest] at hh
  exact hh.symm

open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.Step2Proof renaming rational_upper_literal_factorization → rational_upper_literal_factorization

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming actual_finiteOrbit_positive_finite → actual_finiteOrbit_positive_finite

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPCompactStabilizerHaarSources
attribute [local instance] KPCompactStabilizerHaarSources.groupMeasurableSpace
  KPCompactStabilizerHaarSources.groupBorelSpace
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_compact_finite_test_covariance → actual_compact_finite_test_covariance
open _root_.DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure renaming actual_high_cusp_joint_coarea → actual_high_cusp_joint_coarea

open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport

open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming archEquiv → archEquiv
open _root_.DedekindZetaZeroFree.KPCompactStabilizerHaarSources renaming cocycle → cocycle
open _root_.DedekindZetaZeroFree.KPCompactStabilizerHaarSources renaming cocycle_continuous → cocycle_continuous

end DedekindZetaZeroFree.FullAngularHaar.Constructor.JointMeasure.LocalCuspFactorization

end
