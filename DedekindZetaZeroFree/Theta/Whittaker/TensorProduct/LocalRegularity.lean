module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.UniformFlow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory KPGlobalResidualConstruction
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

def localUniformCoordinates (w : InfinitePlace F) (t : ℝ) : ArchCoordinates F :=
  Function.update (archBase F) w (SheetRescaling.uniformCoordinates R t w)

lemma localUniformCoordinates_smooth (w : InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) (localUniformCoordinates R w) := by
  apply contDiff_pi.mpr
  intro v
  by_cases hv : v = w
  · subst v
    simp only [localUniformCoordinates, Function.update_self]
    exact contDiff_pi.mp (SheetRescaling.uniformCoordinates_smooth R) w
  · simp only [localUniformCoordinates, Function.update_of_ne hv]
    exact contDiff_const

lemma localUniformCoordinates_mem (w : InfinitePlace F) (t : ℝ) :
    localUniformCoordinates R w t ∈ archDomain F := by
  intro v
  by_cases hv : v = w
  · subst v
    simp only [localUniformCoordinates, Function.update_self]
    exact SheetRescaling.uniformCoordinates_mem R t w
  · simp [localUniformCoordinates, Function.update_of_ne hv, archBase]

lemma localUniformChart (w : InfinitePlace F) (t : ℝ) :
    archChart F R.A.zeta12 R.A.primitive_zeta12 (localUniformCoordinates R w t) =
      KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
          ((R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) := by
  rw [KPRationalAdelicSplitting.pglA, KPRationalAdelicSplitting.A_local]
  unfold archChart KPAdelicCoverRestrictedProduct.localInjection
  simp only [MonoidHom.comp_apply]
  apply congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inr q =>
      change (1 : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) =
        Pi.mulSingle (Sum.inl w)
          (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
            ((R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) (Sum.inr q)
      simp
  | inl v =>
      change (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 v)).symm
              (localUniformCoordinates R w t v 0)) *
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
          (if h : localUniformCoordinates R w t v 1 = 0 then 1 else Units.mk0
            ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 v)).symm
                (localUniformCoordinates R w t v 1)) _) *
        KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 v)).symm
              (localUniformCoordinates R w t v 2))) =
        Pi.mulSingle (Sum.inl w)
          (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
            ((R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) (Sum.inl v)
      by_cases hv : v = w
      · subst v
        have hne : (Real.exp (t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
        simp only [localUniformCoordinates, Function.update_self, SheetRescaling.uniformCoordinates,
          show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide,
          ↓reduceIte, map_zero, KPStandardLocalRootLifts.N_zero,
          KPStandardLocalRootLifts.LowerN_zero, one_mul, mul_one, dif_neg hne]
        simp only [KPAdelicCoverRestrictedProduct.localToRestricted,
          RestrictedProduct.mulSingleMonoidHom, RestrictedProduct.mulSingle,
          Pi.mulSingle_eq_same]
        congr 1
        apply Units.ext
        simp only [Units.val_mk0]
        exact (RingEquiv.eq_symm_apply _).mpr (SheetRescaling.radial_arch_value R t w) |>.symm
      · simp [localUniformCoordinates, Function.update_of_ne hv, archBase,
          KPAdelicCoverRestrictedProduct.localToRestricted,
          RestrictedProduct.mulSingleMonoidHom, RestrictedProduct.mulSingle,
          Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne hv)]

lemma local_diagonal_uniform (w : InfinitePlace F) (z : w.Completionˣ) (t : ℝ) :
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
        (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) =
    KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) *
        archChart F R.A.zeta12 R.A.primitive_zeta12 (localUniformCoordinates R w t) := by
  rw [localUniformChart]
  simp only [KPRationalAdelicSplitting.pglA, KPRationalAdelicSplitting.A_local]
  rw [← map_mul, ← map_mul, KPStandardLocalRootLifts.A_mul]
  simp only [KPHilbert.B3, KPHilbert.B6_infinite, map_one, one_pow, one_mul]

theorem localWeyl_uniform_contDiff (v : R.A.UnitQuotient) (w : InfinitePlace F)
    (z : w.Completionˣ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) := by
  have h := (SheetRescaling.fourier_chart_contDiffOn C.realization v
    (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z))
    (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) (KPRationalAdelicSplitting.WCoordinates F R.A.zeta12
          R.A.primitive_zeta12 (Sum.inl w))))).comp
    ((localUniformCoordinates_smooth R w).contDiffOn (s := Set.univ))
    (fun t _ => localUniformCoordinates_mem R w t)
  rw [contDiffOn_univ] at h
  have he : (fun t : ℝ => ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
      (z * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) =
      fun t => fourier R C.sources.dq (C.realization.theta v)
        ((KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) *
            archChart F R.A.zeta12 R.A.primitive_zeta12 (localUniformCoordinates R w t)) *
          KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
              (Sum.inl w) (KPRationalAdelicSplitting.WCoordinates F R.A.zeta12
                R.A.primitive_zeta12 (Sum.inl w)))) /
          fourier R C.sources.dq (C.realization.theta v) 1 := by
    funext t
    unfold ThetaExpansion.normalizedLocalWeylValue
    rw [local_diagonal_uniform]
  rw [he]
  exact h.div_const _

theorem arch_product_jet_le_unconditional (v : R.A.UnitQuotient) (z : R.A.G)
    (u : ℝ) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j (fun t : ℝ => ∏ w : InfinitePlace F,
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inl w)
        (z.1 w * (R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w)) u‖ ≤
      4 ^ Fintype.card (InfinitePlace F) *
        ∑ a : InfinitePlace F → Fin 3, ∏ w : InfinitePlace F,
          ‖ThetaExpansion.localWeylArchJet R C v w (a w).val
            ((z * R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w)‖ := by
  exact arch_product_jet_le R C v z
    (fun w => (localWeyl_uniform_contDiff R C v w (z.1 w)).of_le (by simp)) u j hj

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
