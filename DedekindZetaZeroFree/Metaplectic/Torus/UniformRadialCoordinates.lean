module

public import DedekindZetaZeroFree.Theta.Profiles.RadialSheetPhases
public import DedekindZetaZeroFree.Theta.Whittaker.FourierPeriodRegularity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources KPGlobalResidualConstruction KPAdelicCoverRestrictedProduct
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

theorem localIdele_eval_arch (y : R.A.G) (w : InfinitePlace F) :
    Units.map (adeleEval F (Sum.inl w)) (localIdele R y) = y.1 w := by
  have h : Units.map (adeleEval F (Sum.inl w)).toMonoidHom (localIdele R y) = y.1 w := by
    unfold localIdele
    simp only [map_mul, map_prod]
    have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
        Units.map (adeleEval F (Sum.inl w)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
          Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inl w) := by
      apply Units.ext
      exact congrArg Units.val (eval_localIdele F p (Sum.inl w) z)
    simp only [he]
    have hf : (∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
        (Sum.inr p.val) (y.2 p) (Sum.inl w)) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      exact Pi.mulSingle_eq_of_ne (by simp) _
    rw [hf, mul_one, Finset.prod_eq_single w]
    · simp
    · intro b hb hbw
      exact Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne hbw.symm) _
    · simp
  exact congrArg Units.val h |> Units.ext

theorem localIdele_eval_finite (y : R.A.G) (q : KPFinitePlace F) :
    Units.map (adeleEval F (Sum.inr q)) (localIdele R y) =
      ∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
        (Sum.inr p.val) (y.2 p) (Sum.inr q) := by
  have h : Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R y) =
      ∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
        (Sum.inr p.val) (y.2 p) (Sum.inr q) := by
    unfold localIdele
    simp only [map_mul, map_prod]
    have he (p : KPHilbert.Place F) (z : (KPHilbert.Completion F p)ˣ) :
        Units.map (adeleEval F (Sum.inr q)).toMonoidHom (KPRationalAdelicSplitting.localIdele F p z) =
          Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) p z (Sum.inr q) := by
      apply Units.ext
      exact congrArg Units.val (eval_localIdele F p (Sum.inr q) z)
    simp only [he]
    simp
  exact congrArg Units.val h |> Units.ext

def uniformCoordinates (_R : PrincipalMellin.ActualRecipe S η) (t : ℝ) : ArchCoordinates F :=
  fun _ i => if i = 1 then (Real.exp (t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) else 0

theorem uniformCoordinates_smooth : ContDiff ℝ (⊤ : ℕ∞) (uniformCoordinates R) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 1
  · simp only [uniformCoordinates, hi, ↓reduceIte]
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const _))
  · simp only [uniformCoordinates, hi, ↓reduceIte]
    exact contDiff_const

theorem uniformCoordinates_mem (t : ℝ) : uniformCoordinates R t ∈ archDomain F := by
  intro w
  simp only [uniformCoordinates, ↓reduceIte]
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem radial_arch_value (t : ℝ) (w : InfinitePlace F) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w))
      ((R.A.radialSection (Real.exp t) (Real.exp_pos t)).1 w : w.Completion) =
        (Real.exp (t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) := by
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex _)
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex _).symm _) = _
  simp only [RingEquiv.apply_symm_apply, Units.val_mk0]
  congr 1
  rw [← Real.exp_mul]
  congr 1
  ring

theorem diagonal_uniform_radial (y : R.A.G) (t : ℝ) :
    diagonal R (y * R.A.radialSection (Real.exp t) (Real.exp_pos t)) =
      diagonal R y * archChart F R.A.zeta12 R.A.primitive_zeta12 (uniformCoordinates R t) := by
  unfold diagonal KPRationalAdelicSplitting.pglA KPRationalAdelicSplitting.A archChart
  rw [← map_mul, ← map_mul]
  apply congrArg (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  apply RestrictedProduct.ext
  intro p
  cases p with
  | inl w =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
      (Units.map (adeleEval F (Sum.inl w)) (localIdele R _)) =
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
          (Units.map (adeleEval F (Sum.inl w)) (localIdele R y)) *
          (KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
            ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm (uniformCoordinates R t w 0)) *
          KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
            (if h : uniformCoordinates R t w 1 = 0 then 1 else Units.mk0
              ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
                (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm (uniformCoordinates R t w 1)) _) *
          KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)
            ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).symm (uniformCoordinates R t w 2)))
    rw [localIdele_eval_arch, localIdele_eval_arch]
    have hne : (Real.exp (t / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    simp only [Prod.fst_mul, Pi.mul_apply, uniformCoordinates, ↓reduceIte,
      show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, map_zero,
      KPStandardLocalRootLifts.N_zero, KPStandardLocalRootLifts.LowerN_zero, one_mul, mul_one,
      dif_neg hne]
    rw [KPStandardLocalRootLifts.A_mul]
    simp only [KPHilbert.B3, KPHilbert.B6_infinite, map_one, one_pow, one_mul]
    congr 1
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    congr 1
    exact (RingEquiv.eq_symm_apply _).mpr (radial_arch_value R t w)
  | inr q =>
    change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
      (Units.map (adeleEval F (Sum.inr q)) (localIdele R _)) =
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
          (Units.map (adeleEval F (Sum.inr q)) (localIdele R y)) * 1
    rw [localIdele_eval_finite, localIdele_eval_finite, mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    congr 1
    change y.2 p * 1 = y.2 p
    exact mul_one _

theorem localIdele_eval_continuous (v : KPHilbert.Place F) :
    Continuous (fun y : R.A.G => Units.map (adeleEval F v).toMonoidHom (localIdele R y)) := by
  cases v with
  | inl w =>
    have he : (fun y : R.A.G => Units.map (adeleEval F (Sum.inl w)).toMonoidHom (localIdele R y)) =
        (fun y => y.1 w) := funext (fun y => localIdele_eval_arch R y w)
    rw [he]
    exact (continuous_apply w).comp continuous_fst
  | inr q =>
    have he : (fun y : R.A.G => Units.map (adeleEval F (Sum.inr q)).toMonoidHom (localIdele R y)) =
        (fun y => ∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
          (Sum.inr p.val) (y.2 p) (Sum.inr q)) := funext (fun y => localIdele_eval_finite R y q)
    rw [he]
    apply continuous_finset_prod
    intro p hp
    exact ((continuous_apply (Sum.inr q)).comp (continuous_mulSingle (Sum.inr p.val))).comp
      ((continuous_apply p).comp continuous_snd)

theorem diagonal_continuous : Continuous (diagonal R) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :=
    localTopology F R.A.zeta12 R.A.primitive_zeta12
  let U : Set (KPHilbert.Place F) := {v | match v with
    | .inl _ => False
    | .inr q => q ∉ R.A.Sf}
  have hU : Filter.cofinite ≤ Filter.principal U := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ U
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [U] using R.A.Sf.finite_toSet⟩
  have hm (y : R.A.G) (v : KPHilbert.Place F) (hv : v ∈ U) :
      KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y) v ∈
        compact F R.A.zeta12 R.A.primitive_zeta12 v := by
    cases v with
    | inl w => exact False.elim hv
    | inr q =>
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (Units.map (adeleEval F (Sum.inr q)) (localIdele R y)) ∈ _
      rw [localIdele_eval_finite]
      have he : (∏ p : R.A.Sf, Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ)
          (Sum.inr p.val) (y.2 p) (Sum.inr q)) = 1 := by
        apply Finset.prod_eq_one
        intro p hp
        exact Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne (by
          intro h; exact hv (h.symm ▸ p.property))) _
      rw [he, KPStandardLocalRootLifts.A_one]
      exact (compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)).one_mem
  let f : R.A.G → RestrictedProduct
      (fun v => KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v)
      (fun v => (compact F R.A.zeta12 R.A.primitive_zeta12 v : Set _)) (Filter.principal U) :=
    fun y => ⟨KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y), hm y⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    have ha : Continuous (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v) := by
      cases v with
      | inl w => exact KPStandardLocalRootLifts.complex_A_continuous F R.A.zeta12 R.A.primitive_zeta12 w
      | inr q =>
        exact KPStandardLocalRootLifts.finite_A_continuous F R.A.zeta12 R.A.primitive_zeta12 q
          (depth F R.A.zeta12 R.A.primitive_zeta12 q)
          (depth_admissible F R.A.zeta12 R.A.primitive_zeta12 q)
    exact ha.comp (localIdele_eval_continuous R v)
  exact QuotientGroup.continuous_mk.comp
    (QuotientGroup.continuous_mk.comp ((RestrictedProduct.continuous_inclusion hU).comp hf))
end DedekindZetaZeroFree.SheetRescaling

end
