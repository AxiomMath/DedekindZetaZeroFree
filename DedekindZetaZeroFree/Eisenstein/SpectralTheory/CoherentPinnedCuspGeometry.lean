module

public import DedekindZetaZeroFree.Metaplectic.Torus.StandardDiagonalIdeleLifts
public import DedekindZetaZeroFree.Adeles.Characters.PositiveArchimedeanHaarCharacter
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspDisintegration.RadialRescaling

@[expose] public section

section

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPMsFixedHaar.ActualRadialSection
open KPContinuation.ChamberOutgoingSource
open _root_.DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource renaming archSlot → archSlot
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 def logarithmicSlots (w : InfinitePlace F) (r : Radius) : InfinitePlace F → ℝ :=
  fun v => if v = w then Real.log r.val / 2 else 0
 def ell (w : InfinitePlace F) (r : Radius) : KPGlobalTorusFunctionData.Ideles F :=
  archDiagonalIdele F ζ hζ (logarithmicSlots F w r)
private theorem exp_log_half (r : Radius) : Real.exp (Real.log r.val / 2) = Real.sqrt r.val := by
  have he : Real.exp (Real.log r.val / 2) ^ 2 = r.val := by
    rw [← Real.exp_nat_mul]
    convert Real.exp_log r.property using 1
    congr 1
    ring
  have hs := Real.sq_sqrt r.property.le
  nlinarith [Real.exp_pos (Real.log r.val / 2), Real.sqrt_nonneg r.val]
omit [NumberField F] in
private theorem exp_slots (w v : InfinitePlace F) (r : Radius) :
    (Real.exp (logarithmicSlots F w r v) : ℂ) = positiveSlots F w r v := by
  by_cases hv : v = w
  · simp [logarithmicSlots, positiveSlots, hv, exp_log_half]
  · simp [logarithmicSlots, positiveSlots, hv]
private theorem archSlot_continuous : Continuous (archSlot F ζ hζ) := by
  apply continuous_pi_iff.mpr
  intro w
  apply Units.continuous_iff.mpr
  have he := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm.continuous
  constructor
  · exact he.comp (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply w)))
  · change Continuous (fun u : InfinitePlace F → ℝ =>
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm ((Real.exp (u w) : ℂ)⁻¹))
    simp_rw [← Complex.ofReal_inv, ← Real.exp_neg]
    exact he.comp (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_apply w).neg))
private theorem archIdele_continuous : Continuous (archDiagonalIdele F ζ hζ) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact ((continuous_pi fun w => Units.continuous_val.comp
      ((continuous_pi_iff.mp (archSlot_continuous F ζ hζ)) w)).prodMk continuous_const)
  · change Continuous (fun u : InfinitePlace F → ℝ =>
      (((fun w => ((archSlot F ζ hζ u w)⁻¹).val),1) : KPGlobalTorusFunctionData.Adeles F))
    exact ((continuous_pi fun w => Units.continuous_val.comp
      (continuous_inv.comp ((continuous_pi_iff.mp (archSlot_continuous F ζ hζ)) w))).prodMk continuous_const)
omit [NumberField F] in
private theorem logarithmicSlots_continuous (w : InfinitePlace F) :
    Continuous (logarithmicSlots F w) := by
  apply continuous_pi
  intro v
  by_cases hv : v = w
  · simp only [logarithmicSlots, hv, ↓reduceIte]
    exact (continuous_subtype_val.log (fun r => r.property.ne')).div_const 2
  · simp only [logarithmicSlots, hv, ↓reduceIte]
    exact continuous_const
 theorem ell_continuous (w : InfinitePlace F) : Continuous (ell F ζ hζ w) :=
  (archIdele_continuous F ζ hζ).comp (logarithmicSlots_continuous F w)
private theorem archIdele_add (u v : InfinitePlace F → ℝ) :
    archDiagonalIdele F ζ hζ (u + v) = archDiagonalIdele F ζ hζ u * archDiagonalIdele F ζ hζ v := by
  apply Units.ext
  apply Prod.ext
  · funext w
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w + v w) : ℂ) = _
    rw [Real.exp_add, Complex.ofReal_mul, map_mul]
    rfl
  · exact (one_mul _).symm
private theorem archIdele_zero : archDiagonalIdele F ζ hζ 0 = 1 := by
  apply Units.ext
  apply Prod.ext
  · funext w
    change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp 0 : ℂ) = 1
    simp
  · rfl
 theorem ell_one (w : InfinitePlace F) : ell F ζ hζ w ⟨1,by norm_num⟩ = 1 := by
  unfold ell
  rw [show logarithmicSlots F w ⟨1,by norm_num⟩ = 0 by ext; simp [logarithmicSlots],archIdele_zero]
 theorem ell_mul (w : InfinitePlace F) (r s : Radius) :
    ell F ζ hζ w ⟨r.val*s.val,mul_pos r.property s.property⟩ = ell F ζ hζ w r * ell F ζ hζ w s := by
  unfold ell
  rw [show logarithmicSlots F w ⟨r.val*s.val,mul_pos r.property s.property⟩ =
      logarithmicSlots F w r + logarithmicSlots F w s by
    ext v; simp only [logarithmicSlots, Pi.add_apply, Real.log_mul r.property.ne' s.property.ne']
    split_ifs <;> ring, archIdele_add]
 theorem ell_cube (w : InfinitePlace F) (r : Radius) :
    ∃ u : KPGlobalTorusFunctionData.Ideles F, u^3 = ell F ζ hζ w r := by
  refine ⟨archDiagonalIdele F ζ hζ (fun v => logarithmicSlots F w r v / 3),?_⟩
  rw [pow_succ,pow_two,← archIdele_add,← archIdele_add]
  congr 1
  ext v
  simp only [Pi.add_apply]
  ring
 theorem ell_slots (w : InfinitePlace F) (r : Radius) (v : InfinitePlace F) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl v) (ell F ζ hζ w r : KPAdeles F) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ v)).symm (positiveSlots F w r v) := by
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ v)).symm
      (Real.exp (logarithmicSlots F w r v) : ℂ) = _
  rw [exp_slots]
 theorem ell_norm (w : InfinitePlace F) (r : Radius) :
    ((KPGlobalTorusFunctionData.ideleAbs F (ell F ζ hζ w r) : ℝ≥0) : ℝ) = r.val := by
  rw [ell,KPGlobalResidualConstruction.PositiveArchCharacter.archDiagonalIdele_ideleAbs]
  simp only [logarithmicSlots, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  convert Real.exp_log r.property using 1
  congr 1
  ring
 theorem ell_finite (w : InfinitePlace F) (r : Radius) (q : HeightOneSpectrum (𝓞 F)) :
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr q) (ell F ζ hζ w r : KPAdeles F) = 1 := by
  rfl
 theorem lift_ratio (w : InfinitePlace F) (r : Radius) :
    KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (positiveSlots F w r)) = ell F ζ hζ w r := by
  have he (v : KPHilbert.Place F) :
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (positiveSlots F w r) v =
        KPStandardLocalRootLifts.A F ζ hζ v
          (KPGlobalCubicIdelePairing.ideleEval F v (ell F ζ hζ w r)) := by
    cases v with
    | inl v =>
      have hn : positiveSlots F w r v ≠ 0 := by
        by_cases hv : v = w
        · simpa [positiveSlots, hv] using
            (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr r.property))
        · simp [positiveSlots, hv]
      change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl v)
        (if h : positiveSlots F w r v = 0 then 1 else
          Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ v)).symm (positiveSlots F w r v)) _) = _
      rw [dite_eq_right hn]
      congr 1
      apply Units.ext
      simp only [KPGlobalCubicIdelePairing.ideleEval, Units.val_mk0]
      exact (ell_slots F ζ hζ w r v).symm
    | inr q =>
      change 1 = KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) 1
      rw [KPStandardLocalRootLifts.A_one]
  obtain ⟨t, ht, hp⟩ :=
    KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.standard_diagonal_torus_ratio
      F ζ hζ (ell F ζ hζ w r)
      (KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (positiveSlots F w r)) he
  have hh : t = KPGlobalTorusFunctionData.torusArchChart F ζ hζ (positiveSlots F w r) := Subtype.ext ht
  exact hh ▸ hp
private theorem archTuple_continuous :
    Continuous (fun u : InfinitePlace F → ℝ =>
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun v => (Real.exp (u v) : ℂ))) := by
  let := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  let S : Set (KPHilbert.Place F) := Set.range Sum.inr
  let f : (InfinitePlace F → ℝ) → RestrictedProduct
      (KPLocalCover.CubicGL2Raw F ζ hζ) (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) := fun u =>
    ⟨(KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun v => (Real.exp (u v) : ℂ))).val,
      Filter.eventually_principal.mpr (by rintro v ⟨q,rfl⟩; exact Subgroup.one_mem _)⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro v
    cases v with
    | inl v =>
      change Continuous (fun u : InfinitePlace F → ℝ =>
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl v)
          (if h : (Real.exp (u v) : ℂ) = 0 then 1 else
            Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm (Real.exp (u v) : ℂ)) _))
      have he : (fun u : InfinitePlace F → ℝ =>
        (if h : (Real.exp (u v) : ℂ) = 0 then (1 : v.Completionˣ) else
            Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm (Real.exp (u v) : ℂ))
              ((map_ne_zero _).mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))))) =
          fun u => archSlot F ζ hζ u v := by
        funext u
        simp only [Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _), ↓reduceDIte]
        apply Units.ext
        rfl
      simp_rw [show ∀ u, (if h : (Real.exp (u v) : ℂ) = 0 then (1 : v.Completionˣ) else
            Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (KPHilbert.infinite_isComplex F ζ hζ v)).symm (Real.exp (u v) : ℂ))
              ((map_ne_zero _).mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))) =
            archSlot F ζ hζ u v from fun u => congrFun he u]
      exact (KPStandardLocalRootLifts.complex_A_continuous F ζ hζ v).comp
        (continuous_pi_iff.mp (archSlot_continuous F ζ hζ) v)
    | inr q => exact continuous_const
  have hs : Filter.cofinite ≤ Filter.principal S := by
    apply Filter.le_principal_iff.mpr
    apply Filter.mem_cofinite.mpr
    have he : Sᶜ = Set.range Sum.inl := by ext v; cases v <;> simp [S]
    rw [he]
    exact Set.finite_range _
  exact (RestrictedProduct.continuous_inclusion hs).comp hf
 theorem section_continuous (w : InfinitePlace F) :
    Continuous (radialSection F ζ hζ w) := by
  have hq : Continuous ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)) :=
    QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk
  have he : radialSection F ζ hζ w = fun r =>
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun v => (Real.exp (logarithmicSlots F w r v) : ℂ)) := by
    funext r
    unfold radialSection
    congr 1
    funext v
    exact (exp_slots F w v r).symm
  rw [he]
  exact hq.comp ((archTuple_continuous F ζ hζ).comp (logarithmicSlots_continuous F w))
open _root_.DedekindZetaZeroFree.KPStandardLocalRootLifts renaming d_mul_matrix → d_mul_matrix
private theorem archTuple_add (u v : InfinitePlace F → ℝ) :
    KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (Real.exp ((u+v) w) : ℂ)) =
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (Real.exp (u w) : ℂ)) *
        KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (Real.exp (v w) : ℂ)) := by
  apply RestrictedProduct.ext
  intro w
  cases w with
  | inl w =>
    have he (t : InfinitePlace F → ℝ) :
        KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (Real.exp (t w) : ℂ)) (Sum.inl w) =
          KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) (archSlot F ζ hζ t w) := by
      change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : (Real.exp (t w) : ℂ) = 0 then 1 else
          Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (t w) : ℂ)) _) = _
      simp only [Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _), ↓reduceDIte]
      congr 1
      apply Units.ext
      rfl
    change _ = KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ _ (Sum.inl w) *
      KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ _ (Sum.inl w)
    rw [he,he,he]
    have hs : archSlot F ζ hζ (u+v) w = archSlot F ζ hζ u w * archSlot F ζ hζ v w := by
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (Real.exp (u w+v w) : ℂ) = _
      rw [Real.exp_add,Complex.ofReal_mul,map_mul]
      rfl
    rw [hs]
    unfold KPStandardLocalRootLifts.A
    rw [KPLocalCover.sectionMap_mul,KPLocalChartTopology.complex_sigmaTwo_eq_one,
      map_one,one_mul,d_mul_matrix]
  | inr q =>
    change (1 : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) = 1*1
    rw [one_mul]
private theorem archLift_add (u v : InfinitePlace F → ℝ) :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (Real.exp ((u+v) w) : ℂ)) =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (Real.exp (u w) : ℂ)) *
        KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (Real.exp (v w) : ℂ)) := by
  simp only [KPGlobalTorusFunctionData.archDiagonalLift,archTuple_add,map_mul]
private theorem archLift_zero :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun _ => (1 : ℂ)) = 1 := by
  have he : KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun _ => (1 : ℂ)) = 1 := by
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : (1 : ℂ) = 0 then 1 else
          Units.mk0 ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm 1) _) = 1
      simp only [one_ne_zero, ↓reduceDIte,map_one, Units.mk0_one,KPStandardLocalRootLifts.A_one]
    | inr q => rfl
  simp only [KPGlobalTorusFunctionData.archDiagonalLift,he,map_one]
 theorem section_one (w : InfinitePlace F) :
    radialSection F ζ hζ w ⟨1,by norm_num⟩ = 1 := by
  change KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (positiveSlots F w ⟨1,by norm_num⟩) = 1
  rw [show positiveSlots F w ⟨1,by norm_num⟩ = fun _ => (1 : ℂ) by ext; simp [positiveSlots],archLift_zero]
 theorem section_mul (w : InfinitePlace F) (r s : Radius) :
    radialSection F ζ hζ w ⟨r.val*s.val,mul_pos r.property s.property⟩ =
      radialSection F ζ hζ w r * radialSection F ζ hζ w s := by
  have he (t : Radius) : radialSection F ζ hζ w t =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (fun v => (Real.exp (logarithmicSlots F w t v) : ℂ)) := by
    unfold radialSection
    congr 1
    ext v
    exact (exp_slots F w v t).symm
  rw [he,he,he]
  rw [show logarithmicSlots F w ⟨r.val*s.val,mul_pos r.property s.property⟩ =
      logarithmicSlots F w r + logarithmicSlots F w s by
    ext v; simp only [logarithmicSlots, Pi.add_apply, Real.log_mul r.property.ne' s.property.ne']
    split_ifs <;> ring]
  exact archLift_add F ζ hζ _ _

def radialData (w : InfinitePlace F) : RadialData F ζ hζ where
  slot := w
  ell := ell F ζ hζ w
  continuous_ell := ell_continuous F ζ hζ w
  ell_one := ell_one F ζ hζ w
  ell_mul := ell_mul F ζ hζ w
  ell_cube := ell_cube F ζ hζ w
  ell_slots := ell_slots F ζ hζ w
  ell_finite := ell_finite F ζ hζ w
  ell_norm := ell_norm F ζ hζ w
  lift_ratio := lift_ratio F ζ hζ w
  continuous_section := section_continuous F ζ hζ w
  section_one := section_one F ζ hζ w
  section_mul := section_mul F ζ hζ w
@[simp] theorem radialData_slot (w : InfinitePlace F) : (radialData F ζ hζ w).slot = w := rfl

end DedekindZetaZeroFree.KPMsFixedHaar.ActualRadialSection

end

end

section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

open _root_.DedekindZetaZeroFree.KPMsFixedHaar.FixedLevelGeometry renaming actual_fixed_level_geometry → actual_fixed_level_geometry
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.RadiusShift.Globalization renaming exists_actual_compatibility_laws → exists_actual_compatibility_laws

namespace DedekindZetaZeroFree.KPMsFixedHaar.ActualAllLevels

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def atlas (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Level F ζ hζ) : KPFiniteCuspAtlas.Atlas F ζ hζ hF U :=
  Classical.choice (by
    obtain ⟨hF', _, hA⟩ := kp_cont_finite_cusp_atlas F ζ hζ U
    exact hA)

theorem exists_geometry
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (kernels : ∀ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
      (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U), FiberKernel A) :
    ∃ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (B : RadialData F ζ hζ)
      (D : ∀ U, GeometricDisintegration (atlas F ζ hζ hF U) R P),
      (∀ U, (D U).radial = B) ∧
      (∀ U, (D U).toFiberKernel = kernels hF U (atlas F ζ hζ hF U)) := by
  letI := primitive12_totallyComplex F ζ hζ
  let hF := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero F
  let B := ActualRadialSection.radialData F ζ hζ
    (Classical.arbitrary (NumberField.InfinitePlace F))
  have hD := fun U : Level F ζ hζ => actual_fixed_level_geometry
    (atlas F ζ hζ hF U) R P B (kernels hF U (atlas F ζ hζ hF U))
  choose D hrad hkernel using hD
  exact ⟨hF, B, D, hrad, hkernel⟩

theorem exists_geometry_and_actual_transport
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (kernels : ∀ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
      (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U), FiberKernel A) :
    ∃ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) (B : RadialData F ζ hζ)
      (D : ∀ U, GeometricDisintegration (atlas F ζ hζ hF U) R P),
      (∀ U, (D U).radial = B) ∧
      (∀ U, (D U).toFiberKernel = kernels hF U (atlas F ζ hζ hF U)) ∧
      (∀ U, RadialIntegration (atlas F ζ hζ hF U) R P (D U)) ∧
      ∀ (V U : Level F ζ hζ)
        (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup),
      let AV := atlas F ζ hζ hF V
      let AU := atlas F ζ hζ hF U
      ∃ (l : CuspIndex AV → CuspIndex AU) (rho : CuspIndex AV → Radius)
        (c : CrossSection AV → CrossSection AU) (a : Omega AV → Omega AU),
        Measurable c ∧ Measurable a ∧
        (∀ x, (c x).1 = l x.1) ∧ (∀ ω, (a ω).1 = l ω.1) ∧
        (∀ x, angularProjection AU (c x) = a (angularProjection AV x)) ∧
        (Measure.map a ((D V).beta.withDensity
          (fun ω => ENNReal.ofReal (rho ω.1).val)) = (D U).beta) ∧
        (Measure.map a (probability AV ((D V).beta.withDensity
          (fun ω => ENNReal.ofReal (rho ω.1).val))) = probability AU (D U).beta) ∧
        (kappa AU R P (D U) = (((D V).beta.withDensity
          (fun ω => ENNReal.ofReal (rho ω.1).val)) Set.univ).toReal) ∧
        ((D V).radial.slot = (D U).radial.slot) ∧
        (∀ f : CrossSection AU → ℝ≥0∞, Measurable f →
          (∫⁻ ω, ENNReal.ofReal (rho ω.1).val *
            ∫⁻ x, f (c x) ∂(D V).unipotent ω ∂(D V).beta) =
            ∫⁻ ω, ∫⁻ x, f x ∂(D U).unipotent ω ∂(D U).beta) ∧
        (∀ YV YU (hV : AdmissibleCutoff AV YV) (hU : AdmissibleCutoff AU YU)
          (x : CrossSection AV) (r : Set.Ioi YV) (hr : YU < (rho x.1).val * r.val),
          P.forget V U h ((D V).chart YV hV (x,r)) =
            (D U).chart YU hU (c x,⟨(rho x.1).val * r.val,hr⟩)) := by
  obtain ⟨hF, B, D, hrad, hk⟩ := exists_geometry F ζ hζ R P kernels
  refine ⟨hF, B, D, hrad, hk,
    fun U => fixed_haar_radial_integration (atlas F ζ hζ hF U) R P (D U), ?_⟩
  intro V U h
  have hslot : (D V).radial.slot = (D U).radial.slot := by rw [hrad V, hrad U]
  obtain ⟨l,rho,c,a,hc,ha,hcl,hal,hcomm,hbeta,hprob,hcoeff,hkernel,hchart⟩ :=
    exists_actual_compatibility_laws R P h (D V) (D U) hslot
  exact ⟨l,rho,c,a,hc,ha,hcl,hal,hcomm,hbeta,hprob,hcoeff,hslot,hkernel,hchart⟩

end DedekindZetaZeroFree.KPMsFixedHaar.ActualAllLevels

namespace DedekindZetaZeroFree.KPMsFixedHaar

theorem coherent_cusp_geometry
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ)
    (kernels : ∀ (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
      (U : Level F ζ hζ) (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U), FiberKernel A) :
    ∃ D : AllLevels F ζ hζ R P,
      ∀ U, (D.disintegration U).toFiberKernel = kernels D.totallyComplex U (D.atlas U) := by
  obtain ⟨hF, B, D, hrad, hk, hRI, hcompat⟩ :=
    ActualAllLevels.exists_geometry_and_actual_transport F ζ hζ R P kernels
  let L : AllLevels F ζ hζ R P := {
    totallyComplex := hF
    atlas := ActualAllLevels.atlas F ζ hζ hF
    disintegration := D
    compatible := by
      intro V U h
      obtain ⟨l, rho, c, a, hc, ha, hcl, hal, hcomm, hbeta, hprob,
        hcoeff, hslot, hkernel, hchart⟩ := hcompat V U h
      exact ⟨{
        cuspForget := l
        radiusScale := rho
        angularForget := a
        measurable_angularForget := ha
        angular_label := hal
        crossForget := c
        measurable_crossForget := hc
        cross_label := hcl
        projection_commutes := hcomm
        induced_angular := hbeta
        induced_probability := hprob
        coefficient := hcoeff
        common_slot := hslot
        chart_commutes := hchart
        induced_kernel := hkernel }⟩ }
  exact ⟨L, hk⟩

end DedekindZetaZeroFree.KPMsFixedHaar

end

end
