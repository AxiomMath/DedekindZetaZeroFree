module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.Metaplectic.Torus.ArchimedeanChartCharacter
public import DedekindZetaZeroFree.Metaplectic.Torus.ClosednessAndNormChartFormula

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.ArchValue
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open _root_.DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality renaming arch_center → arch_center

theorem source_arch_character (z : KPGlobalTorusFunctionData.TorusArch F) :
    ∃ r : KPGlobalCenterRationalCharacter.R F ζ hζ,
      r.val = KPGlobalTorusFunctionData.torusArchChart F ζ hζ z ∧
      KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r =
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ r.val) := by
  obtain ⟨c, hc, hχ⟩ := arch_center F ζ hζ z
  let r : KPGlobalCenterRationalCharacter.R F ζ hζ :=
    ⟨c.val, Subgroup.mem_sup_right c.property⟩
  refine ⟨r, hc, ?_⟩
  rw [KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ r 1 c (by simp [r])]
  exact hχ

theorem actual_arch_single_diagonal (w : InfinitePlace F) (y : ℂˣ) :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
      (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) =
      KPRationalAdelicSplitting.pglA F ζ hζ
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w)
          (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y)) := by
  unfold KPGlobalTorusFunctionData.archDiagonalLift KPRationalAdelicSplitting.pglA
    KPRationalAdelicSplitting.A
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inl u =>
    by_cases hu : u = w
    · subst u
      simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
        KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
        KPAdelicCoverRestrictedProduct.adeleEval, y.ne_zero]
      congr 1
      apply Units.ext
      change (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ) =
          Pi.mulSingle w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) w
      simp
    · simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
        KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
        KPAdelicCoverRestrictedProduct.adeleEval, hu]
      rw [← KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inl u)]
      congr 1
      apply Units.ext
      change 1 = Pi.mulSingle w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) u
      simp [hu]
  | inr q =>
    simp [KPGlobalTorusFunctionData.archDiagonalTuple, KPRationalAdelicSplitting.ATuple,
      KPRationalAdelicSplitting.ACoordinates, KPRationalAdelicSplitting.localIdele,
      KPAdelicCoverRestrictedProduct.adeleEval]
    rw [← KPStandardLocalRootLifts.A_one F ζ hζ (Sum.inr q)]
    congr 1

theorem literal_arch_borel_covariance
    (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ)
    (z : KPGlobalTorusFunctionData.TorusArch F)
    (hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F)
    (x : KPAdeles F) (g : KPLiteralRaw.G F ζ hζ) :
    f.val s (((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalExceptionalParameter.realLogPower
        (∏ w : InfinitePlace F, ‖z w‖ ^ 2) (2 / 3 + s) * f.val s g := by
  obtain ⟨r, hr, hχ⟩ := source_arch_character F ζ hζ z
  have hc := (f.property.1 s).2 r x g
  rw [hr] at hc
  rw [hc, hχ]
  have hd : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hν : (KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.nu F ζ hζ r.val) : ℂ) =
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : ℝ≥0) : ℝ) ^ (1 / 6 : ℝ) : ℝ) := by
    simp [KPGlobalCenterRationalCharacter.positiveComplex, KPGlobalCenterRationalCharacter.nu,
      KPGlobalCenterRationalCharacter.sixthPower]
  rw [hν, Real.rpow_def_of_pos hd, Complex.ofReal_exp]
  have hδ := KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz
  rw [← hr] at hδ
  rw [← hδ]
  unfold KPGlobalExceptionalParameter.realLogPower
  rw [← hr, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem literal_single_arch_borel_covariance
    (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ)
    (w : InfinitePlace F) (y : ℂˣ) (g : KPLiteralRaw.G F ζ hζ) :
    f.val s (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
      (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) * g) =
      KPGlobalExceptionalParameter.realLogPower (‖(y : ℂ)‖ ^ 2) (2 / 3 + s) *
        f.val s g := by
  have hz : Function.update (fun _ => (1 : ℂ)) w (y : ℂ) ∈
      KPGlobalTorusFunctionData.torusArchDomain F := by
    intro u
    by_cases hu : u = w
    · subst u; simp [y.ne_zero]
    · simp [Function.update_of_ne hu]
  have hc := literal_arch_borel_covariance F ζ hζ K f s _ hz 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hp : (∏ u : InfinitePlace F,
      ‖Function.update (fun _ => (1 : ℂ)) w (y : ℂ) u‖ ^ 2) = ‖(y : ℂ)‖ ^ 2 := by
    rw [Finset.prod_eq_single w]
    · simp
    · intro u _ hu
      simp [Function.update_of_ne hu]
    · simp
  simpa only [KPGlobalTorusFunctionData.torusArchChart, hn, mul_one, hp] using hc

theorem literal_single_arch_weyl_value
    (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (f : KPLiteralRaw.Flat F ζ hζ K) (s : ℂ)
    (w : InfinitePlace F) (y : ℂˣ) (x : KPAdeles F) (g : KPLiteralRaw.G F ζ hζ) :
    f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ x *
      (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) * g)) =
      KPGlobalExceptionalParameter.realLogPower (‖(y : ℂ)‖ ^ 2) (-2 / 3 - s) *
        f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
          KPGlobalTorusFunctionData.N F ζ hζ
            (x * (↑((KPRationalAdelicSplitting.localIdele F (Sum.inl w)
              (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
                (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y))⁻¹) :
                KPAdeles F)) * g) := by
  let a := KPRationalAdelicSplitting.localIdele F (Sum.inl w)
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y)
  have ha := actual_arch_single_diagonal F ζ hζ w y
  have hn := KPRationalAdelicSplitting.quotient_upper_diagonal F ζ hζ x a
  change KPGlobalTorusFunctionData.N F ζ hζ x * KPRationalAdelicSplitting.pglA F ζ hζ a =
    KPRationalAdelicSplitting.pglA F ζ hζ a *
      KPGlobalTorusFunctionData.N F ζ hζ (x * (↑a⁻¹ : KPAdeles F)) at hn
  have ht : KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ x *
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) =
      KPRationalAdelicSplitting.pglA F ζ hζ a⁻¹ *
        (KPRationalAdelicSplitting.pglW F ζ hζ *
          KPGlobalTorusFunctionData.N F ζ hζ (x * (↑a⁻¹ : KPAdeles F))) := by
    rw [ha]
    change _ * _ * KPRationalAdelicSplitting.pglA F ζ hζ a = _
    rw [mul_assoc, hn, ← mul_assoc,
      KPRationalAdelicSplitting.quotient_weyl_diagonal, mul_assoc]
  rw [← mul_assoc, ht, mul_assoc]
  have hai : KPRationalAdelicSplitting.pglA F ζ hζ a⁻¹ =
      KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
        (Function.update (fun _ => (1 : ℂ)) w (↑(y⁻¹) : ℂ)) := by
    have hh := actual_arch_single_diagonal F ζ hζ w y⁻¹
    simpa only [a, KPRationalAdelicSplitting.localIdele, map_inv] using hh.symm
  rw [hai, literal_single_arch_borel_covariance]
  congr 1
  have hi : ‖((y⁻¹ : ℂˣ) : ℂ)‖ ^ 2 = (‖(y : ℂ)‖ ^ 2)⁻¹ := by
    simp [norm_inv, inv_pow]
  rw [hi]
  unfold KPGlobalExceptionalParameter.realLogPower
  rw [Real.log_inv]
  congr 1
  push_cast
  ring
end DedekindZetaZeroFree.CompactPeriodAnalyticity.ArchValue

end
