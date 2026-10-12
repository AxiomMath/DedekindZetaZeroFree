module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanBorelAndWeylValues
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArchimedeanIdeleDilation

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.WeylIntegral
open KPLiteralRaw ArchValue

private theorem single_arch_norm (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F) (y : ℂˣ) :
    let a := KPRationalAdelicSplitting.localIdele F (Sum.inl w)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y)
    ‖a.val.1‖ = ‖(y : ℂ)‖ ^ 2 := by
  dsimp
  rw [InfiniteAdeleRing.norm_def, Finset.prod_eq_single w]
  · simp [KPRationalAdelicSplitting.localIdele]
    rw [(KPHilbert.infinite_isComplex F ζ hζ w).mult_eq_two]
    congr 1
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have he := e.isometry.dist_eq
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) 0
    have he0 : e 0 = 0 := (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).map_zero
    have hey : e ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm (y : ℂ)) = (y : ℂ) :=
      RingEquiv.apply_symm_apply _ _
    simpa only [he0, hey, dist_zero_right] using he.symm
  · intro u _ hu
    simp [KPRationalAdelicSplitting.localIdele, hu]
  · simp

theorem literal_weyl_integral_weight
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ)
    (w : InfinitePlace F) (g : G F ζ hζ) (y : ℂˣ)
    (hi : Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g))
      (KPAdditiveHaar.adelicMeasure F))
    (_hia : Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) * g)))
      (KPAdditiveHaar.adelicMeasure F)) :
    (∫ x : KPAdeles F, f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) * g))
      ∂KPAdditiveHaar.adelicMeasure F) =
    KPGlobalExceptionalParameter.realLogPower (‖(y : ℂ)‖ ^ 2) (1 / 3 - s) *
      ∫ x : KPAdeles F, f.val s
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ∂KPAdditiveHaar.adelicMeasure F := by
  letI := KPAdditiveHaar.adelicMeasure_isAddHaarMeasure F
  let a := KPRationalAdelicSplitting.localIdele F (Sum.inl w)
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toMonoidHom y)
  have ha : a.val.2 = 1 := by simp [a, KPRationalAdelicSplitting.localIdele]
  have hnorm := single_arch_norm F ζ hζ w y
  have h := ArchHaar.arch_idele_integral_mul_inv
    (KPAdditiveHaar.adelicMeasure F) a ha
    (fun x => f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ x * g)) hi
  rw [hnorm] at h
  simp_rw [literal_single_arch_weyl_value F ζ hζ K f s w y]
  rw [integral_const_mul, h, ← mul_assoc]
  congr 1
  have hp : 0 < ‖(y : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr y.ne_zero) _
  have he : ((‖(y : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      KPGlobalExceptionalParameter.realLogPower (‖(y : ℂ)‖ ^ 2) 1 := by
    unfold KPGlobalExceptionalParameter.realLogPower
    rw [one_mul, ← Complex.ofReal_exp, Real.exp_log hp]
  rw [he]
  unfold KPGlobalExceptionalParameter.realLogPower
  rw [← Complex.exp_add]
  congr 1
  ring

theorem completion_weyl_integral_weight
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ)
    (w : InfinitePlace F) (z : w.Completionˣ) (g : G F ζ hζ)
    (hi : Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g))
      (KPAdditiveHaar.adelicMeasure F))
    (hia : Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPRationalAdelicSplitting.pglA F ζ hζ
          (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * g)))
      (KPAdditiveHaar.adelicMeasure F)) :
    (∫ x : KPAdeles F, f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPRationalAdelicSplitting.pglA F ζ hζ
          (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * g))
      ∂KPAdditiveHaar.adelicMeasure F) =
    KPGlobalExceptionalParameter.realLogPower (‖(z : w.Completion)‖ ^ 2) (1 / 3 - s) *
      ∫ x : KPAdeles F, f.val s
        (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)
        ∂KPAdditiveHaar.adelicMeasure F := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  let y : ℂˣ := Units.map e.toMonoidHom z
  have hy : Units.map e.symm.toMonoidHom y = z := by
    apply Units.ext
    exact e.symm_apply_apply _
  have ha : KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
      (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) =
      KPRationalAdelicSplitting.pglA F ζ hζ
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) := by
    rw [actual_arch_single_diagonal F ζ hζ w y]
    change KPRationalAdelicSplitting.pglA F ζ hζ
      (KPRationalAdelicSplitting.localIdele F (Sum.inl w) (Units.map e.symm.toMonoidHom y)) = _
    rw [hy]
  have hnorm : ‖(y : ℂ)‖ = ‖(z : w.Completion)‖ := by
    let ei := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    have he := ei.isometry.dist_eq (z : w.Completion) 0
    have he' : ei (z : w.Completion) = (y : ℂ) := rfl
    simpa only [dist_zero_right, he', show ei 0 = 0 from e.map_zero] using he
  have hia' : Integrable (fun x : KPAdeles F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x *
        (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
          (Function.update (fun _ => (1 : ℂ)) w (y : ℂ)) * g)))
      (KPAdditiveHaar.adelicMeasure F) := by
    simpa only [ha] using hia
  have h := literal_weyl_integral_weight F ζ hζ K f s w g y hi hia'
  simpa only [ha, hnorm] using h
end DedekindZetaZeroFree.CompactPeriodAnalyticity.WeylIntegral

end
