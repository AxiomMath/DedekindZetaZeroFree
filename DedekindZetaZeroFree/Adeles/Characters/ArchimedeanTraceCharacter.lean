module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.RingTheory.Complex

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField

@[instance_reducible]
noncomputable def archCompletionAlgebra {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : Algebra ℝ v.Completion := by
  classical
  by_cases hv : v.IsReal
  · exact (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom.toAlgebra
  · have hw : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    exact (((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom).comp
      Complex.ofRealHom).toAlgebra

noncomputable def archTrace {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) :
    letI : Algebra ℝ v.Completion := archCompletionAlgebra v
    v.Completion →ₗ[ℝ] ℝ := by
  classical
  letI : Algebra ℝ v.Completion := archCompletionAlgebra v
  refine {
    toFun := fun z => if hv : v.IsReal then
        InfinitePlace.Completion.ringEquivRealOfIsReal hv z
      else
        Algebra.trace ℝ ℂ
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hv) z)
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    by_cases hv : v.IsReal
    · simp [hv, map_add]
    · simp [hv, map_add]
  · intro r z
    by_cases hv : v.IsReal
    · simp only [dif_pos hv]
      have ha : archCompletionAlgebra v =
          (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom.toAlgebra := by
        simp [archCompletionAlgebra, hv]
      have hr : (algebraMap ℝ v.Completion) r =
          (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r := by
        change @algebraMap ℝ v.Completion _ _ (archCompletionAlgebra v) r = _
        rw [ha]
        rfl
      simp only [Algebra.smul_def, hr]
      simp [map_mul]
    · simp only [dif_neg hv]
      have ha : archCompletionAlgebra v =
          (((InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toRingHom).comp
              Complex.ofRealHom).toAlgebra := by
        simp [archCompletionAlgebra, hv]
      have hr : (algebraMap ℝ v.Completion) r =
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm (r : ℂ) := by
        change @algebraMap ℝ v.Completion _ _ (archCompletionAlgebra v) r = _
        rw [ha]
        rfl
      simp only [Algebra.smul_def, hr]
      rw [map_mul, RingEquiv.apply_symm_apply]
      simpa [Algebra.smul_def] using
        (Algebra.trace ℝ ℂ).map_smul r
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp hv) z)

theorem continuous_archTrace {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : Continuous (archTrace v : v.Completion → ℝ) := by
  classical
  by_cases hv : v.IsReal
  · simpa [archTrace, hv] using
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).continuous
  · simp only [archTrace, dif_neg hv, LinearMap.coe_mk, AddHom.coe_mk,
      Algebra.trace_complex_apply, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact continuous_const.mul (Complex.continuous_re.comp
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous)

noncomputable def archTraceCharacter {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : AddChar v.Completion Circle where
  toFun z := Circle.exp (2 * Real.pi * archTrace v z)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    rw [map_add, mul_add, Circle.exp_add]

theorem continuous_archTraceCharacter {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) : Continuous (archTraceCharacter v : v.Completion → Circle) := by
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_archTrace v))

theorem archTrace_of_isReal {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) (hv : v.IsReal) (z : v.Completion) :
    archTrace v z = InfinitePlace.Completion.ringEquivRealOfIsReal hv z := by
  classical
  simp [archTrace, hv]

theorem archTrace_of_isComplex {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) (hv : v.IsComplex) (z : v.Completion) :
    archTrace v z =
      2 * (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv z).re := by
  classical
  simp [archTrace, InfinitePlace.not_isReal_iff_isComplex.mpr hv,
    Algebra.trace_complex_apply]

theorem archTraceCharacter_of_isComplex {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) (hv : v.IsComplex) (z : v.Completion) :
    archTraceCharacter v z = Circle.exp
      (2 * Real.pi * (2 * (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv z).re)) := by
  change Circle.exp (2 * Real.pi * archTrace v z) = _
  rw [archTrace_of_isComplex v hv]

end DedekindZetaZeroFree

end
