module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RealContinuousCharacters
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxCharacterHaar

open MeasureTheory Set

noncomputable def euclideanArea : Measure ℂ :=
  @MeasureSpace.volume ℂ
    (@measureSpaceOfInnerProductSpace ℂ _ _ (FiniteDimensional.rclike_to_real (K := ℂ)) _ _)

noncomputable def character (β : ℂ) : AddChar ℂ Circle where
  toFun x := Circle.exp (β * x).re
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [mul_add, Circle.exp_add]

theorem character_classification (ψ : AddChar ℂ Circle)
    (hψ : Continuous ψ) (hne : ψ ≠ 1) :
    ∃ β : ℂˣ, ∀ x : ℂ, ψ x = character (β : ℂ) x := by
  let ψr : AddChar ℝ Circle :=
    { toFun := fun t => ψ (t : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intros; simp [ψ.map_add_eq_mul] }
  let ψi : AddChar ℝ Circle :=
    { toFun := fun t => ψ ((t : ℂ) * Complex.I)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intros; simp [add_mul, ψ.map_add_eq_mul] }
  obtain ⟨a, ha, _⟩ := kp_real_continuous_character ψr (hψ.comp Complex.continuous_ofReal)
  obtain ⟨b, hb, _⟩ := kp_real_continuous_character ψi
    (hψ.comp (Complex.continuous_ofReal.mul continuous_const))
  let β : ℂ := ⟨2 * Real.pi * a, -(2 * Real.pi * b)⟩
  have hβ (x : ℂ) : ψ x = character β x := by
    rw [← Complex.re_add_im x, ψ.map_add_eq_mul]
    change ψr x.re * ψi x.im = character β (↑x.re + ↑x.im * Complex.I)
    rw [ha, hb, ← Circle.exp_add]
    change Circle.exp _ = Circle.exp _
    congr 1
    simp [β, Complex.mul_re]
  have hβ0 : β ≠ 0 := by
    intro hz
    apply hne
    exact AddChar.ext _ _ (fun x => by simpa [hz, character] using hβ x)
  exact ⟨Units.mk0 β hβ0, hβ⟩

noncomputable def characterScale (β : ℂˣ) : ℝ := ‖(β : ℂ)‖

noncomputable def characterRotation (β : ℂˣ) : Circle :=
  ⟨star (β : ℂ) / (characterScale β : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [characterScale, norm_div, norm_star, Complex.norm_real,
      abs_of_nonneg (norm_nonneg _), Units.ne_zero]⟩

theorem characterScale_pos (β : ℂˣ) : 0 < characterScale β := by
  exact norm_pos_iff.mpr β.ne_zero

theorem character_rotated (β : ℂˣ) (x : ℂ) :
    character (β : ℂ) ((characterRotation β : ℂ) * x) =
      Circle.exp (characterScale β * x.re) := by
  change Circle.exp ((β : ℂ) * (star (β : ℂ) / (characterScale β : ℂ) * x)).re = _
  have h : (β : ℂ) * (star (β : ℂ) / (characterScale β : ℂ)) =
      (characterScale β : ℂ) := by
    rw [← mul_div_assoc]
    change ((β : ℂ) * (starRingEnd ℂ) (β : ℂ)) / (characterScale β : ℂ) = _
    rw [Complex.mul_conj', characterScale]
    simpa [pow_two] using
      mul_div_cancel_right₀ (‖(β : ℂ)‖ : ℂ)
        (Complex.ofReal_ne_zero.mpr (characterScale_pos β).ne')
  rw [← mul_assoc, h]
  simp

noncomputable def characterHaar (β : ℂˣ) : Measure ℂ :=
  ENNReal.ofReal (characterScale β / (2 * Real.pi)) • euclideanArea

theorem characterHaar_isAddHaarMeasure (β : ℂˣ) :
    (characterHaar β).IsAddHaarMeasure := by
  unfold characterHaar euclideanArea
  exact Measure.IsAddHaarMeasure.smul volume
    (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (characterScale_pos β)
      (mul_pos (by norm_num) Real.pi_pos)))) ENNReal.ofReal_ne_top

theorem characterHaar_rotation (β : ℂˣ) :
    Measure.map (fun x : ℂ => (characterRotation β : ℂ) * x) (characterHaar β) =
      characterHaar β := by
  unfold characterHaar euclideanArea
  rw [Measure.map_smul _ (by fun_prop)]
  congr 1
  exact (rotation (characterRotation β)).measurePreserving.map_eq

open scoped FourierTransform RealInnerProductSpace ComplexConjugate

abbrev ComplexGL2 := Matrix.GeneralLinearGroup (Fin 2) ℂ

abbrev ComplexPGL2 := Matrix.ProjGenLinGroup (Fin 2) ℂ

noncomputable def diagonal (y : ℂˣ) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(y : ℂ), 0; 0, 1] (by
    simpa [Matrix.det_fin_two] using y.ne_zero)

noncomputable def upperUnipotent (x : ℂ) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by
    simp [Matrix.det_fin_two])

noncomputable def lowerUnipotent (x : ℂ) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by
    simp [Matrix.det_fin_two])

noncomputable def weyl : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
    simp [Matrix.det_fin_two])

abbrev ComplexSU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

noncomputable def complexSU2Embedding : ComplexSU2 →* ComplexGL2 where
  toFun k := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (k : Matrix (Fin 2) (Fin 2) ℂ) (by
      rw [(Matrix.mem_specialUnitaryGroup_iff.mp k.property).2]
      exact one_ne_zero)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' _ _ := by
    apply Units.ext
    rfl

theorem complexSU2_isCompact :
    IsCompact (Set.range (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hrange : Set.range (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ)) =
      (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := Subtype.range_coe
  rw [hrange]
  have hclosed : IsClosed (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        {A | A * star A = 1} ∩ {A | A.det = 1} := by
      ext A
      simp [ComplexSU2, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    rw [heq]
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hbound (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ ComplexSU2)
      (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
    have hrow := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => (B i i).re)
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp hA).1)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq] at hrow
    change ((A i 0 * (starRingEnd ℂ) (A i 0)) +
      (A i 1 * (starRingEnd ℂ) (A i 1))).re = 1 at hrow
    simp only [Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
      Complex.ofReal_re] at hrow
    fin_cases j <;> simp only [Fin.isValue, Fin.reduceFinMk, id_eq] <;>
      nlinarith [norm_nonneg (A i 0), norm_nonneg (A i 1),
        sq_nonneg ‖A i 0‖, sq_nonneg ‖A i 1‖]
  apply (isCompact_pi_infinite (fun _ : Fin 2 =>
    isCompact_pi_infinite (fun _ : Fin 2 => isCompact_closedBall (0 : ℂ) 1))).of_isClosed_subset hclosed
  intro A hA i j
  simpa [Metric.mem_closedBall, dist_zero_right] using hbound A hA i j

end DedekindZetaZeroFree.KPCplxCharacterHaar

section

namespace DedekindZetaZeroFree.KPCplxCharacterHaar

open MeasureTheory Set

open scoped FourierTransform RealInnerProductSpace ComplexConjugate

abbrev SplitComplexCover := rootsOfUnity 3 ℂ × ComplexGL2

def splitLift : ComplexGL2 →* SplitComplexCover where
  toFun g := (1, g)
  map_one' := rfl
  map_mul' _ _ := by simp

def splitScalarQuotientMap : SplitComplexCover →* (rootsOfUnity 3 ℂ × ComplexPGL2) where
  toFun g := (g.1, Matrix.ProjGenLinGroup.mk g.2)
  map_one' := by simp
  map_mul' g h := by simp

end DedekindZetaZeroFree.KPCplxCharacterHaar

end
