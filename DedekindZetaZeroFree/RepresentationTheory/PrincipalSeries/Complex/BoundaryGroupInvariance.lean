module

public import Mathlib.RingTheory.Complex

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryRegularity
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem integral_inversion (β : ℂˣ) (f : ℂ → ℂ) :
    (∫ z, ((‖z‖ ^ (-4 : ℝ) : ℝ) : ℂ) * f z⁻¹ ∂characterHaar β) =
      ∫ z, f z ∂characterHaar β := by
  letI := characterHaar_isAddHaarMeasure β
  let D (z : ℂ) := (ContinuousLinearMap.toSpanSingleton ℂ (-(z^2)⁻¹)).restrictScalars ℝ
  have hd (z : ℂ) (hz : z ≠ 0) : HasFDerivAt (fun z : ℂ => z⁻¹) (D z) z :=
    (hasFDerivAt_inv hz).restrictScalars ℝ
  have hdet (z : ℂ) : |(D z).det| = ‖z‖ ^ (-4 : ℝ) := by
    simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, norm_neg, norm_inv,
      norm_pow, ← pow_mul, Real.rpow_neg (norm_nonneg z)]
  have he := integral_image_eq_integral_abs_det_fderiv_smul (characterHaar β)
    (s := {0}ᶜ) (isClosed_singleton.isOpen_compl.measurableSet)
    (fun z hz => (hd z (by simpa using hz)).hasFDerivWithinAt)
    (inv_injective.injOn) f
  have him : (fun z : ℂ => z⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa using inv_ne_zero (show x ≠ 0 by simpa using hx)
    · intro hz
      exact ⟨z⁻¹,by simpa using inv_ne_zero (show z ≠ 0 by simpa using hz),inv_inv z⟩
  rw [him] at he
  simp only [hdet,Complex.real_smul] at he
  simpa only [restrict_compl_singleton] using he.symm

theorem pairing_weyl_invariant (β : ℂˣ) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    pairing β s (rightTranslate s weyl f) (rightTranslate (-s) weyl g) = pairing β s f g := by
  have he (z : ℂ) : weyl * upperUnipotent z * weyl = lowerUnipotent z := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  change (∫ z, star (f (weyl * upperUnipotent z * weyl)) *
    g (weyl * upperUnipotent z * weyl) ∂characterHaar β) = _
  simp_rw [he]
  have hae : ∀ᵐ z ∂characterHaar β, z ≠ 0 := by
    letI := characterHaar_isAddHaarMeasure β
    exact ae_iff.mpr (by simp)
  change (∫ z, star (infinityCoordinate f z) * infinityCoordinate g z ∂characterHaar β) = _
  rw [integral_congr_ae (hae.mono fun z hz => product_transition s f g z hz)]
  exact integral_inversion β (fun z => star (openCoordinate f z) * openCoordinate g z)
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming open_bruhat → open_bruhat
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming infinity_bruhat → infinity_bruhat
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming row_nonzero → row_nonzero

private theorem translated_mul (s : ℝ) (a b : ComplexGL2) (f : PrincipalSeries s) :
    rightTranslate s (a*b) f = rightTranslate s a (rightTranslate s b f) := by
  apply Subtype.ext
  funext x
  exact congrArg f (mul_assoc x a b).symm

theorem pairing_group_invariant (β : ℂˣ) (s : ℝ) (h : ComplexGL2)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    pairing β s (rightTranslate s h f) (rightTranslate (-s) h g) = pairing β s f g := by
  let Q := fun h : ComplexGL2 => ∀ (f : PrincipalSeries s) (g : PrincipalSeries (-s)),
    pairing β s (rightTranslate s h f) (rightTranslate (-s) h g) = pairing β s f g
  have hmul (a b : ComplexGL2) (ha : Q a) (hb : Q b) : Q (a*b) := by
    intro f g
    rw [translated_mul,translated_mul,ha,hb]
  have hu (a d : ℂˣ) (b : ℂ) : Q (upperTriangular a d b) :=
    fun f g => pairing_upper_invariant β s f g a d b
  have hw : Q weyl := fun f g => pairing_weyl_invariant β s f g
  have hn (x : ℂ) : Q (upperUnipotent x) := hu 1 1 x
  have hl (x : ℂ) : Q (lowerUnipotent x) := by
    have he : lowerUnipotent x = weyl*upperUnipotent x*weyl := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [weyl,upperUnipotent,lowerUnipotent,Matrix.mul_apply,Fin.sum_univ_two]
    rw [he]
    exact hmul _ _ (hmul _ _ hw (hn x)) hw
  have hh : Q h := by
    rcases row_nonzero h with h0 | h1
    · obtain ⟨a,d,b,x,rfl⟩ := open_bruhat h h0
      exact hmul _ _ (hu a d b) (hmul _ _ hw (hn x))
    · obtain ⟨a,d,b,x,rfl⟩ := infinity_bruhat h h1
      exact hmul _ _ (hu a d b) (hl x)
  exact hh f g
end DedekindZetaZeroFree.CurrentComplexBoundary

end
