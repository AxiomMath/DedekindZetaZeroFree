module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.OpenCellSeparation
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SpectralDeformation
public import DedekindZetaZeroFree.Eisenstein.Continuation.ScatteringChamberAnalyticity

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MeasureTheory KPCplxCharacterHaar KPCplxPrincipalSeriesCharts TraceHaarTransport
open KPReferenceChange.StandardComplexImage.FamilyCorrect
open KPComplexIntertwinerParameterMajorant
open DedekindZetaZeroFree.KPLiteralScatteringGlobalContinuation
  (exponential_integral_differentiable)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def spectralJacquet (f : PrincipalSeries positiveParameter) (s : ℂ) (g : ComplexGL2) : ℂ :=
  ∫ x : ℂ, plusValue f s (weyl * upperUnipotent x * g) *
    star (character (standardComplexParameter : ℂ) x : ℂ) ∂characterHaar standardComplexParameter

theorem literalLocalDeformation_eq_plusValue (s : ℂ)
    (h : KPLiteralTensor.harmonicPlus) (g : ComplexGL2) :
    literalLocalDeformation s h g = plusValue h.val s g := by
  unfold literalLocalDeformation plusValue twist height rowRatio
  rw [Real.log_pow]
  push_cast
  congr 2
  ring

theorem spectralJacquet_integrable (f : PrincipalSeries positiveParameter)
    (s : ℂ) (hs : s ∈ chamber) (g : ComplexGL2) :
    Integrable (fun x : ℂ => plusValue f s (weyl * upperUnipotent x * g) *
      star (character (standardComplexParameter : ℂ) x : ℂ))
      (characterHaar standardComplexParameter) := by
  exact (chamber_integrable standardComplexParameter s hs f g).mul_bdd
    (by fun_prop : Continuous (fun x : ℂ =>
      star (character (standardComplexParameter : ℂ) x : ℂ))).aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun x => by simp))

theorem spectralJacquet_analytic (f : PrincipalSeries positiveParameter)
    (g : ComplexGL2) : AnalyticOnNhd ℂ (fun s => spectralJacquet f s g) chamber := by
  let l : ℂ → ℝ := fun x => Real.log (height (weyl * upperUnipotent x * g))
  let c : ℂ → ℂ := fun x => f (weyl * upperUnipotent x * g) *
    star (character (standardComplexParameter : ℂ) x : ℂ)
  have he (s : ℂ) (x : ℂ) :
      Complex.exp (s * (l x : ℂ)) * c x =
      plusValue f s (weyl * upperUnipotent x * g) *
        star (character (standardComplexParameter : ℂ) x : ℂ) := by
    dsimp [l,c,plusValue,twist]
    ring
  have hi (s : ℂ) (hs : -(1 / 6 : ℝ) < s.re) :
      Integrable (fun x => Complex.exp (s * (l x : ℂ)) * c x)
        (characterHaar standardComplexParameter) := by
    simpa only [he] using spectralJacquet_integrable f s (by
      change (-1 / 6 : ℝ) < s.re
      linarith) g
  have ha := (exponential_integral_differentiable
    (characterHaar standardComplexParameter) l c (-(1/6)) hi).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have hf : (fun s => spectralJacquet f s g) =
      (fun s => ∫ x, Complex.exp (s * (l x : ℂ)) * c x
        ∂characterHaar standardComplexParameter) := by
    funext s
    unfold spectralJacquet
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (he s x).symm))
  rw [hf]
  convert ha using 1
  ext s
  simp only [chamber, Set.mem_setOf_eq]
  norm_num

theorem spectralJacquet_zero (f : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    spectralJacquet f 0 g = KPCplxJacquetFunctional.jacquetIntegral standardComplexParameter
      (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f) := by
  unfold spectralJacquet KPCplxJacquetFunctional.jacquetIntegral
  simp only [plusValue_zero, pi_mk, rightTranslate]
  apply integral_congr_ae
  filter_upwards with x
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

def spectralJacquetMap (s : ℂ) : PrincipalSeries positiveParameter →ₗ[ℂ] (ComplexGL2 → ℂ) := by
  by_cases hs : s ∈ chamber
  · exact {
      toFun f g := spectralJacquet f s g
      map_add' f h := by
        funext g
        unfold spectralJacquet
        have he : (fun x : ℂ => plusValue (f+h) s (weyl * upperUnipotent x * g) *
            star (character (standardComplexParameter : ℂ) x : ℂ)) =
          (fun x => plusValue f s (weyl * upperUnipotent x * g) *
            star (character (standardComplexParameter : ℂ) x : ℂ) +
            plusValue h s (weyl * upperUnipotent x * g) *
            star (character (standardComplexParameter : ℂ) x : ℂ)) := by
          funext x
          simp only [plusValue, Pi.add_apply, twist]
          change _ * (f _ + h _) * _ = _
          ring
        rw [he]
        exact integral_add (spectralJacquet_integrable f s hs g)
          (spectralJacquet_integrable h s hs g)
      map_smul' c f := by
        funext g
        unfold spectralJacquet
        have he : (fun x : ℂ => plusValue (c • f) s (weyl * upperUnipotent x * g) *
            star (character (standardComplexParameter : ℂ) x : ℂ)) =
          (fun x => c * (plusValue f s (weyl * upperUnipotent x * g) *
            star (character (standardComplexParameter : ℂ) x : ℂ))) := by
          funext x
          simp only [plusValue, twist]
          change _ * (c * f _) * _ = _
          ring
        rw [he]
        exact integral_const_mul c _ }
  · exact 0

theorem spectralJacquetMap_apply (s : ℂ) (hs : s ∈ chamber)
    (f : PrincipalSeries positiveParameter) (g : ComplexGL2) :
    spectralJacquetMap s f g = spectralJacquet f s g := by
  simp only [spectralJacquetMap, dif_pos hs, LinearMap.coe_mk, AddHom.coe_mk]

end DedekindZetaZeroFree.SheetRescaling

end
