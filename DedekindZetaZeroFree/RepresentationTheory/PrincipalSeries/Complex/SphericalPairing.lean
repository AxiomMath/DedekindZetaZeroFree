module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.CompactBoundaryIntegration

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem pairing_eq_compact (β : ℂˣ) (ν : Measure ComplexSU2) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    pairing β s f g = pairing β s (sphericalSection s) (sphericalSection (-s)) *
      compactPairing ν s f g := by
  letI := characterHaar_isAddHaarMeasure β
  have he := integral_integral_swap (f := fun z k => star (f (weyl*upperUnipotent z*complexSU2Embedding k)) * g (weyl*upperUnipotent z*complexSU2Embedding k)) (compact_product_integrable β ν s f g)
  have hl : (∫ k, ∫ z, star (f (weyl*upperUnipotent z*complexSU2Embedding k)) *
      g (weyl*upperUnipotent z*complexSU2Embedding k) ∂characterHaar β ∂ν) = pairing β s f g := by
    calc
      _ = ∫ k, pairing β s f g ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun k => pairing_group_invariant β s (complexSU2Embedding k) f g
      _ = _ := by simp
  rw [hl] at he
  rw [integral_congr_ae (Filter.Eventually.of_forall (compact_open_average ν s f g)),integral_mul_const] at he
  exact he.symm

private theorem spherical_open (s : ℝ) (z : ℂ) :
    openCoordinate (sphericalSection s) z = ((1+‖z‖^2)^(-(1+2*s) : ℝ) : ℝ) := by
  change openCoordinate (sphericalFunction s) z = _
  simp [openCoordinate,sphericalFunction,bottomRowNormSq,weyl,upperUnipotent,
    Matrix.GeneralLinearGroup.val_det_apply,Matrix.det_mul,Matrix.det_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Real.rpow_eq_pow]
  rw [Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
  congr 1 <;> ring

theorem spherical_pairing_ne_zero (β : ℂˣ) (s : ℝ) :
    pairing β s (sphericalSection s) (sphericalSection (-s)) ≠ 0 := by
  have he (z : ℂ) : star (openCoordinate (sphericalSection s) z) *
      openCoordinate (sphericalSection (-s)) z = (((1+‖z‖^2)^(-2 : ℝ) : ℝ) : ℂ) := by
    rw [spherical_open,spherical_open]
    simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
    rw [← Real.rpow_add (by positivity)]
    congr 2 <;> ring
  change (∫ z, star (openCoordinate (sphericalSection s) z) *
    openCoordinate (sphericalSection (-s)) z ∂characterHaar β) ≠ 0
  simp_rw [he]
  rw [integral_complex_ofReal]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  letI := characterHaar_isAddHaarMeasure β
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := characterHaar β) (r := 4)
    (by norm_num : (Module.finrank ℝ ℂ : ℝ) < 4)
  have hi' : Integrable (fun z : ℂ => (1+‖z‖^2)^(-2 : ℝ)) (characterHaar β) := by
    convert hi using 1 <;> norm_num [mul_comm]
  apply (integral_pos_iff_support_of_nonneg (fun z => Real.rpow_nonneg (by positivity) _) hi').mpr
  have hs : Function.support (fun z : ℂ => (1+‖z‖^2)^(-2 : ℝ)) = Set.univ := by
    ext z
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  rw [hs]
  exact isOpen_univ.measure_pos (characterHaar β) Set.univ_nonempty

theorem compact_pairing_lie_adjoint (ν : Measure ComplexSU2) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    compactPairing ν s (derivative s X f) g +
      compactPairing ν s f (derivative (-s) X g) = 0 := by
  have h := pairing_lie_adjoint (1 : ℂˣ) s X f g
  rw [pairing_eq_compact (1 : ℂˣ) ν s (derivative s X f) g,
    pairing_eq_compact (1 : ℂˣ) ν s f (derivative (-s) X g),← mul_add] at h
  exact (mul_eq_zero.mp h).resolve_left (spherical_pairing_ne_zero 1 s)
end DedekindZetaZeroFree.CurrentComplexBoundary

end
