module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryFlows

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem pairing_lie_adjoint (β : ℂˣ) (s : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    pairing β s (derivative s X f) g + pairing β s f (derivative (-s) X g) = 0 := by
  let T (t : ℝ) := KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)
  let f₀ (t : ℝ) := KPCplxPrincipalSeriesCharts.rightTranslate s (T t) f
  let g₀ (t : ℝ) := KPCplxPrincipalSeriesCharts.rightTranslate (-s) (T t) g
  let f₁ (t : ℝ) := KPCplxPrincipalSeriesCharts.rightTranslate s (T t) (derivative s X f)
  let g₁ (t : ℝ) := KPCplxPrincipalSeriesCharts.rightTranslate (-s) (T t) (derivative (-s) X g)
  let I (t : ℝ) (z : ℂ) := star (openCoordinate (f₀ t) z) * openCoordinate (g₀ t) z
  let J (t : ℝ) (z : ℂ) := star (openCoordinate (f₁ t) z) * openCoordinate (g₀ t) z +
    star (openCoordinate (f₀ t) z) * openCoordinate (g₁ t) z
  obtain ⟨B₀,hB₀,hf₀⟩ := translated_flow_seminorm_bound s X f
  obtain ⟨B₁,hB₁,hf₁⟩ := translated_flow_seminorm_bound s X (derivative s X f)
  obtain ⟨C₀,hC₀,hg₀⟩ := translated_flow_seminorm_bound (-s) X g
  obtain ⟨C₁,hC₁,hg₁⟩ := translated_flow_seminorm_bound (-s) X (derivative (-s) X g)
  let b (z : ℂ) := (4*B₁*C₀+4*B₀*C₁)*(1+‖z‖^2)^(-2 : ℝ)
  have hbound (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) : ‖J t z‖ ≤ b z := by
    have h₁ := boundary_product_bound s (f₁ t) (g₀ t) z
    have h₂ := boundary_product_bound s (f₀ t) (g₁ t) z
    have hn (r : ℝ) (u : PrincipalSeries r) : 0 ≤ chartSeminorm r 0 u :=
      apply_nonneg (chartSeminorm r 0) u
    have ha := mul_le_mul (hf₁ t ht) (hg₀ t ht) (hn _ _) hB₁
    have hb := mul_le_mul (hf₀ t ht) (hg₁ t ht) (hn _ _) hB₀
    have hp : 0 ≤ (1+‖z‖^2)^(-2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hd := add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤4)) hp)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)) hp)
    exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans (by dsimp [b]; nlinarith [hd]))
  have hint (t : ℝ) : Integrable (I t) (characterHaar β) := pairing_integrable β s (f₀ t) (g₀ t)
  have hjint (t : ℝ) : Integrable (J t) (characterHaar β) :=
    (pairing_integrable β s (f₁ t) (g₀ t)).add (pairing_integrable β s (f₀ t) (g₁ t))
  have hbint : Integrable b (characterHaar β) := by
    letI := characterHaar_isAddHaarMeasure β
    have hi := integrable_rpow_neg_one_add_norm_sq (μ := characterHaar β) (r := 4)
      (by norm_num : (Module.finrank ℝ ℂ : ℝ) < 4)
    have hi' : Integrable (fun z : ℂ => (1+‖z‖^2)^(-2 : ℝ)) (characterHaar β) := by
      convert hi using 1 <;> norm_num [mul_comm]
    exact hi'.const_mul _
  have hdiff (z : ℂ) (t : ℝ) : HasDerivAt (fun u => I u z) (J t z) t := by
    exact (flow_hasDerivAt s X f (weyl * upperUnipotent z) t).star.mul
      (flow_hasDerivAt (-s) X g (weyl * upperUnipotent z) t)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := characterHaar β) (x₀ := (0:ℝ)) (F := I) (F' := J) (bound := b)
    (s := Set.Icc (-1:ℝ) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hint t).aestronglyMeasurable) (hint 0)
    (hjint 0).aestronglyMeasurable (Filter.Eventually.of_forall hbound) hbint
    (Filter.Eventually.of_forall fun z t _ => hdiff z t)
  have hconst : (fun t : ℝ => ∫ z, I t z ∂characterHaar β) = fun _ => pairing β s f g := by
    funext t
    exact pairing_group_invariant β s (T t) f g
  rw [hconst] at h
  have hz := h.2.unique (hasDerivAt_const (0:ℝ) (pairing β s f g))
  have hT : T 0 = 1 := by apply Units.ext; simp [T,KPSmoothActualFlowData.matrixExponential]
  change (∫ z, star (openCoordinate (f₁ 0) z) * openCoordinate (g₀ 0) z +
    star (openCoordinate (f₀ 0) z) * openCoordinate (g₁ 0) z ∂characterHaar β) = 0 at hz
  rw [integral_add (pairing_integrable β s (f₁ 0) (g₀ 0))
    (pairing_integrable β s (f₀ 0) (g₁ 0))] at hz
  simpa only [pairing,f₀,g₀,f₁,g₁,hT,KPCplxPrincipalSeriesCharts.rightTranslate,LinearMap.coe_mk,AddHom.coe_mk,mul_one] using hz
end DedekindZetaZeroFree.CurrentComplexBoundary

end
