module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryLieAdjoint

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Topology Matrix.Norms.Elementwise
namespace DedekindZetaZeroFree.CurrentComplexBoundary
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_point_eval_continuous → evaluation_point_eval_continuous
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming evaluation_rightTranslate_orbit_continuous → evaluation_rightTranslate_orbit_continuous
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming topology_withSeminorms → topology_withSeminorms
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming compact_chart → compact_chart
open _root_.DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts renaming spherical_su2 → spherical_su2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
 instance : CompactSpace ComplexSU2 := by
  apply isCompact_iff_compactSpace.mp
  convert complexSU2_isCompact using 1
  exact Subtype.range_coe.symm

theorem su2Embedding_continuous : Continuous complexSU2Embedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have hi (k : ComplexSU2) : (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← map_inv]
      rfl
    simp_rw [hi]
    exact continuous_subtype_val.star

theorem section_continuous (s : ℝ) (f : PrincipalSeries s) : Continuous (f : ComplexGL2 → ℂ) := by
  have h := (evaluation_point_eval_continuous s 1).comp (evaluation_rightTranslate_orbit_continuous s f)
  simpa only [Function.comp_def,KPCplxPrincipalSeriesCharts.rightTranslate,LinearMap.coe_mk,AddHom.coe_mk,one_mul] using h

def compactPairing (ν : Measure ComplexSU2) (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) : ℂ :=
  ∫ k, star (f (complexSU2Embedding k)) * g (complexSU2Embedding k) ∂ν

theorem compact_pairing_integrable (ν : Measure ComplexSU2) [IsFiniteMeasure ν] (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    Integrable (fun k => star (f (complexSU2Embedding k)) * g (complexSU2Embedding k)) ν := by
  exact (((section_continuous s f).comp su2Embedding_continuous).star.mul
    ((section_continuous (-s) g).comp su2Embedding_continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem compact_translated_bound (s : ℝ) (f : PrincipalSeries s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ComplexSU2,
      chartSeminorm s 0 (KPCplxPrincipalSeriesCharts.rightTranslate s (complexSU2Embedding k) f) ≤ B := by
  have hc := ((topology_withSeminorms s).continuous_seminorm 0).comp
    ((evaluation_rightTranslate_orbit_continuous s f).comp su2Embedding_continuous)
  obtain ⟨B,hB⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  exact ⟨max B 0,le_max_right _ _, fun k => (hB ⟨k,Set.mem_univ _,rfl⟩).trans (le_max_left _ _)⟩

theorem compact_product_integrable (β : ℂˣ) (ν : Measure ComplexSU2) [IsFiniteMeasure ν]
    (s : ℝ) (f : PrincipalSeries s) (g : PrincipalSeries (-s)) :
    Integrable (fun p : ℂ × ComplexSU2 => star (f (weyl*upperUnipotent p.1*complexSU2Embedding p.2)) *
      g (weyl*upperUnipotent p.1*complexSU2Embedding p.2)) ((characterHaar β).prod ν) := by
  obtain ⟨B,hB,hf⟩ := compact_translated_bound s f
  obtain ⟨C,hC,hg⟩ := compact_translated_bound (-s) g
  have hu : Continuous upperUnipotent := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun z : ℂ => !![1,z;0,1])
      fun_prop
    · have hi (z : ℂ) : (upperUnipotent z)⁻¹ = upperUnipotent (-z) := by
        apply inv_eq_of_mul_eq_one_left
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [upperUnipotent,Matrix.mul_apply,Fin.sum_univ_two]
      simp_rw [hi]
      change Continuous (fun z : ℂ => !![1,-z;0,1])
      fun_prop
  have hc : Continuous (fun p : ℂ × ComplexSU2 => weyl*upperUnipotent p.1*complexSU2Embedding p.2) :=
    (continuous_const.mul (hu.comp continuous_fst)).mul (su2Embedding_continuous.comp continuous_snd)
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ComplexSU2 => star (f (weyl*upperUnipotent p.1*complexSU2Embedding p.2)) * g (weyl*upperUnipotent p.1*complexSU2Embedding p.2)) ((characterHaar β).prod ν) := (((section_continuous s f).comp hc).star.mul ((section_continuous (-s) g).comp hc)).aestronglyMeasurable
  letI := characterHaar_isAddHaarMeasure β
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := characterHaar β) (r := 4)
    (by norm_num : (Module.finrank ℝ ℂ : ℝ) < 4)
  have hi' : Integrable (fun z : ℂ => (1+‖z‖^2)^(-2 : ℝ)) (characterHaar β) := by
    convert hi using 1 <;> norm_num [mul_comm]
  apply ((hi'.const_mul (4*B*C)).comp_fst ν).mono' hmeas
  filter_upwards [] with p
  have hb := boundary_product_bound s (KPCplxPrincipalSeriesCharts.rightTranslate s (complexSU2Embedding p.2) f)
    (KPCplxPrincipalSeriesCharts.rightTranslate (-s) (complexSU2Embedding p.2) g) p.1
  have hbc := mul_le_mul (hf p.2) (hg p.2) (apply_nonneg (chartSeminorm (-s) 0) _) hB
  have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbc (by norm_num : (0:ℝ)≤4))
    (Real.rpow_nonneg (by positivity : 0 ≤ 1+‖p.1‖^2) (-2))
  exact hb.trans (by simpa only [mul_assoc] using hd)

theorem compact_open_average (ν : Measure ComplexSU2) [ν.IsMulLeftInvariant] (s : ℝ)
    (f : PrincipalSeries s) (g : PrincipalSeries (-s)) (z : ℂ) :
    (∫ k, star (f (weyl*upperUnipotent z*complexSU2Embedding k)) *
      g (weyl*upperUnipotent z*complexSU2Embedding k) ∂ν) =
    (star (openCoordinate (sphericalSection s) z) * openCoordinate (sphericalSection (-s)) z) *
      compactPairing ν s f g := by
  obtain ⟨a,d,b,k₀,hz⟩ := compact_chart z
  have hs (r : ℝ) (k : ComplexSU2) : sphericalSection r (complexSU2Embedding k) = 1 := by
    have he := spherical_su2 r 1 k
    change sphericalFunction r (complexSU2Embedding k) = 1
    simpa only [one_mul,show sphericalFunction r 1 = 1 from sphericalSection_one r] using he
  have he (k : ComplexSU2) :
      star (f (weyl*upperUnipotent z*complexSU2Embedding k)) *
        g (weyl*upperUnipotent z*complexSU2Embedding k) =
      ((inductionWeight s a d * inductionWeight (-s) a d : ℝ) : ℂ) *
        (star (f (complexSU2Embedding (k₀*k))) * g (complexSU2Embedding (k₀*k))) := by
    rw [hz,mul_assoc,← map_mul,f.property.1 a d b,g.property.1 a d b]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_mul_left_eq_self (fun k : ComplexSU2 => star (f (complexSU2Embedding k)) * g (complexSU2Embedding k)) k₀]
  change _ = (star ((sphericalSection s) (weyl*upperUnipotent z)) *
    (sphericalSection (-s)) (weyl*upperUnipotent z)) * _
  rw [hz,(sphericalSection s).property.1 a d b,(sphericalSection (-s)).property.1 a d b,hs,hs]
  simp [compactPairing,Complex.ofReal_mul]

end DedekindZetaZeroFree.CurrentComplexBoundary

end
