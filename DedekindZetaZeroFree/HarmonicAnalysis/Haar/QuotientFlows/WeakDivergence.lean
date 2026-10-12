module

public import DedekindZetaZeroFree.Metaplectic.Torus.RadialCuspFrames
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RationalQuotientCompactMass
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.NormalPrincipalCoefficient

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

namespace CutoffApproximation

def coreCutoff
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) (x : X F ζ hζ) : ℝ :=
  if x ∈ quotientCore A P Y then 1
  else max 0 (min 1 ((Y + ε - D.modulus (P.projection U x)) / ε))

def cutoffIntegral
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (Y ε : ℝ) (f : X F ζ hζ → ℂ) : ℂ :=
  ∫ x, (coreCutoff A R P D Y ε x : ℂ) * f x ∂ R.quotientHaar

end CutoffApproximation
end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes

end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal BigOperators Matrix.Norms.Operator
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 def basisFlip (j : Fin 6) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (if j.val < 2 then !![0,1;1,0] else !![-1,0;0,1]) (by
      split <;> simp [Matrix.det_fin_two])
private theorem basisFlip_inv (j : Fin 6) : (basisFlip j)⁻¹ = basisFlip j := by
  apply inv_eq_of_mul_eq_one_left
  apply Units.ext
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [basisFlip, Matrix.mul_apply, Fin.sum_univ_two]
private theorem basisFlip_conj (j : Fin 6) (t : ℂ) :
    ((basisFlip j).val * (t • KPSmoothActualFlowData.basisMatrix j) *
      ((basisFlip j)⁻¹).val) = -t • KPSmoothActualFlowData.basisMatrix j := by
  rw [basisFlip_inv]
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [basisFlip, KPSmoothActualFlowData.basisMatrix, KPSmoothActualFlowData.sl2Matrix,
      Matrix.mul_apply, Fin.sum_univ_two]
private theorem basisFlip_exp (j : Fin 6) (t : ℂ) :
    basisFlip j * KPSmoothActualFlowData.matrixExponential (t • KPSmoothActualFlowData.basisMatrix j) *
      (basisFlip j)⁻¹ =
        KPSmoothActualFlowData.matrixExponential (-t • KPSmoothActualFlowData.basisMatrix j) := by
  apply Units.ext
  simp only [Units.val_mul, KPSmoothActualFlowData.matrixExponential, IsUnit.unit_spec]
  rw [← basisFlip_conj j t]
  exact (NormedSpace.exp_units_conj (basisFlip j) (t • KPSmoothActualFlowData.basisMatrix j)).symm
 def flowFlip (w : NumberField.InfinitePlace F) (j : Fin 6) :
    KPSmoothActualFlowData.GInfinity F :=
  fun v => if v = w then Matrix.ProjGenLinGroup.mk (basisFlip j) else 1
private theorem flowFlip_conj (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    flowFlip w j * KPSmoothActualFlowData.flow F (w,j) t * (flowFlip w j)⁻¹ =
      KPSmoothActualFlowData.flow F (w,j) (-t) := by
  ext v
  simp only [Pi.mul_apply, Pi.inv_apply, flowFlip,
    NormalCoefficientCalculus.flow_apply]
  split_ifs with hv
  · simp only [← map_inv, ← map_mul, basisFlip_exp, Complex.ofReal_neg]
  · simp
 def archHom : KPSmoothActualFlowData.GInfinity F →* Cover F ζ hζ where
  toFun := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
  map_one' := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1
  map_mul' := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
private theorem flow_inv (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    KPSmoothActualFlowData.flow F (w,j) (-t) = (KPSmoothActualFlowData.flow F (w,j) t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← (KPSmoothActualFlowData.flow_properties F (w,j)).2.1]
  simp [(KPSmoothActualFlowData.flow_properties F (w,j)).1]
private theorem flow_modular_one (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
    letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    Measure.modularCharacter (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPSmoothActualFlowData.flow F (w,j) t)) = 1 := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  let χ := Measure.modularCharacter (G := Cover F ζ hζ)
  let h := archHom (F := F) (ζ := ζ) (hζ := hζ)
  have hc : h (flowFlip w j) * h (KPSmoothActualFlowData.flow F (w,j) t) *
      (h (flowFlip w j))⁻¹ = (h (KPSmoothActualFlowData.flow F (w,j) t))⁻¹ := by
    rw [← map_inv h, ← map_mul h, ← map_mul h, flowFlip_conj, flow_inv, map_inv h]
  have he := congrArg χ hc
  simp only [map_mul, map_inv] at he
  have hp : 0 < χ (h (flowFlip w j)) := Measure.modularCharacterFun_pos _
  have hp' : 0 < χ (h (KPSmoothActualFlowData.flow F (w,j) t)) := Measure.modularCharacterFun_pos _
  have he' : χ (h (KPSmoothActualFlowData.flow F (w,j) t)) =
      (χ (h (KPSmoothActualFlowData.flow F (w,j) t)))⁻¹ := by
    calc
      _ = χ (h (flowFlip w j)) * χ (h (KPSmoothActualFlowData.flow F (w,j) t)) *
          (χ (h (flowFlip w j)))⁻¹ := by
        rw [mul_right_comm, mul_inv_cancel₀ (ne_of_gt hp), one_mul]
      _ = _ := he
  have hsq : χ (h (KPSmoothActualFlowData.flow F (w,j) t)) *
      χ (h (KPSmoothActualFlowData.flow F (w,j) t)) = 1 := by
    conv_lhs => arg 2; rw [he']
    exact mul_inv_cancel₀ (ne_of_gt hp')
  change χ (h (KPSmoothActualFlowData.flow F (w,j) t)) = 1
  apply NNReal.eq
  change (χ (h (KPSmoothActualFlowData.flow F (w,j) t)) : ℝ) = 1
  have hreal : (χ (h (KPSmoothActualFlowData.flow F (w,j) t)) : ℝ) ^ 2 = 1 := by
    rw [pow_two]
    exact_mod_cast hsq
  have hpos : (0 : ℝ) < χ (h (KPSmoothActualFlowData.flow F (w,j) t)) := by exact_mod_cast hp'
  nlinarith
private theorem ambient_flow_measurePreserving
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    MeasurePreserving (fun g : Cover F ζ hζ => g *
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,j) t))
      R.adelicHaar R.adelicHaar := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : BorelSpace (Cover F ζ hζ) := ⟨rfl⟩
  letI := R.adelic_isHaar
  refine ⟨(continuous_id.mul continuous_const).measurable, ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  change (Measure.modularCharacter (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,j) t)) : ℝ≥0) • R.adelicHaar = _
  rw [flow_modular_one, one_smul]

theorem quotient_flow_measurePreserving
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (w : NumberField.InfinitePlace F) (j : Fin 6) (t : ℝ) :
    MeasurePreserving (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F (w,j) t)))
      R.quotientHaar R.quotientHaar := by
  have hq_meas : Measurable (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) :=
    continuous_quotient_mk'.measurable
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (KubotaRankTwo.GL2 F) := Units.val_injective.countable
  letI : Countable (KPRationalAdelicSplitting.RationalPGL2 F) :=
    (Quotient.mk'_surjective (s := QuotientGroup.leftRel
      (KPRationalAdelicSplitting.rationalScalars F))).countable
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    Set.Countable.to_subtype (Set.countable_range (KPSmoothLocalQuotientCharts.rationalSplit F ζ hζ))
  letI : IsTopologicalGroup (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) := ⟨rfl⟩
  letI := R.adelic_isHaar
  set c := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,j) t) with hc
  have hmulc_meas : Measurable (fun g : Cover F ζ hζ => g * c) :=
    (continuous_id.mul continuous_const).measurable
  have hmp : MeasurePreserving (fun g : Cover F ζ hζ => g * c)
      R.adelicHaar R.adelicHaar := ambient_flow_measurePreserving R w j t
  have hmp_inv : MeasurePreserving (fun g : Cover F ζ hζ => g * c⁻¹)
      R.adelicHaar R.adelicHaar := by
    have hi : c⁻¹ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.flow F (w,j) (-t)) := by
      change ((archHom (F := F) (ζ := ζ) (hζ := hζ))
        (KPSmoothActualFlowData.flow F (w,j) t))⁻¹ = _
      rw [← map_inv, ← flow_inv]
      rfl
    rw [hi]
    exact ambient_flow_measurePreserving R w j (-t)
  have hD' : IsFundamentalDomain (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain) R.adelicHaar := by
    refine IsFundamentalDomain.image_of_equiv (ν := R.adelicHaar) (μ := R.adelicHaar)
      R.domain_fundamental (Equiv.mulRight c) ?_ (Equiv.refl _) ?_
    · exact hmp_inv.quasiMeasurePreserving
    · intro g x
      show ((g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x) * c =
        (g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * (x * c)
      rw [mul_assoc]
  have hmap_mulc :
      Measure.map (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c)
        (R.adelicHaar.restrict R.domain) =
      R.adelicHaar.restrict
        ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain) := by
    let e : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ ≃ᵐ
        KPSmoothLocalQuotientCharts.ActualCover F ζ hζ :=
      (Homeomorph.mulRight c).toMeasurableEquiv
    have he : ⇑e = (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) := rfl
    have hmap_e : Measure.map (⇑e) R.adelicHaar = R.adelicHaar := by
      rw [he]; exact hmp.map_eq
    have hpre : ⇑e ⁻¹'
        ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)
        = R.domain := by
      rw [he]
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := mul_right_cancel hyx
        rwa [← this]
      · intro hx
        exact ⟨x, hx, rfl⟩
    have h := MeasurableEquiv.restrict_map e R.adelicHaar
      ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)
    rw [hmap_e, hpre] at h
    rw [h, he]
  have hcont : Continuous (KPSmoothActualFlowData.rightTranslate F ζ hζ c) :=
    (continuous_id.mul continuous_const).quotient_map' _
  have ht_meas : Measurable (KPSmoothActualFlowData.rightTranslate F ζ hζ c) := hcont.borel_measurable
  have hdom_eq : Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
        (R.adelicHaar.restrict
          ((fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) '' R.domain)) =
      Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ)
        (R.adelicHaar.restrict R.domain) := by
    ext A hA
    have hA₀ : MeasurableSet (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ⁻¹' A) := hq_meas hA
    rw [Measure.map_apply hq_meas hA, Measure.map_apply hq_meas hA,
      Measure.restrict_apply hA₀, Measure.restrict_apply hA₀]
    refine IsFundamentalDomain.measure_set_eq hD' R.domain_fundamental hA₀ (fun γ => ?_)
    ext x
    simp only [Set.mem_preimage]
    have hsmul : (γ • x : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) =
        (γ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x := rfl
    rw [hsmul]
    have h : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        ((γ : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ) * x) =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ x := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simpa using (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ).inv_mem γ.property
    rw [h]
  have hcomp : KPSmoothActualFlowData.rightTranslate F ζ hζ c ∘ KPSmoothLocalQuotientCharts.quotientMap F ζ hζ =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘
        (fun g : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ => g * c) := by
    funext g
    rfl
  refine ⟨ht_meas, ?_⟩
  rw [← R.quotient_normalization]
  rw [Measure.map_map ht_meas hq_meas, hcomp,
    ← Measure.map_map hq_meas hmulc_meas, hmap_mulc, hdom_eq]

end DedekindZetaZeroFree.KPMsGreenFlux.ActualSharpStokes

end

end
