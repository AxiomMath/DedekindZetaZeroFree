module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SU2HaarCharacterAverages

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise

private lemma lower_zero : lowerUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]
private lemma eval_one_bound (s : ℝ) (f : PrincipalSeries s) : ‖f 1‖ ≤ chartSeminorm s 0 f := by
  have hc : Continuous (fun u : ℂ => ‖infinityCoordinate f u‖) := f.property.2.2.continuous.norm
  have hb := (isCompact_closedBall (0 : ℂ) 1).image hc
  have hh : ‖infinityCoordinate f 0‖ ≤ sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1) := by
    apply le_csSup hb.bddAbove
    exact ⟨0, by simp, rfl⟩
  change ‖f 1‖ ≤ chartSeminormValue s 0 f
  simpa only [chartSeminormValue, norm_iteratedFDeriv_zero, infinityCoordinate, lower_zero] using hh.trans (le_max_right
    (sSup ((fun x : ℂ => ‖openCoordinate f x‖) '' Metric.closedBall 0 1))
    (sSup ((fun u : ℂ => ‖infinityCoordinate f u‖) '' Metric.closedBall 0 1)))
private lemma eval_one_cont (s : ℝ) : Continuous (fun f : PrincipalSeries s => f 1) := by
  let e : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => f 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  apply WithSeminorms.continuous_normedSpace_rng ℂ (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩) e
  refine ⟨{0}, 1, ?_⟩
  intro f
  simpa [e] using eval_one_bound s f
private lemma eval_cont (s : ℝ) (g : ComplexGL2) : Continuous (fun f : PrincipalSeries s => f g) := by
  have h := (eval_one_cont s).comp ((pi_continuous s).comp
    (continuous_const.prodMk continuous_id : Continuous (fun f : PrincipalSeries s => (Matrix.ProjGenLinGroup.mk g, f))))
  convert h using 1
  ext f
  change f g = f (1 * g)
  rw [one_mul]
private lemma su2_embed_cont : Continuous complexSU2Embedding := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have he (k : ComplexSU2) : (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      have hk : complexSU2Embedding k⁻¹ = (complexSU2Embedding k)⁻¹ := map_inv _ _
      rw [← hk]
      rfl
    simp_rw [he]
    exact continuous_subtype_val.star
private lemma proj_cont : Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
  continuous_coinduced_rng
private lemma char_cont (ℓ : ℕ) : Continuous (su2HarmonicCharacter ℓ) := by
  let u : ComplexSU2 → KPCompactHarmonic.U2 := fun k => ⟨k.val, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩
  have hc : Continuous u := continuous_subtype_val.subtype_mk _
  have ht (n : ℕ) : Continuous (fun k : ComplexSU2 => KPCompactHarmonic.symmetricPowerTrace n (u k)) := by
    induction n using Nat.twoStepInduction with
    | zero => exact continuous_const
    | one => exact (by fun_prop : Continuous (fun k : ComplexSU2 => Matrix.trace k.val))
    | more n h0 h1 =>
      change Continuous (fun k => Matrix.trace k.val * KPCompactHarmonic.symmetricPowerTrace (n+1) (u k) - Matrix.det k.val * KPCompactHarmonic.symmetricPowerTrace n (u k))
      exact ((show Continuous (fun k : ComplexSU2 => Matrix.trace k.val) by fun_prop).mul h1).sub
        ((show Continuous (fun k : ComplexSU2 => Matrix.det k.val) by fun_prop).mul h0)
  have hd (k : ComplexSU2) : Matrix.det k.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have he : su2HarmonicCharacter ℓ =
      fun k => KPCompactHarmonic.symmetricPowerTrace (2*ℓ) (u k) := by
    funext k
    simp [su2HarmonicCharacter, KPCompactHarmonic.rankOneCharacter, hd k, u]
  rw [he]
  exact ht _

open MeasureTheory
private lemma compact_average_mem (s : ℝ) (μ : Measure ComplexSU2)
    [IsProbabilityMeasure μ] (F : ComplexSU2 → PrincipalSeries s)
    (hc : Continuous F) (v : PrincipalSeries s)
    (hint : ∀ g, Integrable (fun k => F k g) μ)
    (hv : ∀ g, v g = ∫ k, F k g ∂μ) :
    v ∈ closure (convexHull ℝ (Set.range F)) := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI : T2Space (PrincipalSeries s) := principalSeries_t2 s
  letI : CompleteSpace (PrincipalSeries s) := principalSeries_complete s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have h := (continuous_smul : Continuous (fun p : ℂ × PrincipalSeries s => p.1 • p.2)).comp
      ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
    exact h⟩
  letI : LocallyConvexSpace ℝ (PrincipalSeries s) := principalSeries_locallyConvex s
  let C := closure (convexHull ℝ (Set.range F))
  have hCc : IsCompact C := ((isCompact_range hc).totallyBounded.convexHull.closure).isCompact_of_isComplete isClosed_closure.isComplete
  have hCv : Convex ℝ C := (convex_convexHull ℝ (Set.range F)).closure
  have hCF (k : ComplexSU2) : F k ∈ C := subset_closure (subset_convexHull ℝ _ ⟨k, rfl⟩)
  have hfin (u : Finset ComplexGL2) : (C ∩ ⋂ g ∈ u, {w : PrincipalSeries s | w g = v g}).Nonempty := by
    let E : PrincipalSeries s →ₗ[ℝ] (u → ℂ) :=
      { toFun := fun w g => w g.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hec : Continuous E := continuous_pi fun g => eval_cont s g.val
    have hei : Integrable (fun k => E (F k)) μ := integrable_pi_iff.mpr (fun g => hint g.val)
    have hex : (∫ k, E (F k) ∂μ) ∈ E '' C :=
      (hCv.linear_image E).integral_mem (hCc.image hec).isClosed
        (Filter.Eventually.of_forall fun k => ⟨F k, hCF k, rfl⟩) hei
    obtain ⟨w, hwC, hw⟩ := hex
    refine ⟨w, hwC, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro g hg
    have hg' := congrFun hw ⟨g, hg⟩
    have hi := (ContinuousLinearMap.proj (R := ℝ) (i := (⟨g, hg⟩ : u))).integral_comp_comm hei
    change w g = (∫ k, E (F k) ∂μ) ⟨g, hg⟩ at hg'
    have hival : (∫ k, E (F k) ∂μ) ⟨g, hg⟩ = ∫ k, F k g ∂μ := hi.symm
    rw [hival] at hg'
    exact hg'.trans (hv g).symm
  obtain ⟨w, hwC, hw⟩ := hCc.inter_iInter_nonempty
    (fun g => {w : PrincipalSeries s | w g = v g})
    (fun g => isClosed_eq (eval_cont s g) continuous_const) hfin
  have he : w = v := by
    apply Subtype.ext
    funext g
    exact Set.mem_iInter.mp hw g
  exact he ▸ hwC

theorem character_average_mem_orbit_closure (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (f v : PrincipalSeries s)
    (hint : ∀ g, Integrable (fun k : ComplexSU2 =>
      star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) μ)
    (hv : ∀ g, v g = characterAverage s μ ℓ f g) :
    v ∈ closure ((Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => pi s k f))) : Set (PrincipalSeries s)) := by
  letI : IsProbabilityMeasure μ := hprob
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  let d : ℂ := ((2 * ℓ + 1 : ℕ) : ℂ)
  let F : ComplexSU2 → PrincipalSeries s := fun k =>
    (d * star (su2HarmonicCharacter ℓ k)) •
      pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) f
  have hFc : Continuous F :=
    (continuous_const.mul (char_cont ℓ).star).smul
      ((pi_continuous s).comp
        ((proj_cont.comp su2_embed_cont).prodMk continuous_const))
  have hFe (k : ComplexSU2) (g : ComplexGL2) :
      F k g = d * (star (su2HarmonicCharacter ℓ k) *
        f (g * complexSU2Embedding k)) := by
    change (d * star (su2HarmonicCharacter ℓ k)) *
      f (g * complexSU2Embedding k) = _
    exact mul_assoc _ _ _
  have hFi (g : ComplexGL2) : Integrable (fun k => F k g) μ := by
    simp_rw [hFe]
    exact (hint g).const_mul d
  have hFv (g : ComplexGL2) : v g = ∫ k, F k g ∂μ := by
    rw [hv g, characterAverage_formula]
    simp_rw [hFe]
    exact (integral_const_mul d _).symm
  have hm := compact_average_mem s μ F hFc v hFi hFv
  let S := Submodule.span ℂ
    (Set.range (fun k : compactSubgroup => pi s k f))
  have hFS : Set.range F ⊆ (S : Set (PrincipalSeries s)) := by
    rintro _ ⟨k, rfl⟩
    apply S.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding k), ⟨k, rfl⟩⟩, rfl⟩
  have hCS : convexHull ℝ (Set.range F) ⊆ (S : Set (PrincipalSeries s)) :=
    convexHull_min hFS (S.restrictScalars ℝ).convex
  exact closure_mono hCS hm

end DedekindZetaZeroFree.KPCplxHarmonicExtraction
