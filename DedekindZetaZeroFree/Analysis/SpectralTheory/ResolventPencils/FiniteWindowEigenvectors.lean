module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

@[expose] public section

namespace DedekindZetaZeroFree.KPFiniteWindowPencil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma eigenvector_spectral_parameter (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
 (μ : ℝ) (hμ : ¬ IsUnit (1 - (μ + 1) • B)) :
 μ + 1 ≠ 0 ∧ 1 / (1 + μ) ∈ spectrum ℝ B := by
 have hn : μ + 1 ≠ 0 := by
  intro he
  apply hμ
  simp [he]
 refine ⟨hn, ?_⟩
 rw [spectrum.mem_iff]
 intro hu
 apply hμ
 have he : (1 - (μ + 1) • B) = (μ + 1) • (algebraMap ℝ (H →L[ℂ] H) (1 / (1 + μ)) - B) := by
  have hh : (μ + 1) * (1 / (1 + μ)) = 1 := by rw [add_comm 1 μ]; field_simp
  rw [smul_sub, Algebra.smul_def (μ + 1) (algebraMap ℝ (H →L[ℂ] H) (1 / (1 + μ))), ← map_mul, hh, map_one]
 rw [he, Algebra.smul_def]
 exact ((isUnit_iff_ne_zero.mpr hn).map (algebraMap ℝ (H →L[ℂ] H))).mul hu

private lemma eigenvector_local_radius (μ : ℝ) (hn : μ + 1 ≠ 0) (J : Set ℝ) (hμJ : μ ∈ interior J) :
 ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x - 1 / (1 + μ)| < ε → x ≠ 0 ∧ x⁻¹ - 1 ∈ J := by
 let t := 1 / (1 + μ)
 have ht : t ≠ 0 := by simpa [t, add_comm] using inv_ne_zero hn
 have he : t⁻¹ - 1 = μ := by simp [t, add_comm, hn]
 have hc : ContinuousAt (fun x : ℝ => x⁻¹ - 1) t :=
  (continuousAt_id.inv₀ ht).sub continuousAt_const
 have hj : (fun x : ℝ => x⁻¹ - 1) ⁻¹' J ∈ nhds t :=
  hc.preimage_mem_nhds (he.symm ▸ mem_interior_iff_mem_nhds.mp hμJ)
 have hz : ({0}ᶜ : Set ℝ) ∈ nhds t := isClosed_singleton.isOpen_compl.mem_nhds ht
 obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hz hj)
 refine ⟨ε, hε, fun x hx => ?_⟩
 have hh := hs (show x ∈ Metric.ball t ε by simpa [Real.dist_eq, t] using hx)
 exact hh

private lemma eigenvector_bump_identity (ε y : ℝ) (hε : ε ≠ 0) :
 (1 - max 0 (1 - y ^ 2 / ε ^ 2)) * max (ε ^ 2) (y ^ 2) = y ^ 2 := by
 have hp : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
 by_cases h : y ^ 2 ≤ ε ^ 2
 · rw [max_eq_left h, max_eq_right (by apply sub_nonneg.mpr; exact (div_le_one hp).mpr h)]
   field_simp
   ring
 · rw [max_eq_right (le_of_not_ge h), max_eq_left (by apply sub_nonpos.mpr; exact (one_le_div hp).mpr (le_of_not_ge h))]
   simp

lemma pencil_eigenvector_of_finite_window
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (μ : ℝ) (hμ : ¬ IsUnit (1 - (μ + 1) • B))
    (J : Set ℝ) (hμJ : μ ∈ interior J)
    (hfinite : Module.Finite ℂ
      (⨅ (f : ℝ → ℝ) (_ : Continuous f)
        (_ : ∀ ν ∈ J, f (1 / (1 + ν)) = 0),
        (cfc f B).toLinearMap.ker : Submodule ℂ H)) :
    ∃ u : H, u ≠ 0 ∧ u = (μ + 1) • B u := by
 obtain ⟨hn, hspec⟩ := eigenvector_spectral_parameter B hB μ hμ
 obtain ⟨ε, hε, hlocal⟩ := eigenvector_local_radius μ hn J hμJ
 let t : ℝ := 1 / (1 + μ)
 let g : ℝ → ℝ := fun x => max 0 (1 - (x - t) ^ 2 / ε ^ 2)
 have hg : Continuous g := by fun_prop
 let W : Submodule ℂ H := ⨅ (f : ℝ → ℝ) (_ : Continuous f)
     (_ : ∀ ν ∈ J, f (1 / (1 + ν)) = 0), (cfc f B).toLinearMap.ker
 letI : Module.Finite ℂ W := hfinite
 have hrange : ∀ u : H, (cfc g B) u ∈ W := by
  intro u
  simp only [W, Submodule.mem_iInf]
  intro f hf hfJ
  change (cfc f B) ((cfc g B) u) = 0
  have hfg : (fun x => f x * g x) = (fun _ => 0) := by
   funext x
   by_cases hx : |x - t| < ε
   · obtain ⟨hx0, hxJ⟩ := hlocal x hx
     have he : 1 / (1 + (x⁻¹ - 1)) = x := by simp
     rw [← he, hfJ _ hxJ, zero_mul]
   · have he : g x = 0 := by
      apply max_eq_left
      apply sub_nonpos.mpr
      apply (one_le_div (sq_pos_of_pos hε)).mpr
      have h := le_of_not_gt hx
      nlinarith [sq_abs (x - t)]
     rw [he, mul_zero]
  have hop : cfc f B * cfc g B = 0 := by
   rw [← cfc_mul f g B hf.continuousOn hg.continuousOn, hfg, cfc_const_zero]
  simpa only [← ContinuousLinearMap.mul_apply, hop, ContinuousLinearMap.zero_apply]
 let G := cfc g B
 have hcompact : IsCompactOperator G := by
  let G' : H →L[ℂ] W := G.codRestrict W hrange
  have hc : IsCompactOperator G' := isCompactOperator_of_locallyCompactSpace_dom G'
  exact hc.clm_comp W.subtypeL
 have hGspec : (1 : ℂ) ∈ spectrum ℂ G := by
  apply (IsSelfAdjoint.coe_mem_spectrum_complex (cfc_predicate g B)).mpr
  rw [cfc_map_spectrum (a := B) (f := g) hB hg.continuousOn]
  refine ⟨t, hspec, ?_⟩
  simp [g]
 obtain ⟨u, hu⟩ := (hcompact.hasEigenvalue_iff_mem_spectrum one_ne_zero).mpr hGspec |>.exists_hasEigenvector
 have hGu : G u = u := by simpa using hu.apply_eq_smul
 have hu0 : u ≠ 0 := hu.2
 let k : ℝ → ℝ := fun x => max (ε ^ 2) ((x - t) ^ 2)
 have hk : Continuous k := by fun_prop
 have hform : (fun x => (1 - g x) * k x) = (fun x => (x - t) ^ 2) := by
  funext x
  exact eigenvector_bump_identity ε (x - t) hε.ne'
 let A : H →L[ℂ] H := B - algebraMap ℝ (H →L[ℂ] H) t
 have hA : IsSelfAdjoint A := hB.sub (cfc_predicate_algebraMap t)
 have hsq : A * A = (1 - G) * cfc k B := by
  have hv : Continuous (fun x : ℝ => x - t) := by fun_prop
  have ha : cfc (fun x : ℝ => x - t) B = A := by
   rw [cfc_sub (fun x : ℝ => x) (fun _ => t) B continuous_id.continuousOn continuous_const.continuousOn, cfc_id' ℝ B hB, cfc_const t B hB]
  rw [← ha, ← cfc_mul (fun x : ℝ => x - t) (fun x : ℝ => x - t) B hv.continuousOn hv.continuousOn]
  have hc : cfc (fun x : ℝ => 1 - g x) B = 1 - G := by
   rw [cfc_sub (fun _ : ℝ => 1) g B continuous_const.continuousOn hg.continuousOn, cfc_const_one (R := ℝ) (a := B) hB]
  rw [← hc, ← cfc_mul (fun x : ℝ => 1 - g x) k B (continuous_const.sub hg).continuousOn hk.continuousOn, hform]
  congr 1
  funext x
  ring
 have hsqzero : (A * A) u = 0 := by
  rw [hsq]
  have hcomm : Commute (1 - G) (cfc k B) := by
   have hgg := cfc_commute_cfc g k B
   exact (Commute.one_left _).sub_left hgg
  rw [hcomm.eq, ContinuousLinearMap.mul_apply]
  have he : (1 - G) u = 0 := by simpa using sub_eq_zero.mpr hGu.symm
  rw [he, map_zero]
 have hAu : A u = 0 := by
  have hm : u ∈ (ContinuousLinearMap.adjoint A ∘L A).toLinearMap.ker := by
   change (ContinuousLinearMap.adjoint A) (A u) = 0
   rw [hA.adjoint_eq]
   exact hsqzero
  rwa [ContinuousLinearMap.ker_adjoint_comp_self] at hm
 refine ⟨u, hu0, ?_⟩
 have he : B u = t • u := by
  have : B u - t • u = 0 := by simpa [A, Algebra.algebraMap_eq_smul_one] using hAu
  exact sub_eq_zero.mp this
 rw [he, smul_smul]
 have hh : (μ + 1) * t = 1 := by simp [t, add_comm 1 μ, hn]
 rw [hh, one_smul]

end DedekindZetaZeroFree.KPFiniteWindowPencil
