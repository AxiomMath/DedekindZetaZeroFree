module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.Definitions
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Nonprincipality

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowAnalyticContinuation

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem Lpsi_eq_J_mul_mask (u : D.Row)
    (hnp : ¬ (D.inducers u).plus.character.IsPrincipal) (s : ℂ) :
    D.Lpsi u s = (D.rowContinuation u .plus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .plus)
        (fun p => (D.inducers u).plus.character p.asIdeal) s := by
  rw [D.Lpsi_eq_J_mask u s]
  have h0 : MaskedHeckeMeromorphic.poleIndicator (D.inducers u).plus = 0 := by
    unfold MaskedHeckeMeromorphic.poleIndicator
    exact if_neg hnp
  rw [h0, pow_zero, div_one]

theorem Llam_eq_J_mul_mask (u : D.Row)
    (hnp : ¬ (D.omega u).character.IsPrincipal) (s : ℂ) :
    D.Llam u s = (D.rowContinuation u .minus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .minus)
        (fun p => (D.omega u).character p.asIdeal) s := by
  rw [D.Llam_eq_J_mask u s]
  have h0 : MaskedHeckeMeromorphic.poleIndicator (D.omega u) = 0 := by
    unfold MaskedHeckeMeromorphic.poleIndicator
    exact if_neg hnp
  rw [h0, pow_zero, div_one]

theorem Lpsi_analyticOnNhd (u : D.Row) (hu : u.u ≠ 1) :
    AnalyticOnNhd ℂ (D.Lpsi u) {s : ℂ | 0 < s.re} := by
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).1
  intro s hs
  have hJ := (D.rowContinuation u .plus).J_holomorphic s hs
  have hB := (D.rowContinuation u .plus).B_holomorphic s hs
  have hfun : D.Lpsi u = fun s => (D.rowContinuation u .plus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .plus)
        (fun p => (D.inducers u).plus.character p.asIdeal) s :=
    funext (Lpsi_eq_J_mul_mask D u hnp)
  rw [hfun]
  exact hJ.mul hB

theorem Llam_analyticOnNhd (u : D.Row) (hu : u.u ≠ 1) :
    AnalyticOnNhd ℂ (D.Llam u) {s : ℂ | 0 < s.re} := by
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).2
  intro s hs
  have hJ := (D.rowContinuation u .minus).J_holomorphic s hs
  have hB := (D.rowContinuation u .minus).B_holomorphic s hs
  have hfun : D.Llam u = fun s => (D.rowContinuation u .minus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .minus)
        (fun p => (D.omega u).character p.asIdeal) s :=
    funext (Llam_eq_J_mul_mask D u hnp)
  rw [hfun]
  exact hJ.mul hB

theorem exists_entire_numerator (u : D.Row) (hu : u.u ≠ 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s := by
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).1
  obtain ⟨h, hh, hh'⟩ :=
    RowHeckeBridge.hecke_exists_entire D.recipe.A (D.inducers u).plus hnp
  refine ⟨fun s => Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
      (fun v => (D.inducers u).plus.character v.asIdeal) s * h s, ?_, ?_⟩
  · exact (RowHeckeBridge.mask_differentiable D.recipe.A (D.inducers u).plus hnp _
      (RowHeckeBridge.deletionSet_finite D u)).mul hh
  · intro s hs
    have h1 := RowHeckeBridge.Lpsi_eq_mask_mul D u hnp s hs
    have h2 := hh' s (by linarith)
    simp only [h1, h2]

theorem eq_Lpsi_of_analyticOn (u : D.Row) (hu : u.u ≠ 1) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re})
    (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s = D.Lpsi u s :=
  RowHeckeBridge.eqOn_halfPlane_of_eq_right hg (Lpsi_analyticOnNhd D u hu) h

theorem entire_eq_Lpsi (u : D.Row) (hu : u.u ≠ 1) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) :
    ∀ s : ℂ, 0 < s.re → g s = D.Lpsi u s :=
  eq_Lpsi_of_analyticOn D u hu (fun z _ => hg.analyticAt z) h

theorem Llam_eq_mask_mul_hecke (u : D.Row) (hu : u.u ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    D.Llam u s =
      Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
        (fun v => (D.omega u).character v.asIdeal) s *
      (RowHeckeBridge.heckeOmega D u (RowNonprincipal.inducers_nonprincipal D u hu).2).L s := by
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).2
  refine RowHeckeBridge.eqOn_halfPlane_of_eq_right (Llam_analyticOnNhd D u hu) ?_
    (fun z hz => RowHeckeBridge.Llam_eq_mask_mul D u hnp z hz) s hs
  intro z hz
  exact ((RowHeckeBridge.mask_differentiable D.recipe.A (D.omega u) hnp _
    (RowHeckeBridge.deletionSet_finite D u)).analyticAt z).mul
    (RowHeckeBridge.hecke_analyticOn D.recipe.A (D.omega u) hnp z hz)

theorem Llam_ne_zero_of_not_exceptional (ρ U : ℝ) (u : D.Row) (hu : u.u ≠ 1)
    (hU1 : U ≤ D.q u) (hU2 : D.q u < 2 * U)
    (hexc : u ∉ DetectorDef.exceptionalSet D ρ U) (ξ : ℂ)
    (hre : DetectorDef.σ₀ ≤ ξ.re) (him : |ξ.im| ≤ 4 * U ^ ρ) : D.Llam u ξ ≠ 0 := by
  intro h0
  apply hexc
  have hnp := (RowNonprincipal.inducers_nonprincipal D u hu).2
  have hσ : (0 : ℝ) < DetectorDef.σ₀ := by
    unfold DetectorDef.σ₀
    norm_num
  have hpos : 0 < ξ.re := lt_of_lt_of_le hσ hre
  have hzero : (RowHeckeBridge.heckeOmega D u hnp).L ξ = 0 := by
    have e := Llam_eq_mask_mul_hecke D u hu ξ hpos
    rw [h0] at e
    exact (mul_eq_zero.mp e.symm).resolve_left
      (RowHeckeBridge.mask_ne_zero (D.omega u) _ (RowHeckeBridge.deletionSet_finite D u) ξ hpos)
  simp only [DetectorDef.exceptionalSet, Set.mem_setOf_eq]
  exact ⟨hu, hU1, hU2, ξ, ⟨hpos, (RowHeckeBridge.heckeOmega D u hnp).L,
    RowHeckeBridge.hecke_analyticOn D.recipe.A (D.omega u) hnp,
    fun z hz => RowHeckeBridge.hecke_eq_idealLSeries D.recipe.A (D.omega u) hnp z hz,
    hzero⟩, hre, him⟩

theorem Llam_ne_zero_central (ρ U : ℝ) (hU : 0 ≤ U) (u : D.Row) (hu : u.u ≠ 1)
    (hU1 : U ≤ D.q u) (hU2 : D.q u < 2 * U)
    (hexc : u ∉ DetectorDef.exceptionalSet D ρ U) (ξ : ℂ)
    (hx : Scales.goodLine ≤ ξ.re) (him : |ξ.im| ≤ U ^ ρ) : D.Llam u ξ ≠ 0 := by
  have hnn : 0 ≤ U ^ ρ := Real.rpow_nonneg hU ρ
  refine Llam_ne_zero_of_not_exceptional D ρ U u hu hU1 hU2 hexc ξ ?_ (by linarith)
  unfold DetectorDef.σ₀
  unfold Scales.goodLine at hx
  linarith

theorem W1Hat_differentiable : Differentiable ℂ D.W1Hat := by
  have hne : ∀ v, D.recipe.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := D.recipe.probe.finiteTrace_ne_one D.recipe.A D.recipe.σ D.recipe.target
      D.recipe.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F D.recipe.A
    D.recipe.probe.finiteTrace D.recipe.probe.continuousTrace D.recipe.probe.traceCompatible hne
    D.recipe.probe.additiveMeasure D.recipe.probe.multiplicativeMeasure
    D.recipe.probe.additiveHaar D.recipe.probe.multiplicativeHaar w
    D.recipe.probe.W0 D.recipe.probe.W1 D.recipe.probe.annular D.recipe.probe.compactSupport
    D.recipe.probe.supportUnits
  rcases hsheet with ⟨_, _, _, _, _, hW, _, _⟩
  exact hW

theorem mem_OmegaStar_of_re (ξ w z : ℂ) (h1 : Scales.goodLine - EulerDomain.pad ≤ ξ.re)
    (h2 : w.re = Scales.wLine) (h3 : z.re = Scales.zLine) :
    (ξ, w, z) ∈ EulerDomain.OmegaStar := by
  unfold Scales.goodLine EulerDomain.pad at h1
  unfold Scales.wLine at h2
  unfold Scales.zLine at h3
  show 0 < ξ.re ∧ 0 < w.re ∧ 0 < z.re ∧ 1 < 6 * z.re + w.re ∧ 1 < ξ.re + 6 * z.re ∧
    1 < ξ.re + w.re ∧ 2 < ξ.re + w.re + 6 * z.re ∧ 5 < 6 * ξ.re + 6 * z.re ∧ 1 / 2 < ξ.re ∧
    2 < 3 * ξ.re ∧ 5 / 2 < 3 * ξ.re + w.re
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem rowFactor_differentiableAt (u : D.Row) (hu : u.u ≠ 1) (ξ w z : ℂ)
    (hmem : (ξ, w, z) ∈ EulerDomain.OmegaStar) (hz1 : 6 * z ≠ 1) (hξ : D.Llam u ξ ≠ 0) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2) (ξ, w, z) := by
  have hξ0 : 0 < ξ.re := hmem.1
  have hw0 : 0 < w.re := hmem.2.1
  have hz0 : 0 < z.re := hmem.2.2.1
  have hcomp : ∀ (g : ℂ → ℂ) (f : ℂ × ℂ × ℂ → ℂ), DifferentiableAt ℂ f (ξ, w, z) →
      DifferentiableAt ℂ g (f (ξ, w, z)) →
      DifferentiableAt ℂ (fun p => g (f p)) (ξ, w, z) :=
    fun g f hf hg => hg.comp (ξ, w, z) hf
  have h6 : (6 * z).re = 6 * z.re := by simp
  have hzeta : DifferentiableAt ℂ D.zetaSCont (6 * z) := by
    have hmemz : 6 * z ∈ ({s : ℂ | 0 < s.re} \ {1}) :=
      ⟨by show 0 < (6 * z).re; rw [h6]; linarith, hz1⟩
    exact (RightHeckeBounds.zetaSCont_analyticOnNhd D (6 * z) hmemz).differentiableAt
  have hLpsi : DifferentiableAt ℂ (D.Lpsi u) w :=
    (Lpsi_analyticOnNhd D u hu w hw0).differentiableAt
  have hLlam : DifferentiableAt ℂ (D.Llam u) ξ :=
    (Llam_analyticOnNhd D u hu ξ hξ0).differentiableAt
  have hHu : DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => EulerDomain.Hu D u p.1 p.2.1 p.2.2) (ξ, w, z) :=
    (EulerDomain.Hu_normal_convergence D u).2.2.1.differentiableAt
      (EulerDomain.OmegaStar_isOpen.mem_nhds hmem)
  have e1 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => D.zetaSCont (6 * p.2.2)) (ξ, w, z) :=
    hcomp D.zetaSCont (fun p => 6 * p.2.2) (by fun_prop) hzeta
  have e2 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => D.Lpsi u p.2.1) (ξ, w, z) :=
    hcomp (D.Lpsi u) (fun p => p.2.1) (by fun_prop) hLpsi
  have e3 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => D.Llam u p.1) (ξ, w, z) :=
    hcomp (D.Llam u) (fun p => p.1) (by fun_prop) hLlam
  have e5 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => (D.Llam u p.1)⁻¹) (ξ, w, z) :=
    e3.inv hξ
  have e4 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ =>
      D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * (D.Llam u p.1)⁻¹) (ξ, w, z) :=
    (e1.mul e2).mul e5
  unfold PoissonKernel.rowFactor
  simp only [div_eq_mul_inv]
  exact e4.mul hHu

theorem K_differentiableAt (u : D.Row) (hu : u.u ≠ 1) (hq : 0 < D.q u) (Z : ℝ) (hZ : 0 < Z)
    (ξ w z : ℂ) (hmem : (ξ, w, z) ∈ EulerDomain.OmegaStar) (hz1 : 6 * z ≠ 1)
    (hξ : D.Llam u ξ ≠ 0) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => PoissonKernel.K D u p.1 p.2.1 p.2.2 Z) (ξ, w, z) := by
  have hz0 : 0 < z.re := hmem.2.2.1
  have hcomp : ∀ (g : ℂ → ℂ) (f : ℂ × ℂ × ℂ → ℂ), DifferentiableAt ℂ f (ξ, w, z) →
      DifferentiableAt ℂ g (f (ξ, w, z)) →
      DifferentiableAt ℂ (fun p => g (f p)) (ξ, w, z) :=
    fun g f hf hg => hg.comp (ξ, w, z) hf
  have hZ0 : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hq0 : (D.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have a1 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ =>
      (Z : ℂ) ^ (((Scales.xExponent / 2 : ℝ) : ℂ) + p.1 - 1 + (Scales.smoothingExponent : ℂ) * p.2.2 +
        (Scales.yExponent : ℂ) * (p.2.1 - 1))) (ξ, w, z) :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hZ0)
  have a2 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => Complex.exp ((p.1 + p.2.2 - 1) ^ 2))
      (ξ, w, z) :=
    DifferentiableAt.cexp (by fun_prop)
  have hMd : DifferentiableAt ℂ D.M z :=
    D.M_differentiableOn.differentiableAt ((RowHeckeBridge.isOpen_re_gt 0).mem_nhds hz0)
  have a3 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => D.M p.2.2) (ξ, w, z) :=
    hcomp D.M (fun p => p.2.2) (by fun_prop) hMd
  have a4 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => D.W1Hat p.2.1) (ξ, w, z) :=
    hcomp D.W1Hat (fun p => p.2.1) (by fun_prop) ((W1Hat_differentiable D) w)
  have a5 : DifferentiableAt ℂ (fun p : ℂ × ℂ × ℂ => (D.q u : ℂ) ^ (-p.2.2)) (ξ, w, z) :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hq0)
  have a6 := rowFactor_differentiableAt D u hu ξ w z hmem hz1 hξ
  unfold PoissonKernel.K PoissonKernel.kernelWith
  exact (((((a1.mul a2).mul a3).mul a4).mul a5).mul a6)

theorem K_differentiableAt_xi (u : D.Row) (hu : u.u ≠ 1) (hq : 0 < D.q u) (Z : ℝ) (hZ : 0 < Z)
    (ξ w z : ℂ) (hmem : (ξ, w, z) ∈ EulerDomain.OmegaStar) (hz1 : 6 * z ≠ 1)
    (hξ : D.Llam u ξ ≠ 0) :
    DifferentiableAt ℂ (fun x : ℂ => PoissonKernel.K D u x w z Z) ξ := by
  have h := K_differentiableAt D u hu hq Z hZ ξ w z hmem hz1 hξ
  have hc : DifferentiableAt ℂ (fun x : ℂ => ((x, w, z) : ℂ × ℂ × ℂ)) ξ := by fun_prop
  exact h.comp ξ hc

theorem K_continuous_heights (u : D.Row) (hu : u.u ≠ 1) (hq : 0 < D.q u) (Z : ℝ) (hZ : 0 < Z)
    (ξ : ℂ) (hx : Scales.goodLine - EulerDomain.pad ≤ ξ.re) (hξ : D.Llam u ξ ≠ 0) :
    Continuous (fun p : ℝ × ℝ => PoissonKernel.K D u ξ
      ((Scales.wLine : ℂ) + (p.1 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.2 : ℂ) * Complex.I) Z) := by
  have hdiff : ∀ s t : ℝ, DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => PoissonKernel.K D u p.1 p.2.1 p.2.2 Z)
      (ξ, (Scales.wLine : ℂ) + (s : ℂ) * Complex.I, (Scales.zLine : ℂ) + (t : ℂ) * Complex.I) := by
    intro s t
    have hw : ((Scales.wLine : ℂ) + (s : ℂ) * Complex.I).re = Scales.wLine := by simp
    have hz : ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.zLine := by simp
    refine K_differentiableAt D u hu hq Z hZ ξ _ _ (mem_OmegaStar_of_re ξ _ _ hx hw hz) ?_ hξ
    intro h
    have := congrArg Complex.re h
    have h6 : (6 * ((Scales.zLine : ℂ) + (t : ℂ) * Complex.I)).re = 6 * Scales.zLine := by simp
    rw [h6] at this
    unfold Scales.zLine at this
    norm_num at this
  have hcont : Continuous (fun q : ℝ × ℝ => ((ξ, (Scales.wLine : ℂ) + (q.1 : ℂ) * Complex.I,
      (Scales.zLine : ℂ) + (q.2 : ℂ) * Complex.I) : ℂ × ℂ × ℂ)) := by fun_prop
  refine continuous_iff_continuousAt.2 fun q => ?_
  exact ContinuousAt.comp
    (f := fun q : ℝ × ℝ => ((ξ, (Scales.wLine : ℂ) + (q.1 : ℂ) * Complex.I,
      (Scales.zLine : ℂ) + (q.2 : ℂ) * Complex.I) : ℂ × ℂ × ℂ)) (x := q)
    (hdiff q.1 q.2).continuousAt hcont.continuousAt

theorem K_continuous_heights_good (ρ U : ℝ) (hU : 0 ≤ U) (u : D.Row) (hu : u.u ≠ 1)
    (hU1 : U ≤ D.q u) (hU2 : D.q u < 2 * U) (hq : 0 < D.q u)
    (hexc : u ∉ DetectorDef.exceptionalSet D ρ U) (Z : ℝ) (hZ : 0 < Z)
    (ξ : ℂ) (hx : Scales.goodLine ≤ ξ.re) (him : |ξ.im| ≤ U ^ ρ) :
    Continuous (fun p : ℝ × ℝ => PoissonKernel.K D u ξ
      ((Scales.wLine : ℂ) + (p.1 : ℂ) * Complex.I) ((Scales.zLine : ℂ) + (p.2 : ℂ) * Complex.I) Z) := by
  have hpad : (0 : ℝ) ≤ EulerDomain.pad := by
    unfold EulerDomain.pad
    norm_num
  exact K_continuous_heights D u hu hq Z hZ ξ (by linarith)
    (Llam_ne_zero_central D ρ U hU u hu hU1 hU2 hexc ξ hx him)

end

end DedekindZetaZeroFree.Quantitative.RowAnalyticContinuation
