module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.Transform
public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.Growth
public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.Flatness

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.MellinHolomorphic

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory Asymptotics Filter Set Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma g_eq_flat_on :
    EqOn (MellinTransform.g D) (TransformFlat.g D) (Ioi (0 : ℝ)) := by
  intro Z hZ
  have hZ' : (0 : ℝ) < Z := hZ
  simp only [MellinTransform.g, TransformFlat.g, if_pos hZ']
  rw [Complex.ofReal_cpow hZ'.le]
  norm_num

private lemma g_top (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ Z in atTop, ‖MellinTransform.g D Z‖ ≤ C * Z ^ (31 / 32 + ε) := by
  obtain ⟨C, _, h⟩ := Spectral.g_growth D ε hε
  refine ⟨C, eventually_atTop.2 ⟨2, fun Z hZ => ?_⟩⟩
  have hZ0 : (0 : ℝ) < Z := by linarith
  have e : MellinTransform.g D Z = (Z : ℂ) ^ (((61 / 100 : ℝ)) : ℂ) * Spectral.f D Z := by
    simp only [MellinTransform.g, if_pos hZ0]
    norm_num
  rw [e]
  exact h Z hZ

private lemma mellin_props (z : ℂ) (hz : z.re < -(31 / 32)) :
    MellinConvergent (MellinTransform.g D) z ∧
      DifferentiableAt ℂ (mellin (MellinTransform.g D)) z := by
  set ε : ℝ := (-(31 / 32) - z.re) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set a : ℝ := -(31 / 32 + ε) with ha
  set b : ℝ := z.re - 1 with hb
  have hza : z.re < a := by rw [ha, hεdef]; linarith
  have hbz : b < z.re := by rw [hb]; linarith
  have hloc : LocallyIntegrableOn (MellinTransform.g D) (Ioi (0 : ℝ)) := by
    refine LocallyIntegrableOn.congr ?_ (TransformFlat.g_locallyIntegrableOn D)
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun Z hZ => (g_eq_flat_on D hZ).symm)
  have htop : MellinTransform.g D =O[atTop] (fun x : ℝ => x ^ (-a)) := by
    obtain ⟨C, hC⟩ := g_top D ε hε
    have hneg : -a = 31 / 32 + ε := by rw [ha]; ring
    rw [hneg]
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hC, eventually_gt_atTop 0] with Z hZ hZ0
    have hp : 0 ≤ Z ^ (31 / 32 + ε) := Real.rpow_nonneg hZ0.le _
    rw [Real.norm_of_nonneg hp]
    exact hZ
  have hbot : MellinTransform.g D =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
    have h0 := TransformFlat.g_isBigO_zero D (-b)
    exact h0.congr' (eventually_nhdsWithin_of_forall fun Z hZ => (g_eq_flat_on D hZ).symm)
      EventuallyEq.rfl
  exact ⟨mellinConvergent_of_isBigO_rpow hloc htop hza hbot hbz,
    mellin_differentiableAt_of_isBigO_rpow hloc htop hza hbot hbz⟩

theorem T_integrable (s : ℂ) (hs : 31 / 32 < s.re) :
    IntegrableOn (fun Z : ℝ =>
      Spectral.f D Z * (Z : ℂ) ^ (-s + 61 / 100) / (Z : ℂ)) (Set.Ioi 0) := by
  have hc : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • MellinTransform.g D t) (Ioi 0) :=
    (mellin_props D (-s) (by rw [Complex.neg_re]; linarith)).1
  refine IntegrableOn.congr_fun hc (fun t ht => ?_) measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
  have h1 : (t : ℂ) ^ (-s - 1) = (t : ℂ) ^ (-s) / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  have h2 : (t : ℂ) ^ (-s + 61 / 100) = (t : ℂ) ^ (-s) * (t : ℂ) ^ (61 / 100 : ℂ) :=
    Complex.cpow_add _ _ hne
  simp only [MellinTransform.g, if_pos ht', smul_eq_mul]
  rw [h1, h2]
  ring

theorem T_mellinConvergent (s : ℂ) (hs : 31 / 32 < s.re) :
    MellinConvergent (MellinTransform.g D) (-s) :=
  (mellin_props D (-s) (by rw [Complex.neg_re]; linarith)).1

theorem T_differentiableOn :
    DifferentiableOn ℂ (MellinTransform.T D) {s : ℂ | 31 / 32 < s.re} := by
  intro s hs
  have hs' : 31 / 32 < s.re := hs
  have h := (mellin_props D (-s) (by rw [Complex.neg_re]; linarith)).2
  have hneg : DifferentiableAt ℂ (fun s : ℂ => -s) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => mellin (MellinTransform.g D) (-s)) s :=
    h.comp s hneg
  exact h2.differentiableWithinAt

end

end DedekindZetaZeroFree.Quantitative.MellinHolomorphic
