module

public import DedekindZetaZeroFree.Eisenstein.Residues.Exceptional.FiniteDimensionalCoreBounds
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.RaisingOperators.SphericalDerivativeReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageRaising
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageBounds renaming literal_bounded_entire_stage → literal_bounded_entire_stage
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem literal_finite_word_reconstruction
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (m : Fin n → ℕ)
      (v : ∀ i, Fin (m i) → KPContActualSphericalFlatStage.Stage F ζ hζ (U i))
      (w : ∀ i, Fin (m i) → List (Fin
        (KPContActualSphericalRightFieldIdentification.groupDimension F)))
      (Q : ℂ → ℂ) (B : ∀ i, Fin (m i) → ℂ → ℂ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        ∀ s ∈ Metric.ball (0 : ℂ) r, Q s ≠ 0) ∧
      (∀ i j, AnalyticOnNhd ℂ (B i j) KPContinuation.spectralDomain) ∧
      ∀ s ∈ KPContinuation.spectralDomain, ∀ g,
        Q s * f.val s g = ∑ i, ∑ j, B i j s *
          KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ (w i j)
            ((KPContFlatSourceRecipe.flatR F ζ hζ s (v i j).val).val) g := by
  obtain ⟨n, ι, p, T, J, hι, hp, hSmooth, hT, hJ, hpin⟩ :=
    literal_bounded_entire_stage F ζ hζ K hK f
  have hrec (i : Fin n) :=
    KPGlobalResidualConstruction.ActualRaisingGeometry.actual_cleared_spherical_derivative_reconstruction
      F ζ hζ (ι (Pi.single i 1))
  choose U m v w q b hq hq0 hb he using hrec
  let Q : ℂ → ℂ := fun s => ∏ i : Fin n, q i s
  let C : Fin n → ℂ → ℂ := fun i s => ∏ k ∈ Finset.univ.erase i, q k s
  let B : ∀ i, Fin (m i) → ℂ → ℂ := fun i j s => p s i * C i s * b i j s
  have hQ : AnalyticOnNhd ℂ Q KPContinuation.spectralDomain :=
    Finset.univ.analyticOnNhd_fun_prod (fun i _ => hq i)
  have hQ0 : Q 0 = 1 := by simp [Q, hq0]
  have hC (i : Fin n) : AnalyticOnNhd ℂ (C i) KPContinuation.spectralDomain :=
    (Finset.univ.erase i).analyticOnNhd_fun_prod (fun k _ => hq k)
  have hp' (i : Fin n) : AnalyticOnNhd ℂ (fun s => p s i)
      KPContinuation.spectralDomain := by
    intro s hs
    exact ((differentiable_apply i).comp hp).analyticAt s
  have hB (i : Fin n) (j : Fin (m i)) :
      AnalyticOnNhd ℂ (B i j) KPContinuation.spectralDomain :=
    ((hp' i).mul (hC i)).mul (hb i j)
  have hdisk : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
      ∀ s ∈ Metric.ball (0 : ℂ) r, Q s ≠ 0 := by
    have hz : (0 : ℂ) ∈ KPContinuation.spectralDomain := by
      norm_num [KPContinuation.spectralDomain]
    have hn : ∀ᶠ s in 𝓝 (0 : ℂ), Q s ≠ 0 :=
      (hQ 0 hz).continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (KPContinuation.spectralDomain_isOpen.mem_nhds hz) hn)
    exact ⟨r, hr, fun s hs => (hball hs).1, fun s hs => (hball hs).2⟩
  refine ⟨n, U, m, v, w, Q, B, hQ, hQ0, hdisk, hB, ?_⟩
  intro s hs g
  have hi : ι (p s) = ∑ i : Fin n, (p s i) • ι (Pi.single i 1) := by
    calc
      ι (p s) = ι (∑ i : Fin n, Pi.single i (p s i)) :=
        congrArg ι (LinearMap.sum_single_apply (fun _ : Fin n => ℂ) (p s)).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← map_smul]
        congr 1
        ext k
        by_cases hk : k = i <;> simp [hk]
  have hf : f.val s g = ∑ i : Fin n, p s i *
      (KPContFlatSourceRecipe.flatR F ζ hζ s (ι (Pi.single i 1))).val g := by
    rw [← hpin s g]
    change (KPContFlatSourceRecipe.flatR F ζ hζ s (ι (p s))).val g = _
    rw [hi]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hQP : Q s = C i s * q i s :=
    (Finset.prod_erase_mul Finset.univ (fun k => q k s) (Finset.mem_univ i)).symm
  calc
    Q s * (p s i * (KPContFlatSourceRecipe.flatR F ζ hζ s (ι (Pi.single i 1))).val g) =
        (p s i * C i s) *
          (q i s * (KPContFlatSourceRecipe.flatR F ζ hζ s (ι (Pi.single i 1))).val g) := by
            rw [hQP]; ring
    _ = (p s i * C i s) * ∑ j, b i j s *
        KPContActualSphericalRightFieldIdentification.actualRightWord F ζ hζ (w i j)
          ((KPContFlatSourceRecipe.flatR F ζ hζ s (v i j).val).val) g := by
            rw [he i s hs g]
    _ = _ := by simp only [Finset.mul_sum, B, mul_assoc]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageRaising

end
