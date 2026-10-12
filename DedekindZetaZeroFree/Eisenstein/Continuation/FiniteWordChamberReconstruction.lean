module

public import DedekindZetaZeroFree.Eisenstein.Induction.RaisingOperators.ChamberWordSums
public import DedekindZetaZeroFree.Eisenstein.Residues.Exceptional.FiniteWordReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber
open KPLiteralRaw KPContActualSphericalRightFieldIdentification
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalStageRaising renaming literal_finite_word_reconstruction → literal_finite_word_reconstruction
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem lift_eq (c : KPChamberBruhatTwoCells.RationalQuotient F) :
    KPContActualChamberNormalSeries.lift F ζ hζ c = rationalLift F ζ hζ (Quotient.out c) := by
  unfold KPContActualChamberNormalSeries.lift KPContFlatRationalCosetCovariance.matrixRationalHom
  change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
      (Quotient.out c)) = _
  rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift]
  exact (KPLiteralExceptionalResidue.rationalLift_eq_constructed F ζ hζ (Quotient.out c)).symm

 theorem word_zero (w : List (Fin (groupDimension F))) :
    actualRightWord F ζ hζ w (fun _ => 0) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [actualRightWord, ih]
    funext g
    exact deriv_const _ _

 theorem spherical_word_chamber
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (v : KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (w : List (Fin (groupDimension F))) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re)
    (g : G F ζ hζ) :
    Summable (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
      actualRightWord F ζ hζ w ((KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val)
        (rationalLift F ζ hζ (Quotient.out c) * g)) ∧
    actualRightWord F ζ hζ w
      (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
        (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
          (rationalLift F ζ hζ (Quotient.out c) * h)) g =
      ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
        actualRightWord F ζ hζ w ((KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val)
          (rationalLift F ζ hζ (Quotient.out c) * g) := by
  letI : AddCommGroup (KPMsRationalCompactCrossPairing.Source F ζ hζ 0) := Submodule.addCommGroup _
  letI : AddCommGroup (KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) := Submodule.addCommGroup _
  letI : AddCommGroup (KPContActualSphericalFlatStage.Stage F ζ hζ U) := Submodule.addCommGroup _
  by_cases hv : v = 0
  · subst v
    have hz : (KPContFlatSourceRecipe.flatR F ζ hζ s
        (0 : KPContActualSphericalFlatStage.Stage F ζ hζ U).val).val = fun _ => 0 := by
      funext h
      simp
    rw [hz, word_zero]
    simp only [tsum_zero]
    rw [word_zero]
    exact ⟨summable_zero, rfl⟩
  · let ι : ℂ →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U :=
      LinearMap.toSpanSingleton ℂ _ v
    have hι : Function.Injective ι := by
      intro a b hab
      exact (smul_left_injective ℂ (m := v) hv) hab
    have hterm (c : KPChamberBruhatTwoCells.RationalQuotient F) :
        KPContActualChamberNormalSeries.term F ζ hζ U ι (fun _ => 1) c s =
          fun h => (KPContFlatSourceRecipe.flatR F ζ hζ s v.val).val
            (rationalLift F ζ hζ (Quotient.out c) * h) := by
      funext h
      simp [KPContActualChamberNormalSeries.term, KPContActualSphericalFlatStage.L,
        KPContFlatCommonLevelKernel.L, ι, lift_eq]
    have hsum := KPGlobalResidualConstruction.ActualWordChamber.actualRightWord_summable
      F ζ hζ U ι (fun _ => 1) hι (differentiableOn_const _) w s hs g
    have he := KPGlobalResidualConstruction.ActualWordChamber.actualRightWord_eq_tsum
      F ζ hζ U ι (fun _ => 1) hι (differentiableOn_const _) w s hs g
    simp_rw [hterm, KPGlobalResidualConstruction.ActualWordChamber.actualRightWord_left_translate]
      at hsum
    refine ⟨hsum, ?_⟩
    unfold KPContActualChamberNormalSeries.E at he
    simp_rw [hterm, KPGlobalResidualConstruction.ActualWordChamber.actualRightWord_left_translate]
      at he
    exact he

 theorem literal_finite_word_chamber
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (m : Fin n → ℕ)
      (v : ∀ i, Fin (m i) → KPContActualSphericalFlatStage.Stage F ζ hζ (U i))
      (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
      (Q : ℂ → ℂ) (B : ∀ i, Fin (m i) → ℂ → ℂ),
      AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
      (∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        ∀ s ∈ Metric.ball (0 : ℂ) r, Q s ≠ 0) ∧
      (∀ i j, AnalyticOnNhd ℂ (B i j) KPContinuation.spectralDomain) ∧
      (∀ s ∈ KPContinuation.spectralDomain, ∀ g,
        Q s * f.val s g = ∑ i, ∑ j, B i j s * actualRightWord F ζ hζ (w i j)
          ((KPContFlatSourceRecipe.flatR F ζ hζ s (v i j).val).val) g) ∧
      ∀ s, (1 : ℝ) / 3 < s.re → ∀ g,
        Q s * eisenstein F ζ hζ K f s g = ∑ i, ∑ j, B i j s *
          actualRightWord F ζ hζ (w i j)
            (fun h => ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
              (KPContFlatSourceRecipe.flatR F ζ hζ s (v i j).val).val
                (rationalLift F ζ hζ (Quotient.out c) * h)) g := by
  obtain ⟨n, U, m, v, w, Q, B, hQ, hQ0, hdisk, hB, hrec⟩ :=
    literal_finite_word_reconstruction F ζ hζ K hK f
  refine ⟨n, U, m, v, w, Q, B, hQ, hQ0, hdisk, hB, hrec, ?_⟩
  intro s hs g
  have hΩ : s ∈ KPContinuation.spectralDomain :=
    KPContinuation.convergenceHalfPlane_subset_spectralDomain hs
  have hsum (i : Fin n) (j : Fin (m i)) :=
    spherical_word_chamber F ζ hζ (U i) (v i j) (w i j) s hs g
  unfold eisenstein
  rw [← tsum_mul_left]
  simp_rw [hrec s hΩ]
  rw [Summable.tsum_finsetSum (fun i _ =>
    summable_sum (fun j _ => (hsum i j).1.mul_left (B i j s)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j _ => (hsum i j).1.mul_left (B i j s))]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left, (hsum i j).2]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber

end
