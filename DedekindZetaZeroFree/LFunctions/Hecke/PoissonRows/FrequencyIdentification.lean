module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Identification

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawFrequencyPublicBridge

noncomputable section

open DedekindZetaZeroFree DedekindZetaZeroFree.PrincipalMellinComparison
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev Freq (D : FixedData S η) : Type := PrincipalMellinComparison.Frequency D.recipe

abbrev principal (D : FixedData S η) : Freq D := principalFrequency D.recipe

abbrev Raw (D : FixedData S η) : Type :=
  AllRowEuler.InitialSeparation.RawFrequency D.recipe.A

abbrev delSet {D : FixedData S η} (U : Raw D) : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  PrincipalMellinComparison.NonprincipalContinuation.RawHeckeRows.rawDeletionSet U

theorem context_correction (D : FixedData S η) :
    D.recipe.probe.correction = D.context.correction := rfl

def Row.toFreq {D : FixedData S η} (r : D.Row) : Freq D :=
  ⟨⟨r.u, r.isRep.choose⟩, r.isRep.choose_spec⟩

@[simp] theorem Row.toFreq_val {D : FixedData S η} (r : D.Row) : (Row.toFreq r).val.val = r.u :=
  rfl

theorem q_eq_frequencyNorm {D : FixedData S η} (r : D.Row) :
    D.q r = frequencyNorm D.recipe (Row.toFreq r) := rfl

theorem Row.toFreq_injective {D : FixedData S η} : Function.Injective (Row.toFreq (D := D)) := by
  intro r r' h
  exact FixedData.Row.u_injective (congrArg (fun x : Freq D => x.val.val) h)

theorem exists_raw (D : FixedData S η) :
    ∃ U : Freq D → Raw D, ∀ u : Freq D, (U u).u = u.val.val := by
  obtain ⟨_, U, _, hU⟩ := NonprincipalContinuation.RawHeckeRows.actual_context_and_raw_frequencies
    D.recipe
  exact ⟨U, hU⟩

structure Bridge (D : FixedData S η) (U : Freq D → Raw D)
    (P M : Freq D → Detector.PrimitiveFrequencyCharacter F) (plus minus : Freq D → ℂ → ℂ) :
    Prop where
  raw_u : ∀ u, (U u).u = u.val.val
  finite : ∀ u, (delSet (U u)).Finite
  plus_coeff : ∀ (u : Freq D) (I : D.recipe.A.Exterior),
    AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (P u) (delSet (U u)) I.val
  minus_coeff : ∀ (u : Freq D) (I : D.recipe.A.Exterior),
    AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target (U u) I =
      Detector.deletedPrimitiveIdealCoefficient F (M u) (delSet (U u)) I.val
  plus_nonprincipal : ∀ u, u ≠ principal D → ¬ (P u).character.IsPrincipal
  minus_nonprincipal : ∀ u, u ≠ principal D → ¬ (M u).character.IsPrincipal
  plus_diff : ∀ u, u ≠ principal D → DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re}
  minus_diff : ∀ u, u ≠ principal D → DifferentiableOn ℂ (minus u) {s : ℂ | 0 < s.re}
  plus_series : ∀ (u : Freq D) (s : ℂ), 1 < s.re →
    plus u s = AllRowEuler.InitialSeparation.plusL D.recipe.σ (U u) s
  minus_series : ∀ (u : Freq D) (s : ℂ), 1 < s.re →
    minus u s = AllRowEuler.InitialSeparation.minusL D.recipe.σ D.recipe.target (U u) s

theorem exists_bridge (D : FixedData S η) :
    ∃ (U : Freq D → Raw D) (P M : Freq D → Detector.PrimitiveFrequencyCharacter F)
      (plus minus : Freq D → ℂ → ℂ), Bridge D U P M plus minus := by
  classical
  obtain ⟨U, hU⟩ := exists_raw D
  obtain ⟨P, M, hfinite, hP, hM⟩ :=
    NonprincipalContinuation.RawHeckeRows.actual_raw_masked_inducers D.recipe D.context
      (context_correction D) U hU
  have hSD (u : Freq D) :
      (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ delSet (U u) :=
    Set.subset_union_left
  have hplus (u : Freq D) :=
    NonprincipalContinuation.RawHeckeRows.deleted_exterior_series_continuation D.recipe.A (P u)
      (delSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ (U u)) (hP u)
  have hminus (u : Freq D) :=
    NonprincipalContinuation.RawHeckeRows.deleted_exterior_series_continuation D.recipe.A (M u)
      (delSet (U u)) (hfinite u) (hSD u)
      (AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target (U u))
      (hM u)
  choose plus hpDiff hpEq using hplus
  choose minus hmDiff hmEq using hminus
  have hnp (u : Freq D) (hu : u ≠ principal D) :=
    NonprincipalContinuation.RawHeckeRows.actual_raw_inducers_nonprincipal
      D.recipe u (U u) (hU u) hu (P u) (M u) (hP u) (hM u)
  exact ⟨U, P, M, plus, minus,
    ⟨hU, hfinite, hP, hM, fun u hu => (hnp u hu).1, fun u hu => (hnp u hu).2,
      fun u hu => hpDiff u (hnp u hu).1, fun u hu => hmDiff u (hnp u hu).2, hpEq, hmEq⟩⟩

namespace Bridge

variable {D : FixedData S η} {U : Freq D → Raw D}
  {P M : Freq D → Detector.PrimitiveFrequencyCharacter F} {plus minus : Freq D → ℂ → ℂ}

theorem quotient_right_eq (h : Bridge D U P M plus minus) (u : Freq D) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries D.recipe u ξ w z =
      (D.recipe.L (6 * z) * plus u w *
        AllRowEuler.InitialSeparation.correctionProduct D.context (U u) ξ w z) / minus u ξ :=
  NonprincipalContinuation.Corridor.initial_continuation_agreement D.recipe D.context U plus minus
    (context_correction D) h.raw_u h.plus_series h.minus_series u ξ w z hξ hw hz

theorem quotient_corridors (h : Bridge D U P M plus minus) :
    ∃ Ω Ωleft : Set (ℂ × ℂ × ℂ),
      (∀ (u : Freq D) (ξ w z : ℂ), u ≠ principal D →
        ξ.re = 4 → w.re = 4 → z.re = 2 →
        separatedSeries D.recipe u ξ w z =
          NonprincipalContinuation.euler D.recipe D.context U plus minus u ξ w z) ∧
      IsOpen Ω ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip comparisonSigma₁ 4 →
        w ∈ comparisonClosedStrip (3 / 1000) 4 →
        z ∈ comparisonClosedStrip (2 / 5) 2 → (ξ, w, z) ∈ Ω) ∧
      (∀ u : Freq D, u ≠ principal D →
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ × ℂ =>
            NonprincipalContinuation.euler D.recipe D.context U plus minus u p.1 p.2.1 p.2.2) Ω) ∧
      IsOpen Ωleft ∧
      (∀ ξ w z : ℂ, ξ ∈ comparisonClosedStrip (499 / 500) comparisonSigma₁ →
        w.re = 3 / 1000 → z.re = 2 / 5 → (ξ, w, z) ∈ Ωleft) ∧
      (∀ u : Freq D, u ≠ principal D →
        DifferentiableOn ℂ
          (fun p : ℂ × ℂ × ℂ =>
            NonprincipalContinuation.numerator D.recipe D.context U plus u p.1 p.2.1 p.2.2)
          Ωleft) :=
  NonprincipalContinuation.actual_quotient_corridors D.recipe D.context U plus minus
    (context_correction D) h.raw_u h.plus_diff h.minus_diff h.plus_series h.minus_series

theorem plus_conductor_bound (h : Bridge D U P M plus minus) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Freq D,
      1 + (Ideal.absNorm (P u).conductor : ℝ) ≤ C * frequencyNorm D.recipe u :=
  NonprincipalContinuation.RightBound.ConductorEstimate.raw_plus_inducer_conductor_bound
    D.recipe U h.raw_u P h.plus_coeff

theorem plus_conductor_bound_row (h : Bridge D U P M plus minus) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : D.Row,
      1 + (Ideal.absNorm (P (Row.toFreq r)).conductor : ℝ) ≤ C * D.q r := by
  obtain ⟨C, hC, hb⟩ := h.plus_conductor_bound
  exact ⟨C, hC, fun r => hb (Row.toFreq r)⟩

theorem plus_eq_hecke_mul_mask (h : Bridge D U P M plus minus) (u : Freq D)
    (hu : u ≠ principal D) (w : ℂ) (hw : 0 < w.re) :
    plus u w = (RowHeckeBridge.hecke D.recipe.A (P u) (h.plus_nonprincipal u hu)).L w *
      Detector.finiteEulerDeletionMask F (delSet (U u))
        (fun v => (P u).character v.asIdeal) w :=
  NonprincipalContinuation.RightBound.ConductorEstimate.deleted_exterior_continuation_eq
    D.recipe.A (P u) (RowHeckeBridge.hecke D.recipe.A (P u) (h.plus_nonprincipal u hu))
    (delSet (U u)) (h.finite u) Set.subset_union_left
    (AllRowEuler.InitialSeparation.plusExteriorCoefficient D.recipe.σ (U u)) (h.plus_coeff u)
    (plus u) (h.plus_diff u hu) (h.plus_series u) w hw

theorem minus_eq_hecke_mul_mask (h : Bridge D U P M plus minus) (u : Freq D)
    (hu : u ≠ principal D) (w : ℂ) (hw : 0 < w.re) :
    minus u w = (RowHeckeBridge.hecke D.recipe.A (M u) (h.minus_nonprincipal u hu)).L w *
      Detector.finiteEulerDeletionMask F (delSet (U u))
        (fun v => (M u).character v.asIdeal) w :=
  NonprincipalContinuation.RightBound.ConductorEstimate.deleted_exterior_continuation_eq
    D.recipe.A (M u) (RowHeckeBridge.hecke D.recipe.A (M u) (h.minus_nonprincipal u hu))
    (delSet (U u)) (h.finite u) Set.subset_union_left
    (AllRowEuler.InitialSeparation.minusExteriorCoefficient D.recipe.σ D.recipe.target (U u))
    (h.minus_coeff u) (minus u) (h.minus_diff u hu) (h.minus_series u) w hw

theorem localCorrection_eq (h : Bridge D U P M plus minus) (u : Freq D)
    (p : LocalFiniteSums.ExteriorPrime D.recipe.A) (ξ w z : ℂ) :
    AllRowEuler.InitialSeparation.localCorrection D.context (U u) p ξ w z =
      if ((U u).j p).val = 0 then CorrectionFactors.goodFactor D.context p (U u).u ξ w z
      else CorrectionFactors.badFactor D.context p ((U u).j p) ((U u).theta D.context p) ξ w z :=
  rfl

end Bridge

end

end DedekindZetaZeroFree.Quantitative.RawFrequencyPublicBridge
