module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.UniformL2Tails
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberDomainEquations

open KPContActualChamberThreeL2Tails

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (level F ζ hζ C R P H U) R P H)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ
  (level F ζ hζ C R P H U) R P H μG hμG hR realization
local notation "u" => UJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "h" => HJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "dloc" => DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf
local notation "w" => smoothG F ζ hζ C R P H U ι f buffer χ source hι hf

structure Properties
    (r : KPContActualSectorCutoffGraphLimit.Cutoffs
      (U := level F ζ hζ C R P H U) (H := H)) : Prop where
  mem_domain : ∀ (k : ℕ) (s : ℂ), s ∈ V → u k s ∈ (Δ).domain

  local_action : ∀ (k : ℕ) (s : ℂ) (hs : s ∈ V),
    (Δ) ⟨u k s, mem_domain k s hs⟩ = dloc k s
  equation : ∀ (k : ℕ) (s : ℂ) (hs : s ∈ V),
    (Δ) ⟨u k s, mem_domain k s hs⟩ -
      KPContActualChamberCasimirJets.lambda F s • u k s =
    -h k s + ∑ j ∈ Finset.Icc 1 (min k 2),
      ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s

  uniform_bounds : ∀ (L : Set ℂ), IsCompact L → ∀ (hL : L ⊆ V) (k : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℂ) (hs : s ∈ L),
      ‖u k s‖ ≤ B ∧ ‖u k s‖ + ‖(Δ) ⟨u k s, mem_domain k s (hL hs)⟩‖ ≤ B

  uniform_graph_limit : ∀ (L : Set ℂ), IsCompact L → ∀ (hL : L ⊆ V) (k : ℕ),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (s : ℂ) (hs : s ∈ L),
      dist (KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n (w k s))
        (u k s, (Δ) ⟨u k s, mem_domain k s (hL hs)⟩) < ε

  zero_equation : ∀ (s : ℂ) (hs : s ∈ V),
    (Δ) ⟨u 0 s, mem_domain 0 s hs⟩ -
      KPContActualChamberCasimirJets.lambda F s • u 0 s = -h 0 s

  zero_representatives : ∀ s ∈ V,
    ((u 0 s).val : Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
      (fun x => KPContActualChamberNormalSeries.E F ζ hζ U ι f s
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) -
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s) x) ∧
    ((h 0 s).val : Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.commutator s)

   abbrev GS := KPContActualSectorCutoffGraphLimit.GraphSection
    (U := level F ζ hζ C R P H U) (H := H)

   def gs (k : ℕ) (s : ℂ) (hs : s ∈ V) : GS F ζ hζ C R P H U :=
    ⟨smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s, by
       exact (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).1.2,
     by exact (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.2.2,
     by exact (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.2.1.2⟩

  private lemma sectionClass_gs (k : ℕ) (s : ℂ) (hs : s ∈ V) :
      KPContActualSectorCutoffGraphLimit.sectionClass
        (U := level F ζ hζ C R P H U) (H := H)
        (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs) = u k s := rfl

  private lemma laplacianClass_gs (k : ℕ) (s : ℂ) (hs : s ∈ V) :
      KPContActualSectorCutoffGraphLimit.laplacianClass
        (U := level F ζ hζ C R P H U) (H := H)
        (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs) = dloc k s := rfl

  private lemma toSector_ofReal_norm_sq
      (x : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ
        (level F ζ hζ C R P H U) R P H) :
      ENNReal.ofReal (‖KPContSectorLineL2Isometry.toSector F ζ hζ
        (level F ζ hζ C R P H U) R P H x‖ ^ 2) =
        KPContSectorLineL2Isometry.normIntegral F ζ hζ
          (level F ζ hζ C R P H U) R P H x.val := by
    have h2 : (KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ
        (level F ζ hζ C R P H U) R P H)
        (KPContSectorLineL2Isometry.toSector F ζ hζ
          (level F ζ hζ C R P H U) R P H x) =
        KPContSectorLineL2Isometry.mk F ζ hζ (level F ζ hζ C R P H U) R P H x := by
      have hline : KPContSectorLineL2Isometry.lineToSector F ζ hζ
          (level F ζ hζ C R P H U) R P H
          (KPContSectorLineL2Isometry.mk F ζ hζ (level F ζ hζ C R P H U) R P H x) =
          KPContSectorLineL2Isometry.toSector F ζ hζ
            (level F ζ hζ C R P H U) R P H x := rfl
      rw [← hline]
      exact LinearEquiv.symm_apply_apply _ _
    have hnorm : ‖KPContSectorLineL2Isometry.toSector F ζ hζ
        (level F ζ hζ C R P H U) R P H x‖ =
        ‖KPContSectorLineL2Isometry.mk F ζ hζ (level F ζ hζ C R P H U) R P H x‖ := by
      rw [← h2]
      exact (LinearIsometryEquiv.norm_map _ _).symm
    rw [hnorm]
    exact KPContSectorLineL2Isometry.ofReal_norm_sq F ζ hζ (level F ζ hζ C R P H U) R P H x

  private lemma UJet_ofReal_norm_sq (k : ℕ) (s : ℂ) :
      ENNReal.ofReal (‖u k s‖ ^ 2) =
        squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf 0 k s := by
    rw [show u k s = KPContSectorLineL2Isometry.toSector F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (borelG F ζ hζ C R P H U ι f buffer χ source hι hf k s) from rfl]
    rw [toSector_ofReal_norm_sq]
    simp [squareIntegral, squaredDensity, baseMeasure, KPContSectorLineL2Isometry.normIntegral,
      borelG]

  private lemma DeltaJet_ofReal_norm_sq (k : ℕ) (s : ℂ) :
      ENNReal.ofReal (‖dloc k s‖ ^ 2) =
        squareIntegral F ζ hζ C R P H U ι f buffer χ source hι hf 2 k s := by
    rw [show dloc k s = KPContSectorLineL2Isometry.toSector F ζ hζ
        (level F ζ hζ C R P H U) R P H
        (borelDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) from rfl]
    rw [toSector_ofReal_norm_sq]
    simp [squareIntegral, squaredDensity, baseMeasure, KPContSectorLineL2Isometry.normIntegral,
      borelDelta]

  private lemma key
      (r : KPContActualSectorCutoffGraphLimit.Cutoffs
        (U := level F ζ hζ C R P H U) (H := H))
      (hr : KPContActualSectorCutoffGraphLimit.Properties F ζ hζ
        (level F ζ hζ C R P H U) R P H μG hμG hR realization r)
      (k : ℕ) (s : ℂ) (hs : s ∈ V) :
      ∃ hw : u k s ∈ (Δ).domain, (Δ) ⟨u k s, hw⟩ = dloc k s := by
    obtain ⟨hw, hact⟩ := hr.closed_graph_consequence
      (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs)
    refine ⟨sectionClass_gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs ▸ hw, ?_⟩
    calc (Δ) ⟨u k s, _⟩
        = (Δ) ⟨KPContActualSectorCutoffGraphLimit.sectionClass
              (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs), hw⟩ := by
          congr 1
      _ = KPContActualSectorCutoffGraphLimit.laplacianClass
            (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs) := hact
      _ = dloc k s :=
          laplacianClass_gs F ζ hζ C R P H U ι hι f hf buffer χ source k s hs

  private lemma three_uniform_tails
      (htail : KPContActualChamberThreeL2Tails.Properties F ζ hζ C R P H U
        ι f buffer χ source hι hf)
      (L : Set ℂ) (hL : IsCompact L) (hLsub : L ⊆ V) (k : ℕ) :
      KPContActualSectorCutoffGraphLimit.ThreeUniformTails
        (U := level F ζ hζ C R P H U) (H := H)
        (fun i : ULift ↥L =>
          gs F ζ hζ C R P H U ι hι f hf buffer χ source k i.1.1 (hLsub i.1.2)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro ε hε
      obtain ⟨A, hA'⟩ := htail.uniform_tails L hL hLsub k (ε / 2) (by positivity)
      obtain ⟨_hA, hAll⟩ := hA'
      refine ⟨Nat.ceil A, ?_⟩
      intro n hn i
      have hAn : A ≤ (n : ℝ) := le_trans (Nat.le_ceil A) (by exact_mod_cast hn)
      have hsq := hAll (n : ℝ) hAn (0 : Fin 3) i.1.1 i.1.2
      refine lt_of_le_of_lt ?_
        ((ENNReal.ofReal_lt_ofReal_iff (p := ε / 2) (q := ε) (by positivity : (0 : ℝ) < ε)).mpr (by linarith))
      exact hsq
    · intro ε hε
      obtain ⟨A, hA'⟩ := htail.uniform_tails L hL hLsub k (ε / 2) (by positivity)
      obtain ⟨_hA, hAll⟩ := hA'
      refine ⟨Nat.ceil A, ?_⟩
      intro n hn i
      have hAn : A ≤ (n : ℝ) := le_trans (Nat.le_ceil A) (by exact_mod_cast hn)
      have hsq := hAll (n : ℝ) hAn (1 : Fin 3) i.1.1 i.1.2
      refine lt_of_le_of_lt ?_
        ((ENNReal.ofReal_lt_ofReal_iff (p := ε / 2) (q := ε) (by positivity : (0 : ℝ) < ε)).mpr (by linarith))
      exact hsq
    · intro ε hε
      obtain ⟨A, hA'⟩ := htail.uniform_tails L hL hLsub k (ε / 2) (by positivity)
      obtain ⟨_hA, hAll⟩ := hA'
      refine ⟨Nat.ceil A, ?_⟩
      intro n hn i
      have hAn : A ≤ (n : ℝ) := le_trans (Nat.le_ceil A) (by exact_mod_cast hn)
      have hsq := hAll (n : ℝ) hAn (2 : Fin 3) i.1.1 i.1.2
      refine lt_of_le_of_lt ?_
        ((ENNReal.ofReal_lt_ofReal_iff (p := ε / 2) (q := ε) (by positivity : (0 : ℝ) < ε)).mpr (by linarith))
      exact hsq

  private lemma main_assembly
      (htail : KPContActualChamberThreeL2Tails.Properties F ζ hζ C R P H U
        ι f buffer χ source hι hf) :
      ∃ r : KPContActualSectorCutoffGraphLimit.Cutoffs
          (U := level F ζ hζ C R P H U) (H := H),
        KPContActualSectorCutoffGraphLimit.Properties F ζ hζ
          (level F ζ hζ C R P H U) R P H μG hμG hR realization r ∧
        Properties F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source r := by
    obtain ⟨r, hr⟩ := kp_cont_actual_sector_cutoff_graph_limit F ζ hζ μG hμG
      (level F ζ hζ C R P H U) R hR P H realization
    refine ⟨r, hr, ?_⟩
    have hkey := key F ζ hζ C R P H U μG hμG hR realization ι hι f hf buffer χ source r hr
    have hmemfun : ∀ (k : ℕ) (s : ℂ), s ∈ V → u k s ∈ (Δ).domain :=
      fun k s hs => (hkey k s hs).choose
    have hactfun : ∀ (k : ℕ) (s : ℂ) (hs : s ∈ V),
        (Δ) ⟨u k s, hmemfun k s hs⟩ = dloc k s :=
      fun k s hs => (hkey k s hs).choose_spec
    have heqfun : ∀ (k : ℕ) (s : ℂ) (hs : s ∈ V),
        (Δ) ⟨u k s, hmemfun k s hs⟩ -
          KPContActualChamberCasimirJets.lambda F s • u k s =
        -h k s + ∑ j ∈ Finset.Icc 1 (min k 2),
          ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s := by
      intro k s hs
      rw [hactfun k s hs, htail.differential_rhs_class k s hs]
      abel
    have hboundfun : ∀ (L : Set ℂ), IsCompact L → ∀ (hL : L ⊆ V) (k : ℕ),
        ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℂ) (hs : s ∈ L),
          ‖u k s‖ ≤ B ∧ ‖u k s‖ + ‖(Δ) ⟨u k s, hmemfun k s (hL hs)⟩‖ ≤ B := by
      intro L hL hLsub k
      obtain ⟨B, hB0, hB⟩ := htail.uniform_bounds L hL hLsub k
      refine ⟨2 * Real.sqrt B + 1, by positivity, ?_⟩
      intro s hs
      have h0 := hB 0 s hs
      have h2 := hB 2 s hs
      rw [← UJet_ofReal_norm_sq F ζ hζ C R P H U ι hι f hf buffer χ source k s] at h0
      rw [← DeltaJet_ofReal_norm_sq F ζ hζ C R P H U ι hι f hf buffer χ source k s] at h2
      have hs0 : ‖u k s‖ ^ 2 ≤ B := (ENNReal.ofReal_le_ofReal_iff hB0).mp h0
      have hs2 : ‖dloc k s‖ ^ 2 ≤ B := (ENNReal.ofReal_le_ofReal_iff hB0).mp h2
      have hn0 : ‖u k s‖ ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hs0
      have hn2 : ‖dloc k s‖ ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hs2
      rw [hactfun k s (hLsub hs)]
      exact ⟨by linarith [Real.sqrt_nonneg B], by linarith [Real.sqrt_nonneg B]⟩
    have hgraphfun : ∀ (L : Set ℂ), IsCompact L → ∀ (hL : L ⊆ V) (k : ℕ),
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (s : ℂ) (hs : s ∈ L),
          dist (KPContActualSectorCutoffGraphLimit.graphPair μG hμG hR realization r n (w k s))
            (u k s, (Δ) ⟨u k s, hmemfun k s (hL hs)⟩) < ε := by
      intro L hL hLsub k ε hε
      have hfam := three_uniform_tails F ζ hζ C R P H U ι hι f hf buffer χ source htail L hL hLsub k
      obtain ⟨N, hN⟩ := hr.uniform_graph_limit (I := ULift ↥L)
        (fun i : ULift ↥L =>
          gs F ζ hζ C R P H U ι hι f hf buffer χ source k i.1.1 (hLsub i.1.2)) hfam ε hε
      refine ⟨N, ?_⟩
      intro n hn s hs
      have hconv := hN n hn (ULift.up ⟨s, hs⟩)
      dsimp only at hconv
      have hpair : (KPContActualSectorCutoffGraphLimit.sectionClass
          (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s (hLsub hs)),
          KPContActualSectorCutoffGraphLimit.laplacianClass
          (gs F ζ hζ C R P H U ι hι f hf buffer χ source k s (hLsub hs))) =
          (u k s, (Δ) ⟨u k s, hmemfun k s (hLsub hs)⟩) := by
        rw [sectionClass_gs F ζ hζ C R P H U ι hι f hf buffer χ source k s (hLsub hs),
            laplacianClass_gs F ζ hζ C R P H U ι hι f hf buffer χ source k s (hLsub hs)]
        exact (congrArg (fun t => (u k s, t)) (hactfun k s (hLsub hs))).symm
      rw [hpair] at hconv
      simpa [gs] using hconv
    have hzerofun : ∀ (s : ℂ) (hs : s ∈ V),
        (Δ) ⟨u 0 s, hmemfun 0 s hs⟩ -
          KPContActualChamberCasimirJets.lambda F s • u 0 s = -h 0 s := by
      intro s hs
      simpa using heqfun 0 s hs
    have hzerorepfun : ∀ s ∈ V,
        ((u 0 s).val : Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
          (fun x => KPContActualChamberNormalSeries.E F ζ hζ U ι f s
            (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) -
            KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
              (source.descent.cutoff s) x) ∧
        ((h 0 s).val : Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
            (source.descent.commutator s) := by
      intro s hs
      have hh := htail.actual_ae 0 s hs
      refine ⟨?_, ?_⟩
      · have hg : KPContActualChamberThreeL2Tails.g F ζ hζ C R P H U ι f buffer χ source 0 s =
            (fun x => KPContActualChamberNormalSeries.E F ζ hζ U ι f s
              (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) -
              KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
                (source.descent.cutoff s) x) := by
          funext x
          simp [KPContActualChamberThreeL2Tails.g, iteratedDerivWithin_zero]
        rw [← hg]
        exact hh.1
      · have hh' : KPContActualChamberThreeL2Tails.h F ζ hζ C R P H U ι f buffer χ source 0 s =
            KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
              (source.descent.commutator s) := by
          funext x
          simp [KPContActualChamberThreeL2Tails.h, iteratedDerivWithin_zero]
        rw [← hh']
        exact hh.2.1
    exact ⟨hmemfun, hactfun, heqfun, hboundfun, hgraphfun, hzerofun, hzerorepfun⟩

end DedekindZetaZeroFree.KPContActualChamberDomainEquations

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_domain_equations
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
      KPContinuation.spectralDomain f χ) :
    ∃ r : KPContActualSectorCutoffGraphLimit.Cutoffs
        (U := KPContActualAllCuspSource.level F ζ hζ C R P H U) (H := H),
      KPContActualSectorCutoffGraphLimit.Properties F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H μG hμG hR realization r ∧
      KPContActualChamberDomainEquations.Properties F ζ hζ C R P H U μG hμG hR realization
        ι hι f hf buffer χ source r := by
  have htail := kp_cont_actual_chamber_three_l2_tails F ζ hζ C R P H U realization
    ι hι f hf buffer χ source
  exact KPContActualChamberDomainEquations.main_assembly F ζ hζ C R P H U μG hμG hR
    realization ι hι f hf buffer χ source htail

end DedekindZetaZeroFree

end
