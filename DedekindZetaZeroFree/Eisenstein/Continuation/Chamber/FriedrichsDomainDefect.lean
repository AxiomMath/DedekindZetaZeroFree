module

public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.GraphHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberDomainDefect

abbrev V : Set ℂ := KPContActualChamberNormalSeries.V

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Covered := KPContActualAllCuspSource.Covered F ζ hζ C R P H U
abbrev Sector := KPContActualAllCuspSource.Sector F ζ hζ C R P H U
abbrev SmoothSections := KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
abbrev measure := KPContActualAllCuspSource.measure F ζ hζ C R P H U

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def seriesScalar (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  KPChamberL2Defect.series (KPContActualChamberNormalSeries.lift F ζ hζ)
    (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U)
    (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s

variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B
  KPContinuation.spectralDomain f χ)

def defectScalar (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  seriesScalar F ζ hζ C R P H U ι f s -
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff s)

def sourceScalar (s : ℂ) : Covered F ζ hζ C R P H U → ℂ :=
  KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.commutator s)

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
  (level F ζ hζ C R P H U) R P H)

abbrev laplacian := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ
  (level F ζ hζ C R P H U) R P H μG hμG hR realization

local notation "Δ" => laplacian F ζ hζ C R P H U μG hμG hR realization
local notation "HU" => Sector F ζ hζ C R P H U
local notation "L2" => KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R
  (level F ζ hζ C R P H U)
local notation "lam" => KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ)

structure DomainConclusions (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) where

  normal : KPContActualChamberNormalSeries.ChamberConclusions F ζ hζ C R P H U ι f hι hf

  series : ℂ → SmoothSections F ζ hζ C R P H U
  series_formula : ∀ s ∈ V,
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
      seriesScalar F ζ hζ C R P H U ι f s

  series_lift : ∀ s ∈ V, ∀ g : KPContActualChamberNormalSeries.G F ζ hζ,
    KPContActualCutoffSmoothDescent.lift F ζ hζ C R P H U (series s)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
        KPContActualChamberNormalSeries.E F ζ hζ U ι f s g

  series_casimir : ∀ s ∈ V,
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (z : KPFiniteCuspAtlas.SymmetricSpace F),
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      ((series s).val i).val z = lam s * ((series s).val i).val z

  u : ℕ → ℂ → (Δ).domain
  defect_memLp : ∀ k s, s ∈ V → MemLp
    (KPChamberL2Defect.scalarJet (defectScalar F ζ hζ C R P H U ι f B χ source) k s)
    2 (measure F ζ hζ C R P H U)

  defect_ae : ∀ k s, s ∈ V →
    ((u k s : HU) : L2) =ᵐ[measure F ζ hζ C R P H U]
      KPChamberL2Defect.scalarJet (defectScalar F ζ hζ C R P H U ι f B χ source) k s
  source_jet_memLp : ∀ k s, s ∈ V → MemLp
    (KPChamberL2Defect.scalarJet (sourceScalar F ζ hζ C R P H U ι f B χ source) k s)
    2 (measure F ζ hζ C R P H U)

  source_jet_ae : ∀ k s, s ∈ V →
    ((iteratedDerivWithin k source.h V s : HU) : L2) =ᵐ[measure F ζ hζ C R P H U]
      KPChamberL2Defect.scalarJet (sourceScalar F ζ hζ C R P H U ι f B χ source) k s
  equation : ∀ s ∈ V, Δ (u 0 s) - lam s • (u 0 s : HU) = -source.h s

  differentiated_equation : ∀ k s, s ∈ V →
    Δ (u k s) - lam s • (u k s : HU) = -iteratedDerivWithin k source.h V s +
      KPChamberL2Defect.spectralCorrection (Module.finrank ℚ F / 2)
        (fun j z => (u j z : HU)) k s
  derivative_identification : ∀ k s, s ∈ V →
    iteratedDerivWithin k (fun z => (u 0 z : HU)) V s = (u k s : HU)

  graph_holomorphic : ∀ k,
    DifferentiableOn ℂ (fun s => ((u k s : HU), Δ (u k s))) V

  graph_derivative_identification : ∀ k s, s ∈ V →
    iteratedDerivWithin k (fun z => ((u 0 z : HU), Δ (u 0 z))) V s =
      ((u k s : HU), Δ (u k s))
  graph_locally_bounded : ∀ k, ∀ K : Set ℂ, IsCompact K → K ⊆ V →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K,
      ‖(u k s : HU)‖ ≤ M ∧ KPChamberL2Defect.graphNorm Δ (u k s) ≤ M

end DedekindZetaZeroFree.KPContActualChamberDomainDefect

namespace DedekindZetaZeroFree

private theorem domainDefect_clm_jet
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (L : A →L[ℂ] B) (g : ℂ → A) (O : Set ℂ) (hO : UniqueDiffOn ℂ O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) (hg : ContDiffWithinAt ℂ k g O s) :
    iteratedDerivWithin k (fun z => L (g z)) O s = L (iteratedDerivWithin k g O s) := by
  unfold iteratedDerivWithin
  change ((iteratedFDerivWithin ℂ k (L ∘ g) O s) _) = _
  rw [L.iteratedFDerivWithin_comp_left hg hO hs le_rfl]
  rfl

private theorem domainDefect_leibniz
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    (F : Type) [Field F] [NumberField F]
    (u : ℕ → ℂ → A) (z : ℕ → ℂ → A × A) (h : ℂ → A)
    (hu : DifferentiableOn ℂ (u 0) KPContActualChamberDomainDefect.V)
    (hz : DifferentiableOn ℂ (z 0) KPContActualChamberDomainDefect.V)
    (huj : ∀ k s, s ∈ KPContActualChamberDomainDefect.V →
      iteratedDerivWithin k (u 0) KPContActualChamberDomainDefect.V s = u k s)
    (hzj : ∀ k s, s ∈ KPContActualChamberDomainDefect.V →
      iteratedDerivWithin k (z 0) KPContActualChamberDomainDefect.V s = z k s)
    (he : ∀ s ∈ KPContActualChamberDomainDefect.V,
      h s = KPContActualChamberCasimirJets.lambda F s • u 0 s - (z 0 s).2)
    (k : ℕ) (s : ℂ) (hs : s ∈ KPContActualChamberDomainDefect.V) :
    iteratedDerivWithin k h KPContActualChamberDomainDefect.V s =
      KPContActualChamberCasimirJets.lambda F s • u k s - (z k s).2 +
        ∑ j ∈ Finset.Icc 1 (min k 2),
          ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s := by
  let V := KPContActualChamberDomainDefect.V
  have hopen : IsOpen V := KPChamberL2Defect.chamber_isOpen
  have hdiff : UniqueDiffOn ℂ V := hopen.uniqueDiffOn
  have hl : ContDiffWithinAt ℂ k (KPContActualChamberCasimirJets.lambda F) V s := by
    unfold KPContActualChamberCasimirJets.lambda KPContinuation.spectralCoordinate
    fun_prop
  have hu' : ContDiffWithinAt ℂ k (u 0) V s := (hu.contDiffOn hopen).contDiffWithinAt hs
  have hz' : ContDiffWithinAt ℂ k (z 0) V s := (hz.contDiffOn hopen).contDiffWithinAt hs
  have hsub := iteratedDerivWithin_sub hs hdiff (hl.smul hu') hz'.snd
  rw [(iteratedDerivWithin_congr he) hs]
  rw [show (fun t => KPContActualChamberCasimirJets.lambda F t • u 0 t - (z 0 t).2) =
    (KPContActualChamberCasimirJets.lambda F • u 0) - (fun t => (z 0 t).2) from rfl]
  rw [hsub]
  have hsnd := domainDefect_clm_jet (ContinuousLinearMap.snd ℂ A A) (z 0) V hdiff k s hs hz'
  change iteratedDerivWithin k (fun t => (z 0 t).2) V s = (iteratedDerivWithin k (z 0) V s).2 at hsnd
  rw [hsnd, hzj k s hs]
  rw [iteratedDerivWithin_smul hs hdiff hl hu']
  simp_rw [huj _ s hs]
  have hcast (j : ℕ) (v : A) (c : ℂ) : (Nat.choose k j) • c • v = ((Nat.choose k j : ℂ) * c) • v := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp_rw [hcast]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.sub_zero, iteratedDerivWithin_zero, Nat.cast_one, one_mul]
  have hsum : (∑ j ∈ Finset.range k,
      ((Nat.choose k (j+1) : ℂ) * KPContActualChamberCasimirJets.lambdaJet F (j+1) s) • u (k-(j+1)) s) =
      ∑ j ∈ Finset.Icc 1 (min k 2),
      ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s := by
    let T := fun j => ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • u (k-j) s
    change (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 (min k 2), T j
    rw [show (∑ j ∈ Finset.range k, T (j+1)) = ∑ j ∈ Finset.Icc 1 k, T j by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]; simp [add_comm]]
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      exact ⟨hj.1, hj.2.trans (min_le_left _ _)⟩
    · intro j hj hn
      have hj2 : 2 < j := by simp only [Finset.mem_Icc] at hj hn; omega
      simp [T, (KPContActualChamberCasimirJets.spectral_jets F s hs).2.2.2.2 j hj2]
  change (_ + _ • _) - _ = _
  have hsum' : (∑ j ∈ Finset.range k,
      ((Nat.choose k (j+1) : ℂ) * iteratedDerivWithin (j+1) (KPContActualChamberCasimirJets.lambda F) V s) • u (k-(j+1)) s) = _ := hsum
  rw [hsum']
  abel

open KPContActualSphericalFlatStage in
private theorem domainDefect_stage
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (hι : Function.Injective ι) :
    KPContActualSphericalFlatStage.StageConclusions F ζ hζ C R P H U ι := by
  refine {
    source := sourceFlat_eq F ζ hζ C R P H U ι
    covariance := covariance F ζ hζ U ι
    smooth_holomorphy := smoothHolomorphy F ζ hζ U ι hι
    archimedean_parameter := ?_
    incoming := ?_
    coefficient := ?_
    frame_recipe := ?_
    transition := ?_
    metric_radial := ?_
    casimir := ?_
    rational_index := ?_ }
  · intro s v u g
    have he : 1 + 2 * KPIncomingCasimir.nu s = 4 / 3 + 2 * s := by
      unfold KPIncomingCasimir.nu
      ring
    rw [he]
    exact KPContFlatArchDiagonalMultiplier.flatR_covariance F ζ hζ s u
      (coreInclusion F ζ hζ U ι v) g
  · intro a s hs v t b
    simpa [KPIncomingCasimir.heightFactor, KPIncomingCasimir.nu] using
      incoming_formula F ζ hζ C R P H U ι a s hs v t b
  · intro a j
    exact ⟨fun s hs v => KPContFlatCuspCoefficientTransition.locally_parallel
      F ζ hζ C R P H U a ι s hs v j,
      fun b => KPContFlatCuspCoefficientTransition.frameCoefficient_holomorphic
        F ζ hζ C R P H U a ι j b⟩
  · intro a s hs v b
    exact KPContFlatCuspCoefficientTransition.frameCoefficient_formula
      F ζ hζ C R P H U a ι s hs v b
  · intro a s hs v g b q
    exact ⟨(KPContFlatCuspCoefficientTransition.transport_formula F ζ hζ C R P H U a ι
      s hs v g b).1,
      (KPContFlatCuspIncomingEvaluation.frequencies F ζ hζ C R P H U a).constantSystem.transition_formula
        g ((KPContFlatCuspIncomingEvaluation.b F ζ hζ C R P H U a ι s hs v).val b) q⟩
  · intro a s hs v p q
    change KPContFlatCuspCasimirSpecialization.Δloc _ _ _ = _
    exact KPContFlatCuspCasimirSpecialization.metric_radial_scalar F ζ hζ C R P H U ι a s hs v p q
  · intro a s hs v q z
    change KPContFlatCuspCasimirSpecialization.Δloc _ _ _ = _
    exact KPContFlatCuspCasimirSpecialization.incoming_casimir_scalar F ζ hζ C R P H U ι a s hs v q z
  · intro s v g γ
    simpa only [KPContFlatRationalCosetCovariance.cosetEquiv_mk,
      KPContFlatRationalCosetCovariance.L, L,
      KPContFlatCommonLevelKernel.L, LinearMap.comp_apply, Submodule.coe_subtype] using
      KPContFlatRationalCosetCovariance.rationalTerm_transport_mk F ζ hζ s
        (coreInclusion F ζ hζ U ι v) g γ

set_option maxHeartbeats 4000000 in

theorem kp_cont_actual_chamber_domain_defect
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (T : ℝ)
    (hT : (H.atlas (KPContActualChamberDomainDefect.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H T,
      ∃ source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B
          KPContinuation.spectralDomain f χ,
        Nonempty (KPContActualChamberDomainDefect.DomainConclusions F ζ hζ C R P H U
          ι f B χ source μG hμG hR realization hι hf) := by
  classical
  open KPContActualChamberDomainDefect in
  have hStage := domainDefect_stage F ζ hζ C R P H U ι hι
  obtain ⟨B, ⟨source⟩⟩ := kp_cont_actual_all_cusp_source F ζ hζ C R P H U realization
    ι hι hStage KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen
    (fun _ h => h) f hf T hT χ
  have htail := kp_cont_actual_chamber_three_l2_tails F ζ hζ C R P H U realization
    ι hι f hf B χ source
  obtain ⟨r, hr, de, gh⟩ := kp_cont_actual_chamber_graph_holomorphy.{_, 0} F ζ hζ C R P H U
    μG hμG hR realization ι hι f hf B χ source
  let v := KPContActualChamberThreeL2Tails.UJet F ζ hζ C R P H U ι f B χ source hι hf
  let h := KPContActualChamberThreeL2Tails.HJet F ζ hζ C R P H U ι f B χ source hι hf
  let z := KPContActualChamberGraphHolomorphy.ZJet F ζ hζ C R P H U μG hμG hR realization
    ι hι f hf B χ source de
  let Δ := KPContActualChamberDomainDefect.laplacian F ζ hζ C R P H U μG hμG hR realization
  let u : ℕ → ℂ → Δ.domain := fun k s =>
    if hs : s ∈ KPContActualChamberDomainDefect.V then ⟨v k s, de.mem_domain k s hs⟩ else 0
  have hu : ∀ k s, s ∈ KPContActualChamberDomainDefect.V →
      (u k s : KPContActualChamberDomainDefect.Sector F ζ hζ C R P H U) = v k s := by
    intro k s hs
    simp [u, hs]
  have hz : ∀ k s, s ∈ KPContActualChamberDomainDefect.V →
      z k s = ((u k s : KPContActualChamberDomainDefect.Sector F ζ hζ C R P H U), Δ (u k s)) := by
    intro k s hs
    simp [z, KPContActualChamberGraphHolomorphy.ZJet, u, hs, v, Δ]
  have hV : KPContActualChamberDomainDefect.V ⊆ KPContinuation.spectralDomain := by
    intro s hs
    change (1 : ℝ)/3 < s.re at hs
    change -(1 : ℝ)/6 < s.re
    linarith
  have hh0 : ∀ s ∈ KPContActualChamberDomainDefect.V, h 0 s = source.h s := by
    intro s hs
    apply Subtype.ext
    apply MeasureTheory.Lp.ext
    exact (de.zero_representatives s hs).2.trans (source.source_ae s (hV hs)).symm
  have he : ∀ s ∈ KPContActualChamberDomainDefect.V,
      source.h s = KPContActualChamberCasimirJets.lambda F s • v 0 s - (z 0 s).2 := by
    intro s hs
    have hd := de.zero_equation s hs
    change Δ ⟨v 0 s, de.mem_domain 0 s hs⟩ - KPContActualChamberCasimirJets.lambda F s • v 0 s = -h 0 s at hd
    rw [hh0 s hs] at hd
    have hz' := hz 0 s hs
    have huv := hu 0 s hs
    have hdu : u 0 s = ⟨v 0 s, de.mem_domain 0 s hs⟩ := by apply Subtype.ext; exact huv
    rw [hdu] at hz'
    rw [hz']
    dsimp only
    have hh := congrArg Neg.neg hd
    simp only [neg_sub, neg_neg] at hh
    exact hh.symm
  have hhj : ∀ k s, s ∈ KPContActualChamberDomainDefect.V →
      iteratedDerivWithin k source.h KPContActualChamberDomainDefect.V s = h k s := by
    intro k s hs
    have hj := domainDefect_leibniz F v z source.h (gh.value_holomorphic 0)
      (gh.product_holomorphic 0) gh.value_derivatives gh.product_derivatives he k s hs
    have hd := de.equation k s hs
    have hz' : (z k s).2 = Δ ⟨v k s, de.mem_domain k s hs⟩ := by
      simp [z, KPContActualChamberGraphHolomorphy.ZJet, hs, v, Δ]
    change Δ ⟨v k s, de.mem_domain k s hs⟩ - KPContActualChamberCasimirJets.lambda F s • v k s =
      -h k s + ∑ j ∈ Finset.Icc 1 (min k 2), ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) • v (k-j) s at hd
    rw [hj, hz']
    have hh := congrArg Neg.neg hd
    simp only [neg_sub, neg_add, neg_neg] at hh
    rw [hh]
    abel
  let series : ℂ → KPContActualChamberDomainDefect.SmoothSections F ζ hζ C R P H U := fun s =>
    if hs : s ∈ KPContActualChamberDomainDefect.V then
      ⟨KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s,
        KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf 0 s hs⟩
    else 0
  have hseries : ∀ s ∈ KPContActualChamberDomainDefect.V,
      KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
        KPContActualChamberDomainDefect.seriesScalar F ζ hζ C R P H U ι f s := by
    intro s hs
    have hline : (series s).val = KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf 0 s := by
      simp [series, hs]
    have hscalar : KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (series s) =
        (KPContActualChamberCasimirJets.coveredJet F ζ hζ C R P H U ι f hι hf 0 s).val := by
      unfold KPContActualCutoffSmoothDescent.scalar
      change ((KPContSectorScalarLineAlgebra.S F ζ hζ
        (KPContActualChamberDomainDefect.level F ζ hζ C R P H U) R P H).symm (series s).val).val = _
      rw [hline]
      simp only [KPContActualChamberCasimirJets.lineJet, LinearEquiv.symm_apply_apply]
    rw [hscalar]
    funext x
    simp [KPContActualChamberCasimirJets.coveredJet, hs, KPContActualChamberCasimirJets.jet,
      KPContActualChamberDomainDefect.seriesScalar, KPContActualChamberNormalSeries.E,
      KPChamberL2Defect.series, KPContActualChamberNormalSeries.term]
  have hgscalar : ∀ k s,
      KPContActualChamberThreeL2Tails.g F ζ hζ C R P H U ι f B χ source k s =
      KPChamberL2Defect.scalarJet (KPContActualChamberDomainDefect.defectScalar
        F ζ hζ C R P H U ι f B χ source) k s := by
    intro k s
    rfl
  refine ⟨B, source, ⟨{
    normal := kp_cont_actual_chamber_normal_series F ζ hζ C R P H U ι hι f hf
    series := series
    series_formula := hseries
    series_lift := ?_
    series_casimir := ?_
    u := u
    defect_memLp := ?_
    defect_ae := ?_
    source_jet_memLp := ?_
    source_jet_ae := ?_
    equation := ?_
    differentiated_equation := ?_
    derivative_identification := ?_
    graph_holomorphic := ?_
    graph_derivative_identification := ?_
    graph_locally_bounded := ?_ }⟩⟩
  · intro s hs g
    unfold KPContActualCutoffSmoothDescent.lift
    rw [hseries s hs]
    obtain ⟨e, he, heval, _⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
    change KPContActualChamberDomainDefect.seriesScalar F ζ hζ C R P H U ι f s _ = _
    unfold KPContActualChamberDomainDefect.seriesScalar
    rw [← heval s hs]
    exact he s hs g
  · intro s hs i x
    simpa only [series, dif_pos hs, KPContActualChamberCasimirJets.lambda, KPContActualChamberCasimirJets.d] using
      KPGlobalResidualConstruction.ActualMeanZeroSection.actual_component_casimir
        F ζ hζ C R P H U ι hι f hf s hs i x
  · intro k s hs
    rw [← hgscalar]
    exact (htail.covered_memLp k s hs).1
  · intro k s hs
    rw [hu k s hs, ← hgscalar]
    exact (htail.actual_ae k s hs).1
  · intro k s hs
    exact (htail.covered_memLp k s hs).2
  · intro k s hs
    rw [hhj k s hs]
    exact (htail.actual_ae k s hs).2.1
  · intro s hs
    have hd := de.zero_equation s hs
    have hu' : u 0 s = ⟨v 0 s, de.mem_domain 0 s hs⟩ := by apply Subtype.ext; exact hu 0 s hs
    rw [hu', ← hh0 s hs]
    exact hd
  · intro k s hs
    have hu' : u k s = ⟨v k s, de.mem_domain k s hs⟩ := by apply Subtype.ext; exact hu k s hs
    rw [hu', hhj k s hs]
    have hc : KPChamberL2Defect.spectralCorrection (Module.finrank ℚ F / 2)
        (fun j t => (u j t : KPContActualChamberDomainDefect.Sector F ζ hζ C R P H U)) k s =
        KPChamberL2Defect.spectralCorrection (Module.finrank ℚ F / 2) v k s := by
      unfold KPChamberL2Defect.spectralCorrection
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only
      rw [hu (k-j) s hs]
    rw [hc]
    exact de.equation k s hs
  · intro k s hs
    have heq : Set.EqOn (fun t => (u 0 t : KPContActualChamberDomainDefect.Sector F ζ hζ C R P H U)) (v 0)
        KPContActualChamberDomainDefect.V := fun t ht => hu 0 t ht
    rw [(iteratedDerivWithin_congr heq) hs, gh.value_derivatives k s hs, hu k s hs]
  · intro k
    apply (gh.product_holomorphic k).congr
    intro s hs
    exact (hz k s hs).symm
  · intro k s hs
    have heq : Set.EqOn (fun t => ((u 0 t : KPContActualChamberDomainDefect.Sector F ζ hζ C R P H U), Δ (u 0 t))) (z 0)
        KPContActualChamberDomainDefect.V := fun t ht => (hz 0 t ht).symm
    rw [(iteratedDerivWithin_congr heq) hs, gh.product_derivatives k s hs]
    exact hz k s hs
  · intro k K hK hKV
    obtain ⟨M, hM, hbound⟩ := de.uniform_bounds K hK hKV k
    refine ⟨M, hM, ?_⟩
    intro s hs
    have hu' : u k s = ⟨v k s, de.mem_domain k s (hKV hs)⟩ := by apply Subtype.ext; exact hu k s (hKV hs)
    rw [hu']
    exact hbound s hs

end DedekindZetaZeroFree

end
