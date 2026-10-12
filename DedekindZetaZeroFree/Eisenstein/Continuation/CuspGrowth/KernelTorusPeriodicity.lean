module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.CompactCrossExponentialBound

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)

private theorem scalar_cusp_frame
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (atlasLevel F ζ hζ C R P H U))
    (z : KPArch.Space (KPCuspLogShape.dimension F)) (ε : rootsOfUnity 3 F) :
    (KPContSectorScalarLineAlgebra.J F ζ hζ (atlasLevel F ζ hζ C R P H U) e).val
      (z, finiteRepresentative F ζ hζ C R P H U a ε) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContSectorScalarLineAlgebra.S F ζ hζ (atlasLevel F ζ hζ C R P H U)
        R P H e a.1).val ((sigma F ζ hζ C R P H U a) • z) := by
  let j := KPContSectorScalarLineAlgebra.J F ζ hζ (atlasLevel F ζ hζ C R P H U) e
  have hr := j.property.1 z (finiteRepresentative F ζ hζ C R P H U a ε)
    (sigma F ζ hζ C R P H U a)
  have hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (sigma F ζ hζ C R P H U a) * finiteRepresentative F ζ hζ C R P H U a ε =
      KPCuspGenuineMonodromy.central F ζ hζ ε * (atlas F ζ hζ C R P H U).representative a.1 := by
    have hcomm : ∀ c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ,
        c * KPCuspGenuineMonodromy.central F ζ hζ ε =
          KPCuspGenuineMonodromy.central F ζ hζ ε * c := by
      intro c
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
          (show (KPCuspGenuineMonodromy.central F ζ hζ ε :
            KPCuspGenuineMonodromy.Cover F ζ hζ) ∈
            (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩)) c
    rw [finiteRepresentative, ← mul_assoc, ← mul_assoc, hcomm]
    simp only [map_inv, mul_assoc, mul_inv_cancel_left]
  rw [hc, j.property.2.1] at hr
  rw [KPContSectorScalarLineAlgebra.S_apply]
  exact hr.symm

include hι hf hs in
private theorem sheet_frame
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (atlasLevel F ζ hζ C R P H U))
    (he : ∀ g, e.val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (atlasLevel F ζ hζ C R P H U) (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      KPContActualChamberNormalSeries.E F ζ hζ U ι f s g)
    (t : ℝ) (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (KPContSectorScalarLineAlgebra.S F ζ hζ (atlasLevel F ζ hζ C R P H U)
        R P H e a.1).val ((sigma F ζ hζ C R P H U a) • KPCuspCharts.toArch F (p,t)) := by
  simp only [KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
    iteratedDerivWithin_zero, cuspGroup]
  rw [(KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1, ← he]
  rw [localGroup, KPContSectorScalarLineAlgebra.group_lift_formula,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  exact scalar_cusp_frame F ζ hζ C R P H U a e _ ε

include hι hf hs

theorem actualCuspSheet_crossAction
    (h : stabilizer F ζ hζ C R P H U a) (t : ℝ)
    (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      ((geometry F ζ hζ C R P H U a).crossAction h p).1
      ((geometry F ζ hζ C R P H U a).crossAction h p).2 ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a h) : ℂ) *
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε := by
  obtain ⟨e, he, _, _⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  rw [sheet_frame F ζ hζ C R P H U ι hι f hf a s hs (e s) (he s hs),
    sheet_frame F ζ hζ C R P H U ι hι f hf a s hs (e s) (he s hs)]
  obtain ⟨A, hA, hc⟩ := (parabolic F ζ hζ C R P H U a).upper h h.property
  have hact : (h : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (p,t) =
      KPCuspCharts.toArch F ((geometry F ζ hζ C R P H U a).crossAction h p,t) := by
    change KPCuspSiegel.action F _ _ = _
    rw [(geometry F ζ hζ C R P H U a).actual_action h A hA hc,
      (geometry F ζ hζ C R P H U a).crossAction_formula h A hA hc]
    rfl
  rw [← hact]
  let γ := KPCuspGenuineMonodromy.cuspInclusion F (component F ζ hζ C R P H U a)
    (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2) (sigma F ζ hζ C R P H U a) h
  have heq : (sigma F ζ hζ C R P H U a) • ((h : KPCuspArithmetic.PGL2 F) •
      KPCuspCharts.toArch F (p,t)) = (γ : KPCuspArithmetic.PGL2 F) •
      ((sigma F ζ hζ C R P H U a) • KPCuspCharts.toArch F (p,t)) := by
    simp only [γ, KPCuspGenuineMonodromy.cuspInclusion_formula, mul_smul, inv_smul_smul]
  rw [heq, KPContSectorScalarLineAlgebra.S_equivariance]
  change _ = (KPCuspGenuineMonodromy.chi F ζ hζ
    (((atlas F ζ hζ C R P H U).line a.1).rho γ) : ℂ) * _
  change (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
    ((KPCuspGenuineMonodromy.chi F ζ hζ (((atlas F ζ hζ C R P H U).line a.1).rho γ) : ℂ) * _) = _
  ring

theorem actualCuspSheet_norm_crossAction
    (h : stabilizer F ζ hζ C R P H U a) (t : ℝ)
    (p : KPCuspCharts.Cross F) (ε : rootsOfUnity 3 F) :
    ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      ((geometry F ζ hζ C R P H U a).crossAction h p).1
      ((geometry F ζ hζ C R P H U a).crossAction h p).2 ε‖ =
    ‖KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t p.1 p.2 ε‖ := by
  rw [actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs,
    norm_mul, KPContSectorCoveredQuotientVocabulary.chi_norm, one_mul]

theorem actualCuspSheet_translation
    (l : (parabolic F ζ hζ C R P H U a).L) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
      (x + KPCuspCharts.embedding F l.val) b ε =
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
      ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ) *
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε := by
  let D := parabolic F ζ hζ C R P H U a
  let G := geometry F ζ hζ C R P H U a
  let h := D.inclusion (Multiplicative.ofAdd l)
  obtain ⟨A, hA, hc⟩ := D.upper h.val h.property
  have ha := G.actual_action h A hA hc ((x,b),0)
  rw [G.unipotent_action l ((x,b),0)] at ha
  have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective ha
  have he : G.crossAction h (x,b) = (x + KPCuspCharts.embedding F l.val,b) := by
    rw [G.crossAction_formula h A hA hc]
    exact (congrArg Prod.fst hp).symm
  have hh := actualCuspSheet_crossAction F ζ hζ C R P H U ι hι f hf a s hs h t (x,b) ε
  change G.crossAction h (x,b) = _ at he
  change KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
    (G.crossAction h (x,b)).1 (G.crossAction h (x,b)).2 ε = _ at hh
  rw [he] at hh
  exact hh

theorem actualCuspSheet_kernel_representative
    (t : ℝ) (x y : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F)
    (hxy : (QuotientAddGroup.mk x : KernelTorus F ζ hζ C R P H U a) = QuotientAddGroup.mk y) :
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε =
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t y b ε := by
  have hx : -x + y ∈ KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
        (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)) := by
    simpa [sub_eq_add_neg, add_comm] using (QuotientAddGroup.eq_iff_sub_mem).mp hxy.symm
  obtain ⟨l, hl, he⟩ := hx
  have hy : y = x + KPCuspCharts.embedding F l := by rw [he]; abel
  rw [hy, actualCuspSheet_translation F ζ hζ C R P H U ι hι f hf a s hs
    ⟨l, hl.1⟩, hl.2 hl.1, map_one, Units.val_one, one_mul]

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
