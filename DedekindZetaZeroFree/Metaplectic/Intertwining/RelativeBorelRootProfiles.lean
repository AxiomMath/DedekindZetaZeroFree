module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.CubicRootResidualIntegrals

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)

theorem relative_borel_coordinate
 (u : (LocalField F q)ˣ) (b : BL F ζ hζ q S P)
 (hb : (b : ActualCover F ζ hζ q) =
  KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
  KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ))) :
 S.borel.coordinate (retractL F ζ hζ q S P b) = u⁻¹ ^ (2 : ℕ) := by
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  have he : (b : ActualCover F ζ hζ q) =
    (S.borel.torus (retractL F ζ hζ q S P b) : ActualCover F ζ hζ q) *
    (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
  have hp := congrArg S.borel.projection (he.symm.trans hb)
  have pn : S.borel.projection
      (KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q)) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pa : S.borel.projection (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ))) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (u⁻¹ ^ (2 : ℕ)) 1) :=
    (S.openCell P).projection_eq _
  rw [map_mul, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection,
    pn, pa, ← map_mul, ← map_mul] at hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h11 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 1 1) hc
  have h00 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 0 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.d, KubotaRankTwo.n,
    KPStandardLocalRootLifts.N, KPStandardLocalRootLifts.A,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply] at h11 h00
  apply Units.ext
  simpa [h11] using h00

theorem eventual_normalized_test_root_profile
    (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
      (f : scalarSections F ζ hζ q S P hP .minus),
      IsMinusTest F ζ hζ q S P hP
        (diagonalLift F ζ hζ q π ((i.val : ℤ), 0)) m f → ∀ t : LocalField F q,
      f.val (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) =
        (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℂ)) t := by
  obtain ⟨M, hM⟩ :=
    KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry
      F ζ hζ q S P hP htame π hπ .minus
  refine ⟨M, fun m hm i f hf t => ?_⟩
  obtain ⟨K, hK, hc, hn, hd, hr, ho, hz, hs, hchart⟩ := hM m hm
  by_cases ht : t ∈ rootLevelSet F ζ hζ q m
  · rw [Set.indicator_of_mem ht]
    have hf' := congrArg (fun v : scalarSections F ζ hζ q S P hP .minus =>
      v.val (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
        (hf.1 (KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) ht)
    change f.val (_ * KPPGLLocalCover.N F ζ hζ (Sum.inr q) t) = _ at hf'
    rw [← diagonalLift_index_zero_eq_eta, hf.2.2] at hf'
    simpa only [diagonalLift_index_zero_eq_eta] using hf'
  · rw [Set.indicator_of_notMem ht]
    by_contra h
    have hsup := hf.2.1 h
    have hsup' : eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) t ∈ bruhatSupport F ζ hζ q S P π i m := by
      simpa only [diagonalLift_index_zero_eq_eta, testSupport, bruhatSupport] using hsup
    exact ht ((hchart i i t).mp hsup').2

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end
