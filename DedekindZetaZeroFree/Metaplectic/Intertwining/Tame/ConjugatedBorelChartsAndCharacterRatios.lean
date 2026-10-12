module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicBorel.LowShellUnitCharts
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.TransposeKernelTestCoefficients

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameLowShellConcreteCharts
open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeKernelUnfoldingRaw KPTameValuationCoordinates
open ActualFiniteBorel.LowShellUnitCharts
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

def diagonalTorus (π : (LocalField F q)ˣ) (f' : DiagonalValuations) :
    actualTorus F ζ hζ q :=
  ⟨diagonalLift F ζ hζ q π f', by
    refine ⟨KubotaRankTwo.d (LocalField F q) (π ^ f'.1) (π ^ f'.2), rfl, ?_, ?_⟩
    all_goals simp [KubotaRankTwo.d]⟩

theorem diagonalTorus_coordinate (π : (LocalField F q)ˣ) (f' : DiagonalValuations) :
    ActualFiniteTorus.coordinate F ζ hζ q (diagonalTorus F ζ hζ q π f') =
      π ^ (f'.1 - f'.2) := by
  rw [diagonal_coordinate F ζ hζ q (π ^ f'.1) (π ^ f'.2)
    (diagonalTorus F ζ hζ q π f') rfl, zpow_sub, div_eq_mul_inv]

def conjugateUnitHL (a : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ) :
    HL F ζ hζ q S P :=
  ⟨⟨ActualFiniteTorus.normalWord F ζ hζ q
      (KPHilbert.B3 F ζ hζ (Sum.inr q) (ActualFiniteTorus.coordinate F ζ hζ q a)
        (KPTameCompact.unitInclusion F q u)) (KPTameCompact.unitInclusion F q u),
      (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 _ _⟩,
    unit_word_mem_HL F ζ hζ q S P hP _ u⟩

def conjugateUnitBorel (a : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ) :
    BL F ζ hζ q S P :=
  ⟨S.borel.torus (conjugateUnitHL F ζ hζ q S P hP a u).val,
    ⟨S.borel.torus (conjugateUnitHL F ζ hζ q S P hP a u).val,
      by
        change S.borel.retract (S.borel.torus _) ∈ HL F ζ hζ q S P
        rw [S.borel.retract_torus]
        exact (conjugateUnitHL F ζ hζ q S P hP a u).property,
      rfl⟩⟩

theorem conjugateUnitBorel_word (a : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ) :
    (conjugateUnitBorel F ζ hζ q S P hP a u : ActualCover F ζ hζ q) =
      (a : ActualCover F ζ hζ q) * KPPGLLocalCover.A F ζ hζ (Sum.inr q)
        (KPTameCompact.unitInclusion F q u) * (a : ActualCover F ζ hζ q)⁻¹ := by
  rw [torus_conjugate F ζ hζ q]
  exact S.torus_full _

theorem conjugateUnitBorel_retract (a : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ) :
    ((retractL F ζ hζ q S P (conjugateUnitBorel F ζ hζ q S P hP a u)).val :
      ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)
        (KPHilbert.B3 F ζ hζ (Sum.inr q) (ActualFiniteTorus.coordinate F ζ hζ q a)
          (KPTameCompact.unitInclusion F q u)) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) := by
  have hb : inBorel F ζ hζ q S P (conjugateUnitBorel F ζ hζ q S P hP a u) =
      S.borel.torus (conjugateUnitHL F ζ hζ q S P hP a u).val := Subtype.ext rfl
  simp only [retractL, hb, S.borel.retract_torus]
  rfl

theorem inner_chart (a : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ) :
    (a : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)⁻¹ =
    (conjugateUnitBorel F ζ hζ q S P hP a u : ActualCover F ζ hζ q) *
      ((a : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) := by
  rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_diagonal, inv_inv,
    conjugateUnitBorel_word]
  group

theorem concrete_outer_chart (e : actualTorus F ζ hζ q) (u : (KPTameCompact.O F q)ˣ)
    (x : LocalField F q) :
    ((e : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) (x / (KPTameCompact.unitInclusion F q u : LocalField F q))) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u)⁻¹ =
      (conjugateUnitBorel F ζ hζ q S P hP e u : ActualCover F ζ hζ q) *
        ((e : ActualCover F ζ hζ q) * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) := by
  rw [conjugateUnitBorel_word]
  exact outer_chart F ζ hζ q e _ x

theorem concrete_chi_ratio
    (hnorm : ∀ (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
      (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
      (h.val : ActualCover F ζ hζ q) =
        KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) →
      (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) * normPower (LocalField F q) (y ^ 3) (1 / 6))
    (π : (LocalField F q)ˣ) (f' : DiagonalValuations) (i : Fin 3)
    (u : (KPTameCompact.O F q)ˣ) :
    chi F ζ hζ q S P hP .minus
        (conjugateUnitBorel F ζ hζ q S P hP (diagonalTorus F ζ hζ q π f') u) /
      chi F ζ hζ q S P hP .plus
        (conjugateUnitBorel F ζ hζ q S P hP
          (ActualFiniteTorus.torusLift F ζ hζ q (π ^ i.val)) u) =
      (ordinaryIota F ζ hζ
        (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u)) : ℂ) ^
          (f'.1 - f'.2 - (i.val : ℤ)) := by
  rw [literal_chi_ratio F ζ hζ q S P hP hnorm _ _ _ _ u
    (conjugateUnitBorel_retract F ζ hζ q S P hP _ u)
    (conjugateUnitBorel_retract F ζ hζ q S P hP _ u), diagonalTorus_coordinate]
  have he : ActualFiniteTorus.coordinate F ζ hζ q
      (ActualFiniteTorus.torusLift F ζ hζ q (π ^ i.val)) = π ^ i.val :=
    ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 _ _
      (by simp [ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord])).1
  rw [he]
  let B : (LocalField F q)ˣ →* rootsOfUnity 3 F :=
    { toFun := fun v => KPHilbert.B3 F ζ hζ (Sum.inr q) v (KPTameCompact.unitInclusion F q u)
      map_one' := KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 _
      map_mul' := fun x y => (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).1 x y _ }
  change (ordinaryIota F ζ hζ (B (π ^ (f'.1 - f'.2)) / B (π ^ i.val)) : ℂ) = _
  rw [map_zpow, map_pow, ← zpow_natCast, div_eq_mul_inv, ← zpow_sub, map_zpow,
    Units.val_zpow_eq_zpow_val]
  rfl

end DedekindZetaZeroFree.KPTameLowShellConcreteCharts

end
