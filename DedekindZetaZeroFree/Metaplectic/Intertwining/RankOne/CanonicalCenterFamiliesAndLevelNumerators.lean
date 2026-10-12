module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CenterInducedDiagonalComparison
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.InducingDataConversions

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellContinuationProve

set_option maxHeartbeats 800000

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : Polarization S.heisenberg)
  (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
    S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ε : Sign)

theorem exists_uniformizer :
    ∃ π : (LocalField F q)ˣ,
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).symm
      (WithZero.exp (-1 : ℤ)))
  have hp' : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) p) = WithZero.exp (-1 : ℤ) := by
    rw [hp]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).apply_symm_apply _
  have hpne : p ≠ 0 := by
    intro h
    have h0 : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) := by
      simpa [h] using hp'
    exact WithZero.exp_ne_zero h0.symm
  exact ⟨Units.mk0 p hpne, hp'⟩

end DedekindZetaZeroFree.KPRankOneShellContinuationProve

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellContinuation
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellRepair KPRankOneCenterInducedDiagonalComparison

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in

theorem actual_exists_tauStandardFamily_normalized
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) :
    Nonempty (TauStandardFamily F ζ hζ q S.heisenberg S.borel P S.iwasawa μ) := by
  classical
  obtain ⟨π,hπ⟩ := KPRankOneShellContinuationProve.exists_uniformizer F q
  obtain ⟨C,hC⟩ := actual_exists_global_intertwining_continuation F ζ hζ q S P μ hμ π hπ
  let op := fun ε z => transportToSections (LocalField F q) S.borel P S.iwasawa ε z (C ε z)
  refine ⟨{ op := op
            intertwining := fun ε z hz => (hC ε z hz).2
            numerators := fun J hJ ε => actual_existsUnique_level_numerator F ζ hζ q S P J hJ μ hμ ε
            shell_eq := ?_
            integral_eq := ?_ }⟩
  · intro ε z hz f g h
    have hCG : C ε z = actualContinued F ζ hζ q S P μ hμ π hπ ε z := by
      apply LinearMap.ext
      intro φ
      obtain ⟨J,hJ,hφ⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ
      exact ((hC ε z (denominator_ne_zero_of_convergence (LocalField F q) ε z hz)).1
        J hJ _ (actualLevelNumerator_spec F ζ hζ q S P J hJ μ hμ π hπ ε) ⟨φ,hφ⟩).trans
        (actualContinued_eq_level F ζ hζ q S P μ hμ π hπ ε z J hJ ⟨φ,hφ⟩).symm
    refine ⟨?_,?_⟩
    · convert actual_section_integrable F ζ hζ q S P μ hμ π hπ ε z hz f g h using 1
      funext x
      rw [(S.openCell P).upper_eq]
    change ((transportToSections (LocalField F q) S.borel P S.iwasawa ε z (C ε z) f).val g).val h = _
    rw [hCG]
    simpa only [(S.openCell P).upper_eq] using
      actualContinued_section_eq_integral F ζ hζ q S P μ hμ π hπ ε z hz f g h
  · intro J ε p hp z hz φ
    change (compactTrivialization S.borel P S.iwasawa (targetSign ε) (targetParameter ε z))
      (C ε z ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε z)).symm
        (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε z) φ.val))) = _
    rw [LinearEquiv.symm_apply_apply]
    obtain ⟨J',hJ',hφ'⟩ := actual_common_level F ζ hζ q S P (sourceSign ε) φ.val
    let ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J' := ⟨φ.val,hφ'⟩
    obtain ⟨p',hp',_⟩ := actual_existsUnique_level_numerator F ζ hζ q S P J' hJ' μ hμ ε
    rw [(hC ε z hz).1 J' hJ' p' hp' ψ]
    congr 1
    exact tauContinuedLevel_compatible_any F ζ hζ q S.heisenberg S.borel P S.iwasawa
      J' J μ ε p' p hp' hp ψ φ rfl z

theorem actual_exists_tauStandardFamily
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure] :
    Nonempty (TauStandardFamily F ζ hζ q S.heisenberg S.borel P S.iwasawa μ) := by
  classical
  let c := μ ((valuation (LocalField F q)).integer : Set (LocalField F q))
  have hc0 : c ≠ 0 := by
    have hn : ((valuation (LocalField F q)).integer : Set (LocalField F q)) ∈ nhds (0 : LocalField F q) := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨(1 : (ValueGroupWithZero (LocalField F q))ˣ),?_⟩
      intro x hx
      exact le_of_lt (by simpa using hx)
    exact (Measure.measure_pos_of_mem_nhds μ hn).ne'
  have hctop : c ≠ ⊤ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1).measure_ne_top
  let ν : Measure (LocalField F q) := c⁻¹ • μ
  haveI : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul μ
    (ENNReal.inv_ne_zero.mpr hctop) (ENNReal.inv_ne_top.mpr hc0)
  have hν : ν ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1 :=
    ENNReal.inv_mul_cancel hc0 hctop
  obtain ⟨Jν⟩ := actual_exists_tauStandardFamily_normalized F ζ hζ q S P ν hν
  have hm : c • ν = μ := by
    dsimp only [ν]
    rw [smul_smul,ENNReal.mul_inv_cancel hc0 hctop,one_smul]
  rw [← hm]
  exact ⟨tauStandardFamily_smul_measure F ζ hζ q S.heisenberg S.borel P S.iwasawa ν Jν c hctop⟩

end DedekindZetaZeroFree.KPRankOneShellContinuation

end

end
