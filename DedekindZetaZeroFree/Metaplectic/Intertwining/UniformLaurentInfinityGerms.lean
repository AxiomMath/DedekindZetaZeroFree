module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.FullCenterReverseChart
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.OpenCellLaurentProfiles
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ForwardUniformLaurentNumerator

@[expose] public section

namespace DedekindZetaZeroFree.KPActualResidueSources
open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw KPActualScalarBinding
noncomputable section
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q)
local notation "H₀" => KPExceptionalRaw.actualTorus F ζ hζ q

variable (P : Polarization S.heisenberg) [DecidableEq S.D]

theorem actual_forward_uniform_infinity_data
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ (L : CompactOpenLevel (Cover F ζ hζ q))
      (χ : ℤ →₀ centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus L)
      (N : ℕ),
      (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup ∧
      (∀ r : ℂˣ, IsRegular F q r →
        forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
          rep hrep d φ hφ hcφ r =
        centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I .minus
          (-additiveParameter F q r)
          ((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f)).val) ∧
      (∀ v : (LocalField F q)ˣ, (N : ℤ) < valuationIndex F q v →
        signedWeyl F ζ hζ q * nLift F ζ hζ q (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
          openCoordinate F ζ hζ q 0 ∈ L.toOpenSubgroup) := by
  classical
  obtain ⟨L, hL, ψ, hψ⟩ := KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.compact_profile_uniform_laurent
    F ζ hζ q S.heisenberg S.borel P I (S.openCell P) rep hrep d φ hφ hcφ
  obtain ⟨χ, hχ⟩ := KPRankOneReverseLaurentShellExpansion.FiniteAnnulusSteps.forward_uniform_laurent_numerator
    F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ L hL ψ hψ
  have hn : Continuous (nLift F ζ hζ q) := by
    have he : nLift F ζ hζ q = fun x => (S.borel.upperRoot (Multiplicative.ofAdd x) : Cover F ζ hζ q) :=
      funext (fun x => ((S.openCell P).upper_eq x).symm)
    rw [he]
    exact continuous_subtype_val.comp (S.borel.upperRoot_continuous.comp continuous_ofAdd)
  have hn0 : nLift F ζ hζ q 0 = 1 := by
    rw [← (S.openCell P).upper_eq]
    change (S.borel.upperRoot 1 : Cover F ζ hζ q) = 1
    simp
  have ht : Continuous (fun x : LocalField F q =>
      signedWeyl F ζ hζ q * nLift F ζ hζ q (-x) * openCoordinate F ζ hζ q 0) :=
    (continuous_const.mul (hn.comp continuous_neg)).mul continuous_const
  have ht0 : signedWeyl F ζ hζ q * nLift F ζ hζ q (-(0 : LocalField F q)) *
      openCoordinate F ζ hζ q 0 = 1 := by
    simp [openCoordinate, hn0]
  have hU : {x : LocalField F q | signedWeyl F ζ hζ q * nLift F ζ hζ q (-x) *
      openCoordinate F ζ hζ q 0 ∈ L.toOpenSubgroup} ∈ nhds (0 : LocalField F q) :=
    ht.continuousAt.preimage_mem_nhds
      (L.toOpenSubgroup.isOpen.mem_nhds (by rw [ht0]; exact L.toOpenSubgroup.one_mem))
  obtain ⟨γ, hγ, hγU⟩ := (IsValuativeTopology.hasBasis_nhds_zero' (LocalField F q)).mem_iff.mp hU
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  let m : ℤ := WithZero.log (e γ)
  refine ⟨L, χ, m.natAbs, hL, hχ, ?_⟩
  intro v hv
  have hval : valuation (LocalField F q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) < γ := by
    apply e.toOrderIso.lt_iff_lt.mp
    have hv0 : e (valuation (LocalField F q) (v : LocalField F q)) ≠ 0 :=
      (map_ne_zero e).2 (by simpa using v.ne_zero)
    have hγ0 : e γ ≠ 0 := (map_ne_zero e).2 hγ
    apply (WithZero.log_lt_log (by
      change e (valuation (LocalField F q) ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) ≠ 0
      exact (map_ne_zero e).2 (by simpa using v⁻¹.ne_zero)) hγ0).mp
    change valuationIndex F q v⁻¹ < m
    have hi : valuationIndex F q v⁻¹ = -valuationIndex F q v := by
      simp [valuationIndex, Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv]
    rw [hi]
    omega
  exact hγU hval

end
end DedekindZetaZeroFree.KPActualResidueSources
