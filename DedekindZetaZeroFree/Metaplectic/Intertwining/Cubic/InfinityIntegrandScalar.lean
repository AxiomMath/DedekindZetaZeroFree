module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.UniformLaurentInfinityGerms

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

omit [DecidableEq S.D] in
private theorem compact_right_invariant
    (I : IwasawaData S.borel) (L : CompactOpenLevel (Cover F ζ hζ q))
    (hL : (L.toOpenSubgroup : Subgroup (Cover F ζ hζ q)) ≤ I.compact.toOpenSubgroup)
    (ε : Sign) (z : ℂ) (ψ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I ε L)
    (g j : Cover F ζ hζ q) (hj : j ∈ L.toOpenSubgroup) :
    (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I ε z ψ.val).val (g * j) =
      (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I ε z ψ.val).val g := by
  let f := centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I ε z ψ.val
  let k := I.compactPart g
  let k' : I.compact.toOpenSubgroup := ⟨(k : Cover F ζ hζ q) * j,
    I.compact.toOpenSubgroup.mul_mem k.property (hL hj)⟩
  have hk : f.val (k : Cover F ζ hζ q) = ψ.val.val k := by
    change centerInducingAction F ζ hζ q S.heisenberg S.borel ε z (I.borelPart (k : Cover F ζ hζ q))
      (ψ.val.val (I.compactPart (k : Cover F ζ hζ q))) = _
    rw [I.borelPart_compact, I.compactPart_compact, map_one]
    rfl
  have hk' : f.val (k' : Cover F ζ hζ q) = ψ.val.val k' := by
    change centerInducingAction F ζ hζ q S.heisenberg S.borel ε z (I.borelPart (k' : Cover F ζ hζ q))
      (ψ.val.val (I.compactPart (k' : Cover F ζ hζ q))) = _
    rw [I.borelPart_compact, I.compactPart_compact, map_one]
    rfl
  have he : ψ.val.val k' = ψ.val.val k := ψ.property ⟨j, hj⟩ k k' rfl
  change f.val (g * j) = f.val g
  conv_lhs => rw [I.decomposition g, mul_assoc]
  change f.val ((I.borelPart g : Cover F ζ hζ q) * (k' : Cover F ζ hζ q)) = _
  rw [f.property.1, hk', he, ← hk, ← f.property.1, ← I.decomposition g]

private theorem infinity_integrand_formula
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ)
    (hgerm : (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val
        (signedWeyl F ζ hζ q * nLift F ζ hζ q (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
          openCoordinate F ζ hζ q 0) =
      (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val 1) :
    reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r lam h v =
      ((forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r).val 1).val h *
        (localAbs (LocalField F q) v : ℂ)⁻¹ * normPower (LocalField F q) v lam := by
  have hb := congrArg (fun V : CenterModule S.heisenberg => V.val h)
    (actual_reverse_chart F ζ hζ q S P r
      (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P) rep hrep d φ hφ hcφ r) v)
  rw [hgerm] at hb
  change _ = (localAbs (LocalField F q) v : ℂ) *
    ((KPExceptionalRaw.ordinaryIota F ζ hζ (kappa F ζ hζ q v 0) : ℂ) * _) at hb
  have hp : (localAbs (LocalField F q) v : ℂ) ≠ 0 := by
    exact_mod_cast (localAbs_pos _ _).ne'
  unfold reverseIntegrand
  rw [S.openCell_ordinary P, hb]
  field_simp

private theorem forward_germ
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N : ℕ, ∀ r : ℂˣ, IsRegular F q r → ∀ v : (LocalField F q)ˣ,
      (N : ℤ) < valuationIndex F q v →
      (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r).val
        (signedWeyl F ζ hζ q * nLift F ζ hζ q (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) *
          openCoordinate F ζ hζ q 0) =
      (forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r).val 1 := by
  obtain ⟨L, χ, N, hL, hχ, hN⟩ := actual_forward_uniform_infinity_data F ζ hζ q S P
    I μ J rep hrep d φ hφ hcφ
  refine ⟨N, ?_⟩
  intro r hr v hv
  rw [hχ r hr]
  have hh := compact_right_invariant F ζ hζ q S I L hL .minus
    (-additiveParameter F q r)
    ((1 - t F q (r : ℂ))⁻¹ • χ.sum (fun n f => (r : ℂ) ^ n • f))
    1 _ (hN v hv)
  simpa only [one_mul] using hh

theorem actual_infinity_eventual_scalar
    (I : IwasawaData S.borel) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q S.heisenberg S.borel I μ)
    (rep : S.D → H₀) (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : S.D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) :
    ∃ N : ℕ, ∀ r : ℂˣ, IsRegular F q r → ∀ (lam : ℂ) (h : H₀)
      (v : (LocalField F q)ˣ), (N : ℤ) < valuationIndex F q v →
      reverseIntegrand F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r lam h v =
      ((forwardSection F ζ hζ q S.heisenberg S.borel P I μ J (S.openCell P)
        rep hrep d φ hφ hcφ r).val 1).val h *
        (localAbs (LocalField F q) v : ℂ)⁻¹ * normPower (LocalField F q) v lam := by
  obtain ⟨N, hN⟩ := forward_germ F ζ hζ q S P I μ J
    rep hrep d φ hφ hcφ
  refine ⟨N, ?_⟩
  intro r hr lam h v hv
  exact infinity_integrand_formula F ζ hζ q S P I μ J rep hrep d φ hφ hcφ
    r lam h v (hN r hr v hv)

end
end DedekindZetaZeroFree.KPActualResidueSources
