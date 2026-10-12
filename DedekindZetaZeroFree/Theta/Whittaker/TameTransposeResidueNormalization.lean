module

public import DedekindZetaZeroFree.Metaplectic.Kubota.UniformizerHilbertPowers

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

abbrev Residue := IsLocalRing.ResidueField (KPTameCompact.O F q)

def HasPiFirstOrientation (π : (LocalField F q)ˣ)
    (κ : MulChar (Residue F q) ℂ) : Prop :=
  ∀ u : (KPTameCompact.O F q)ˣ,
    κ (IsLocalRing.residue (KPTameCompact.O F q) (u : KPTameCompact.O F q)) =
      (ordinaryIota F ζ hζ
        (KPHilbert.B3 F ζ hζ (Sum.inr q) π
          (KPTameCompact.unitInclusion F q u)) : ℂ)

def HasConductorOneResidue (π : (LocalField F q)ˣ)
    (ψ : Multiplicative (LocalField F q) →* ℂˣ)
    (ψbar : AddChar (Residue F q) ℂ) : Prop :=
  ψbar ≠ 1 ∧ ∀ u : KPTameCompact.O F q,
    ψbar (IsLocalRing.residue (KPTameCompact.O F q) u) =
      (ψ (Multiplicative.ofAdd ((u : LocalField F q) / (π : LocalField F q))) : ℂ)

section ScalarArrays
variable {k : Type*} [Field k] [Fintype k]

def g (κ : MulChar k ℂ) (ψbar : AddChar k ℂ) (j : ZMod 3) : ℂ :=
  KPTameGauss.cubicGaussSum κ ψbar j

end ScalarArrays

variable (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

theorem B_powers (π : (LocalField F q)ˣ) (a b : ℤ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) (π ^ a) (π ^ b) = 1 := by
  exact KPTameLiteralNormalizationAtomic.DiagonalArithmetic.uniformizer_hilbert_powers
    F ζ hζ q π a b

include S in
theorem diagonal_scalar (π : (LocalField F q)ˣ) (a b : ℤ) :
    diagonalLift F ζ hζ q π (a,b) =
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ (a-b)) := by
  exact KPTameLiteralNormalizationAtomic.DiagonalArithmetic.diagonal_lift_scalar
    F ζ hζ q S π a b

def IsNormalizedTameExtension : Prop :=
  ∀ (h : HL F ζ hζ q S P) (e : rootsOfUnity 3 F)
    (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
    (h.val : ActualCover F ζ hζ q) =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) (y ^ 3) →
    (P.ωL h : ℂ) = (ordinaryIota F ζ hζ e : ℂ) *
      normPower (LocalField F q) (y ^ 3) (1 / 6)

private theorem abs_zpow (π : (LocalField F q)ˣ) (n : ℤ) :
    localAbs (LocalField F q) (π ^ n) = localAbs (LocalField F q) π ^ n := by
  let R : (LocalField F q)ˣ →* ℝ :=
    { toFun := localAbs (LocalField F q)
      map_one' := localAbs_one _
      map_mul' := localAbs_mul _ }
  exact map_zpow R π n

include S P hP in
private theorem cube_chi (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (n : ℤ) :
    ∃ h : HL F ζ hζ q S P,
      (h.val : actualTorus F ζ hζ q) = S.borel.cubeLift (π ^ (-n)) ∧
      chiH F ζ hζ q S P hP .minus h =
        (residueCardinality (LocalField F q) : ℂ) ^ n := by
  have hc : (S.borel.cubeLift (π ^ (-n)) : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P := by
    rw [HL, Subgroup.mem_comap]
    have he : S.heisenberg.π (S.borel.cubeLift (π ^ (-n))) = 1 := by
      exact (show (S.borel.cubeLift (π ^ (-n)) : actualTorus F ζ hζ q) ∈ S.heisenberg.π.ker by
        rw [S.heisenberg.quotient_kernel]; exact (S.borel.cubeLift _).property)
    rw [he]; exact P.L.one_mem
  let h : HL F ζ hζ q S P := ⟨S.borel.cubeLift (π ^ (-n)), hc⟩
  refine ⟨h, rfl, ?_⟩
  have hw : (weylHL F ζ hζ q S P hP h : actualTorus F ζ hζ q) =
      S.borel.cubeLift ((π ^ (-n))⁻¹) := by
    change S.borel.weyl (S.borel.cubeLift (π ^ (-n))) = _
    rw [← S.borel.weylCenter_coe]
    exact congrArg Subtype.val (S.borel.weyl_cube (π ^ (-n)))
  have hh := P.extends_center (weylHL F ζ hζ q S P hP h)
    (hw ▸ (S.borel.cubeLift ((π ^ (-n))⁻¹)).property)
  rw [chiH, hh]
  have he : (⟨(weylHL F ζ hζ q S P hP h : actualTorus F ζ hζ q),
    hw ▸ (S.borel.cubeLift ((π ^ (-n))⁻¹)).property⟩ : S.heisenberg.C) =
      S.borel.cubeLift ((π ^ (-n))⁻¹) := Subtype.ext hw
  rw [he, S.borel.exceptional_cube]
  change normPower (LocalField F q) (((π ^ (-n))⁻¹) ^ 3) (1/6) *
    normPower (LocalField F q) (S.borel.coordinate (S.borel.cubeLift (π ^ (-n)))) (1/2) = _
  rw [S.borel.cube_coordinate]
  have hp : localAbs (LocalField F q) π = (residueCardinality (LocalField F q) : ℝ)⁻¹ := by
    simp [localAbs, hπ, Real.rpow_neg_one]
  have hQ : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Nat.card_pos
  simp only [normPower, ← zpow_neg, neg_neg, ← zpow_natCast, ← zpow_mul, abs_zpow,
    hp, inv_zpow, Real.log_inv, Real.log_zpow, ← Complex.exp_add]
  push_cast
  conv_lhs => arg 1; ring_nf
  rw [Complex.exp_int_mul, Complex.exp_log]
  exact_mod_cast (ne_of_gt hQ)

theorem actual_minus_transports
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    ∀ i : Fin 3, ∃ h : HL F ζ hζ q S P,
      diagonalLift F ζ hζ q π (-1, (i.val : ℤ) + 1) =
        (S.borel.torus h : ActualCover F ζ hζ q) *
          eta F ζ hζ q π ⟨(1 - (i.val : ZMod 3)).val, ZMod.val_lt _⟩ ∧
      chiH F ζ hζ q S P hP .minus h =
        (residueCardinality (LocalField F q) : ℂ) ^ transportExponent i := by
  intro i
  obtain ⟨h, hh, hchi⟩ := cube_chi F ζ hζ q S P hP π hπ (transportExponent i)
  refine ⟨h, ?_, hchi⟩
  rw [S.torus_full, hh, S.cube_actual, eta, diagonal_scalar F ζ hζ q S]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast,
    KPPGLLocalCover.A_mul, B_powers, one_pow, map_one, one_mul, ← zpow_add]
  congr 1
  congr 1
  fin_cases i <;> norm_num [transportExponent, ZMod.val_one]

end DedekindZetaZeroFree.KPTameTransposeLiteralCoefficients

end
