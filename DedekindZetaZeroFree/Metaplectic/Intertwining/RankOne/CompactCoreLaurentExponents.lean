module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailInducingActionAndCubeClasses

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

def initialExponent (g : ActualCover F ζ hζ q) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)) : LocalField F q)))

def initialCoefficient (P : Polarization S.heisenberg) (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) : ℂ :=
  deltaHalf S.borel (S.iwasawa.borelPart g) *
    (borelAction S.borel P (sourceSign ε) (S.iwasawa.borelPart g)
      (φ.val (S.iwasawa.compactPart g))).val h

theorem initialCoordinate_monomial (P : Polarization S.heisenberg) (ε : Sign)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) (s : ℂ) :
    ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ).val g).val h =
      initialCoefficient F ζ hζ q S P ε φ g h *
        (evaluationUnit (LocalField F q) ε s : ℂ) ^ initialExponent F ζ hζ q S g := by
  let y := S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))
  let n : ℤ := WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (y : LocalField F q)))
  have hp : normPower (LocalField F q) y (sourceParameter ε s) =
      (evaluationUnit (LocalField F q) ε s : ℂ) ^ (-n) := by
    have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
      exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (valuation (LocalField F q)).integer))
    have he : (evaluationUnit (LocalField F q) ε s : ℂ) = r (LocalField F q) (sourceParameter ε s) := by
      cases ε <;> simp [evaluationUnit, sourceParameter, rUnit, r, Complex.exp_neg]
    rw [he]
    change Complex.exp (sourceParameter ε s * (Real.log ((residueCardinality (LocalField F q) : ℝ) ^ (n : ℝ)) : ℂ)) = _
    rw [Real.log_rpow hq]
    unfold r
    rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  change (deltaHalf S.borel (S.iwasawa.borelPart g) * normPower (LocalField F q) y (sourceParameter ε s)) *
      (borelAction S.borel P (sourceSign ε) (S.iwasawa.borelPart g) (φ.val (S.iwasawa.compactPart g))).val h = _
  rw [hp]
  dsimp [initialCoefficient, initialExponent, y, n]
  ring

theorem initialExponent_locallyConstant : IsLocallyConstant (initialExponent F ζ hζ q S) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun y : ActualCover F ζ hζ q => g⁻¹ * y) :=
    continuous_const.mul continuous_id
  have hmem : ∀ᶠ y : ActualCover F ζ hζ q in nhds g,
      g⁻¹ * y ∈ S.iwasawa.compact.toOpenSubgroup :=
    hc.continuousAt.preimage_mem_nhds (by
      simpa using S.iwasawa.compact.toOpenSubgroup.isOpen.mem_nhds
        S.iwasawa.compact.toOpenSubgroup.one_mem)
  filter_upwards [hmem] with y hy
  let b : S.borel.B := (S.iwasawa.borelPart g)⁻¹ * S.iwasawa.borelPart y
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    have he : (b : ActualCover F ζ hζ q) =
        (S.iwasawa.compactPart g : ActualCover F ζ hζ q) * (g⁻¹ * y) *
          (S.iwasawa.compactPart y : ActualCover F ζ hζ q)⁻¹ := by
      calc
        (b : ActualCover F ζ hζ q) =
            (S.iwasawa.compactPart g : ActualCover F ζ hζ q) *
              (((S.iwasawa.borelPart g : ActualCover F ζ hζ q) *
                (S.iwasawa.compactPart g : ActualCover F ζ hζ q))⁻¹ *
                ((S.iwasawa.borelPart y : ActualCover F ζ hζ q) *
                  (S.iwasawa.compactPart y : ActualCover F ζ hζ q))) *
              (S.iwasawa.compactPart y : ActualCover F ζ hζ q)⁻¹ := by
          simp [b, mul_assoc]
        _ = _ := by rw [← S.iwasawa.decomposition g, ← S.iwasawa.decomposition y]
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compactPart g).property hy)
      (S.iwasawa.compact.toOpenSubgroup.inv_mem (S.iwasawa.compactPart y).property)
  have hn := S.iwasawa.intersection_norm b hb
  have he : S.iwasawa.borelPart y = S.iwasawa.borelPart g * b := by
    simp [b]
  have ha : localAbs (LocalField F q)
      (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart y))) =
      localAbs (LocalField F q)
        (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g))) := by
    rw [he, map_mul, map_mul, localAbs_mul, hn, mul_one]
  have hq : (1 : ℝ) < residueCardinality (LocalField F q) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField (valuation (LocalField F q)).integer))
  unfold localAbs at ha
  have hn := (Real.rpow_right_inj (by linarith : (0 : ℝ) < residueCardinality (LocalField F q))
    (ne_of_gt hq)).mp ha
  unfold initialExponent
  congr 1
  exact_mod_cast hn

theorem initialExponent_finite_on_compact (C : Set (ActualCover F ζ hζ q)) (hC : IsCompact C) :
    (initialExponent F ζ hζ q S '' C).Finite := by
  exact (hC.image (initialExponent_locallyConstant F ζ hζ q S).continuous).finite_of_discrete

end DedekindZetaZeroFree.KPRankOneShellRepair

end
