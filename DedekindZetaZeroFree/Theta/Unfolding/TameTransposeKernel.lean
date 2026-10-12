module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.ConductorOneSupportLabels
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.HigherShellTranslationCancellation

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfolding

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality
open KPTameValuationCoordinates

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

 theorem weyl_involutive (t : actualTorus F ζ hζ q) :
    S.borel.weyl (S.borel.weyl t) = t := by
  have hs : S.borel.liftedW ^ 2 = 1 := by
    rw [(S.openCell S.polarization).weyl_eq]
    simpa only [KPRankOneOpenCellKernel.signedWeyl,
      KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW] using
      KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  have hi : S.borel.liftedW⁻¹ = S.borel.liftedW := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)
  apply S.borel.torus_injective
  apply Subtype.ext
  rw [S.borel.weyl_from_lift, S.borel.weyl_from_lift, hi]
  simp only [← mul_assoc]
  have hm : S.borel.liftedW * S.borel.liftedW = 1 := by simpa [pow_two] using hs
  rw [hm, one_mul, mul_assoc, hm, mul_one]
 theorem weyl_symm_eq (t : actualTorus F ζ hζ q) :
    S.borel.weyl.symm t = S.borel.weyl t := by
  apply S.borel.weyl.injective
  rw [S.borel.weyl.apply_symm_apply, weyl_involutive F ζ hζ q S]

def scalarCoordinateEquiv (ε : Sign) :
    sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε where
  toFun f := ⟨fun g => (f.val g).val 1, by
    constructor
    · intro b g
      have hf := congrArg (fun v : InducedModule P => v.val 1)
        (f.property.1 (inBorel F ζ hζ q S P b) g)
      cases ε
      · have hv := (f.val g).property (retractL F ζ hζ q S P b) 1
        simp [inducingAction, inducingScalar, deltaHalf, borelAction, tau,
          inducedRepresentation, Representation.subrepresentation_apply,
          rightTranslationRepresentation, normPower, rightTranslate] at hf
        change (f.val ((inBorel F ζ hζ q S P b : ActualCover F ζ hζ q) * g)).val 1 = _
        rw [hf]
        change Complex.exp (2⁻¹ * ↑(Real.log (localAbs (LocalField F q)
          (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b)))))) *
          (f.val g).val (retractL F ζ hζ q S P b : actualTorus F ζ hζ q) = _
        simp only [mul_one] at hv
        rw [hv]
        simp [chi, chiH, normPower, retractL]
        ring
      · have hv := (f.val g).property (weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b)) 1
        simp [inducingAction, inducingScalar, deltaHalf, borelAction, weylConjugate, tau,
          inducedRepresentation, Representation.subrepresentation_apply,
          rightTranslationRepresentation, normPower, rightTranslate] at hf
        change (f.val ((inBorel F ζ hζ q S P b : ActualCover F ζ hζ q) * g)).val 1 = _
        rw [hf]
        change Complex.exp (2⁻¹ * ↑(Real.log (localAbs (LocalField F q)
          (S.borel.coordinate (S.borel.retract (inBorel F ζ hζ q S P b)))))) *
          (f.val g).val (weylHL F ζ hζ q S P hP (retractL F ζ hζ q S P b) : actualTorus F ζ hζ q) = _
        simp only [mul_one] at hv
        rw [hv]
        simp [chi, chiH, normPower, retractL]
        ring
    · obtain ⟨J, hJ⟩ := f.property.2
      refine ⟨J, ?_⟩
      intro j hj
      funext g
      exact congrArg (fun v : InducedModule P => v.val 1) (congrFun (hJ j hj) g)⟩
  invFun f := ⟨fun g => ⟨fun t =>
    let t' := match ε with
      | .plus => t
      | .minus => S.borel.weyl.symm t
    (normPower (LocalField F q) (S.borel.coordinate t') (1 / 2))⁻¹ *
      f.val ((S.borel.torus t' : ActualCover F ζ hζ q) * g), by
      intro a t
      cases ε
      · let b : BL F ζ hζ q S P := ⟨S.borel.torus a, ⟨S.borel.torus a,
          by change S.borel.retract (S.borel.torus a) ∈ HL F ζ hζ q S P
             rw [S.borel.retract_torus]
             exact a.property, rfl⟩⟩
        have hf := f.property.1 b ((S.borel.torus t : ActualCover F ζ hζ q) * g)
        have hnorm : ∀ x y : (LocalField F q)ˣ,
            normPower (LocalField F q) (x * y) (1 / 2) =
              normPower (LocalField F q) x (1 / 2) * normPower (LocalField F q) y (1 / 2) := by
          intro x y
          simp [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ _))
            (ne_of_gt (localAbs_pos _ _)), mul_add, Complex.exp_add]
        change (normPower (LocalField F q) (S.borel.coordinate (a * t)) (1 / 2))⁻¹ *
          f.val ((S.borel.torus (a * t) : ActualCover F ζ hζ q) * g) = _
        have hr : retractL F ζ hζ q S P b = a := by
          apply Subtype.ext
          change S.borel.retract (S.borel.torus a) = a
          exact S.borel.retract_torus a
        change f.val ((S.borel.torus a : ActualCover F ζ hζ q) *
          ((S.borel.torus t : ActualCover F ζ hζ q) * g)) = _ at hf
        simp only [map_mul, Subgroup.coe_mul, mul_assoc, hf, chi, chiH, hr, hnorm]
        simp only [mul_inv_rev]
        have hn : normPower (LocalField F q) (S.borel.coordinate a) (1 / 2) ≠ 0 :=
          Complex.exp_ne_zero _
        change _ = (P.ωL a : ℂ) * _
        field_simp
        <;> ring
      · let a' : HL F ζ hζ q S P := weylHL F ζ hζ q S P hP a
        let b : BL F ζ hζ q S P := ⟨S.borel.torus a', ⟨S.borel.torus a',
          by change S.borel.retract (S.borel.torus a') ∈ HL F ζ hζ q S P
             rw [S.borel.retract_torus]
             exact a'.property, rfl⟩⟩
        have hf := f.property.1 b ((S.borel.torus (S.borel.weyl.symm t) : ActualCover F ζ hζ q) * g)
        have hnorm : ∀ x y : (LocalField F q)ˣ,
            normPower (LocalField F q) (x * y) (1 / 2) =
              normPower (LocalField F q) x (1 / 2) * normPower (LocalField F q) y (1 / 2) := by
          intro x y
          simp [normPower, localAbs_mul, Real.log_mul (ne_of_gt (localAbs_pos _ _))
            (ne_of_gt (localAbs_pos _ _)), mul_add, Complex.exp_add]
        change (normPower (LocalField F q) (S.borel.coordinate (S.borel.weyl.symm (a * t))) (1 / 2))⁻¹ *
          f.val ((S.borel.torus (S.borel.weyl.symm (a * t)) : ActualCover F ζ hζ q) * g) = _
        have hr : retractL F ζ hζ q S P b = a' := by
          apply Subtype.ext
          change S.borel.retract (S.borel.torus a') = a'
          exact S.borel.retract_torus a'
        change f.val ((S.borel.torus a' : ActualCover F ζ hζ q) *
          ((S.borel.torus (S.borel.weyl.symm t) : ActualCover F ζ hζ q) * g)) = _ at hf
        have hw : S.borel.weyl.symm a = a' := weyl_symm_eq F ζ hζ q S a
        simp only [map_mul, hw, Subgroup.coe_mul, mul_assoc, hf, chi, chiH, hr, hnorm]
        simp only [mul_inv_rev]
        have hn : normPower (LocalField F q) (S.borel.coordinate a') (1 / 2) ≠ 0 :=
          Complex.exp_ne_zero _
        change _ = (P.ωL a : ℂ) * _
        have ha : weylHL F ζ hζ q S P hP a' = a := by
          apply Subtype.ext
          exact weyl_involutive F ζ hζ q S a
        rw [ha]
        field_simp
        <;> ring
⟩, by
    apply KPTameTransposeSectionReconstruction.reconstruction_section_membership
      F ζ hζ q S P hP ε f
    intro g t
    rfl⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext g
    apply Subtype.ext
    funext t
    cases ε with
    | plus =>
      have hf := congrArg (fun v : InducedModule P => v.val 1)
        (f.property.1 (S.borel.torus t) g)
      dsimp [inducingAction, inducingScalar, deltaHalf, borelAction, tau,
        inducedRepresentation, Representation.subrepresentation,
        rightTranslationRepresentation] at hf ⊢
      simp only [S.borel.retract_torus, normPower, zero_mul, Complex.exp_zero,
        mul_one, one_mul, Pi.smul_apply, smul_eq_mul] at hf ⊢
      rw [hf]
      dsimp [rightTranslate]
      simp [S.borel.retract_torus, Complex.exp_ne_zero,
        ContinuousMulEquiv.apply_symm_apply]
      change (f.val g).val (1 * _) = (f.val g).val t
      simp
    | minus =>
      have hf := congrArg (fun v : InducedModule P => v.val 1)
        (f.property.1 (S.borel.torus (S.borel.weyl.symm t)) g)
      dsimp [inducingAction, inducingScalar, deltaHalf, borelAction, tau,
        weylConjugate, inducedRepresentation, Representation.subrepresentation,
        rightTranslationRepresentation] at hf ⊢
      simp only [S.borel.retract_torus, normPower, zero_mul, Complex.exp_zero,
        mul_one, one_mul, Pi.smul_apply, smul_eq_mul,
        ContinuousMulEquiv.apply_symm_apply] at hf ⊢
      rw [hf]
      dsimp [rightTranslate]
      simp [S.borel.retract_torus, Complex.exp_ne_zero,
        ContinuousMulEquiv.apply_symm_apply]
      change (f.val g).val (1 * _) = (f.val g).val t
      simp
      exact congrArg (f.val g).val (S.borel.weyl.apply_symm_apply t)
  right_inv := by
    intro f
    apply Subtype.ext
    funext g
    cases ε <;>
      simp [normPower, map_one, localAbs_one]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

variable (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (ξ : (valuation (LocalField F q)).integer) (hξ : IsPrimitiveRoot ξ 3)

def deformedTest (f : scalarSections F ζ hζ q S P hP .minus) (s : ℂ) :
    sectionSpace S.borel P .minus (sourceParameter .minus s) :=
  compactTrivialization S.borel P S.iwasawa .minus (sourceParameter .minus s)
    ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
      ((scalarCoordinateEquiv F ζ hζ q S P hP .minus).symm f))

def diagonalLift (π : (LocalField F q)ˣ) (f : DiagonalValuations) :
    ActualCover F ζ hζ q :=
  KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
    (KPLocalCover.sectionMap F ζ hζ (Sum.inr q)
      (KubotaRankTwo.d (LocalField F q) (π ^ f.1) (π ^ f.2)))

def testSupport (a : ActualCover F ζ hζ q) (m : ℕ) : Set (ActualCover F ζ hζ q) :=
  {g | ∃ (b : BL F ζ hζ q S P) (k : ActualCover F ζ hζ q),
    k ∈ splitCongruenceSet F ζ hζ q m ∧
      g = b * a * k * KPPGLLocalCover.W F ζ hζ (Sum.inr q)}

def IsMinusTest (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus) : Prop :=
  (∀ k ∈ splitCongruenceSet F ζ hζ q m,
    scalarAction F ζ hζ q S P hP .minus k f = f) ∧
  Function.support f.val ⊆ testSupport F ζ hζ q S P a m ∧
  f.val (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) = 1

def lowShell : Set (LocalField F q) := (valuation (LocalField F q)).integer

def conductorOneShell (π : (LocalField F q)ˣ) : Set (LocalField F q) :=
  expandingBall F q π 1 \ lowShell F q

end DedekindZetaZeroFree.KPTameTransposeKernelUnfolding

end

end
