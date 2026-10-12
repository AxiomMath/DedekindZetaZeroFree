module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ScalarSectionDecay
public import DedekindZetaZeroFree.Eisenstein.Induction.ProjectiveHeightSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def p1Inf : KPHeightSeries.P1 F :=
  Projectivization.mk (K := F) (![1, 0] : Fin 2 → F) (by
    intro h; have := congrFun h 0; simp at this)

 def p1Fin (t : F) : KPHeightSeries.P1 F :=
  Projectivization.mk (K := F) (![t, 1] : Fin 2 → F) (by
    intro h; have := congrFun h 1; simp at this)

 def optP1 : Option F → KPHeightSeries.P1 F
  | none => p1Inf F
  | some t => p1Fin F t

private theorem optP1_injective : Function.Injective (optP1 F) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some t =>
      exfalso
      have hh : p1Inf F = p1Fin F t := h
      rw [p1Inf, p1Fin, Projectivization.mk_eq_mk_iff] at hh
      obtain ⟨a, ha⟩ := hh
      have h1 : (a : F) = 0 := by
        simpa [Units.smul_def] using congrFun ha 1
      exact a.ne_zero h1
  | some t =>
    cases j with
    | none =>
      exfalso
      have hh : p1Fin F t = p1Inf F := h
      rw [p1Fin, p1Inf, Projectivization.mk_eq_mk_iff] at hh
      obtain ⟨a, ha⟩ := hh
      have h1 : (a : F) = 0 := by
        simpa [Units.smul_def] using congrFun ha 1
      exact a.ne_zero h1
    | some u =>
      have hh : p1Fin F t = p1Fin F u := h
      rw [p1Fin, p1Fin, Projectivization.mk_eq_mk_iff] at hh
      obtain ⟨a, ha⟩ := hh
      have h1 : (a : F) = 1 := by
        simpa [Units.smul_def] using congrFun ha 1
      have h0 : (a : F) * u = t := by
        simpa [Units.smul_def] using congrFun ha 0
      have : t = u := by rw [← h0, h1, one_mul]
      exact congrArg some this

 noncomputable def chamberCellEquiv :
    KPChamberBruhatTwoCells.RationalQuotient F ≃ Option F :=
  (Equiv.ofBijective (KPChamberBruhatTwoCells.cellIndex F)
    (KPChamberBruhatTwoCells.cellIndex_bijective F)).symm

def chamberCosetIndex (c : KPChamberBruhatTwoCells.RationalQuotient F) :
    KPHeightSeries.P1 F :=
  optP1 F (chamberCellEquiv F c)

theorem chamberCosetIndex_injective : Function.Injective (chamberCosetIndex F) :=
  (optP1_injective F).comp (chamberCellEquiv F).injective

theorem chamberCosetIndex_mulHeight_out
    (c : KPChamberBruhatTwoCells.RationalQuotient F) :
    Projectivization.mulHeight (chamberCosetIndex F c) =
      Projectivization.mulHeight
        (KPChamberHeight.bottomRow F (Quotient.out c)) := by
  obtain ⟨i, rfl⟩ := (KPChamberBruhatTwoCells.cellIndex_bijective F).2 c
  have hi : chamberCellEquiv F (KPChamberBruhatTwoCells.cellIndex F i) = i :=
    (Equiv.ofBijective _ (KPChamberBruhatTwoCells.cellIndex_bijective F)).symm_apply_apply i
  unfold chamberCosetIndex
  rw [hi]
  cases i with
  | none =>
    have he := bottomRow_eq_of_rationalCoset_eq F
      (Quotient.out (KPChamberBruhatTwoCells.cellIndex F none)) 1
      (Quotient.out_eq _)
    rw [he, bottomRow_one_mulHeight]
    simp [optP1, p1Inf, Projectivization.mulHeight_mk]
  | some t =>
    have he := bottomRow_eq_of_rationalCoset_eq F
      (Quotient.out (KPChamberBruhatTwoCells.cellIndex F (some t)))
      (KPChamberBruhatTwoCells.rationalWeyl F *
        KPChamberBruhatTwoCells.rationalUnipotent F t) (Quotient.out_eq _)
    rw [he, bottomRow_open_mulHeight]
    simp [optP1, p1Fin, Projectivization.mulHeight_mk]

theorem chamberCoset_fixed_parameter_height_lower_bound
    (g : KPChamberHeight.AdelPGL F) :
    ∃ m : ℝ, 0 < m ∧ ∀ c : KPChamberBruhatTwoCells.RationalQuotient F,
      m * Projectivization.mulHeight (chamberCosetIndex F c) ≤
        KPChamberHeight.height F
          (KPChamberHeight.bottomRow F (Quotient.out c)) g := by
  obtain ⟨m, hm, hb⟩ := fixed_parameter_height_lower_bound F g
  refine ⟨m, hm, fun c => ?_⟩
  rw [chamberCosetIndex_mulHeight_out]
  exact hb _

theorem chamberCosetHeightBound (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    ∃ B : ℝ, ∀ c : KPChamberBruhatTwoCells.RationalQuotient F,
      ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤
        B * KPHeightSeries.term (Projectivization.mulHeight (K := F))
          (2 / 3 + s.re) (chamberCosetIndex F c) := by
  obtain ⟨B, hB, hb⟩ := actualScalarHeightDecay F ζ hζ K hK f s hs
  obtain ⟨m, hm, hlow⟩ := chamberCoset_fixed_parameter_height_lower_bound F
    (coveredHeightProjection F ζ hζ g)
  let a : ℝ := 2 / 3 + s.re
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hq : -2 * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num) ha
  refine ⟨B * m ^ (-2 * a), fun c => ?_⟩
  have he := hb (rationalLift F ζ hζ (Quotient.out c) * g)
  rw [actualBaseRowHeight_rational_mul] at he
  have hpow :
      (KPChamberHeight.height F (KPChamberHeight.bottomRow F (Quotient.out c))
        (coveredHeightProjection F ζ hζ g)) ^ (-2 * a) ≤
      (m * Projectivization.mulHeight (chamberCosetIndex F c)) ^ (-2 * a) :=
    Real.rpow_le_rpow_of_nonpos
      (mul_pos hm (Projectivization.mulHeight_pos _)) (hlow c) hq
  calc
    ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤
        B * (KPChamberHeight.height F (KPChamberHeight.bottomRow F (Quotient.out c))
          (coveredHeightProjection F ζ hζ g)) ^ (-2 * a) := he
    _ ≤ B * (m * Projectivization.mulHeight (chamberCosetIndex F c)) ^ (-2 * a) :=
      mul_le_mul_of_nonneg_left hpow hB
    _ = (B * m ^ (-2 * a)) * KPHeightSeries.term (Projectivization.mulHeight (K := F))
        (2 / 3 + s.re) (chamberCosetIndex F c) := by
      rw [Real.mul_rpow hm.le (Projectivization.mulHeight_pos _).le]
      dsimp [KPHeightSeries.term, a]
      ring

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
