module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneRootParameter

open scoped Valued
open ValuativeRel KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPLocalPrincipalSeries KPLocalStoneVonNeumann

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

def r (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (residueCardinality K : ℝ) : ℂ))

def rUnit (s : ℂ) : ℂˣ :=
  Units.mk0 (r K s) (Complex.exp_ne_zero _)

def t (s : ℂ) : ℂ :=
  (residueCardinality K : ℂ)⁻¹ * r K s ^ 6

variable {K}
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def rootCubeLift (A : LocalBorelData (K := K) (G := G) T) (u : Kˣ) : A.B :=
  A.torus (A.cubeLift (u ^ 2) : H)

theorem rootCubeLift_coordinate (A : LocalBorelData (K := K) (G := G) T) (u : Kˣ) :
    A.coordinate (A.retract (rootCubeLift A u)) = u ^ 6 := by
  simp only [rootCubeLift, A.retract_torus, A.cube_coordinate, ← pow_mul]

def rootCharacter (A : LocalBorelData (K := K) (G := G) T)
    (ε : Sign) (s : ℂ) (u : Kˣ) : ℂ :=
  (match ε with
  | .plus => (T.ω (A.cubeLift (u ^ 2)) : ℂ)
  | .minus => (T.ω (A.weylCenter (A.cubeLift (u ^ 2))) : ℂ)) *
    normPower K (u ^ 6) s

theorem rootCharacter_inducingAction
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (ε : Sign) (s : ℂ) (u : Kˣ) (v : InducedModule P) :
    inducingAction A P ε s (rootCubeLift A u) v =
      (deltaHalf A (rootCubeLift A u) * rootCharacter A ε s u) • v := by
  have hc := (finite_heisenberg_induction T P).2.2.2.1
  cases ε with
  | plus =>
    change inducingScalar A s (rootCubeLift A u) •
      (tau P (A.retract (rootCubeLift A u)) v) = _
    rw [show A.retract (rootCubeLift A u) = (A.cubeLift (u ^ 2) : H) from
      A.retract_torus _ , hc]
    simp only [inducingScalar, rootCubeLift_coordinate, rootCharacter, smul_smul]
    congr 1
    change deltaHalf A (rootCubeLift A u) * normPower K (u ^ 6) s * (T.ω _ : ℂ) = _
    ring
  | minus =>
    change inducingScalar A s (rootCubeLift A u) •
      (tau P (A.weyl (A.retract (rootCubeLift A u))) v) = _
    rw [show A.retract (rootCubeLift A u) = (A.cubeLift (u ^ 2) : H) from
      A.retract_torus _, ← A.weylCenter_coe, hc]
    simp only [inducingScalar, rootCubeLift_coordinate, rootCharacter, smul_smul]
    congr 1
    change deltaHalf A (rootCubeLift A u) * normPower K (u ^ 6) s * (T.ω _ : ℂ) = _
    ring

private theorem abs_pow (u : Kˣ) (n : ℕ) : localAbs K (u ^ n) = localAbs K u ^ n := by
  induction n with
  | zero => simp [localAbs_one]
  | succ n ih => simp only [pow_succ, localAbs_mul, ih]

theorem rootCharacter_uniformizer
    (A : LocalBorelData (K := K) (G := G) T) (s : ℂ) (π : Kˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (valuation K (π : K)) = WithZero.exp (-1 : ℤ)) :
    rootCharacter A .plus s π = t K s := by
  have hq : 0 < (residueCardinality K : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := 𝓀[K]))
  have ha : localAbs K π = (residueCardinality K : ℝ)⁻¹ := by
    simp only [localAbs, hπ, WithZero.log_exp]
    norm_cast
    simp
  have hl : Real.log (localAbs K (π ^ 6)) = -6 * Real.log (residueCardinality K : ℝ) := by
    rw [abs_pow, ha, Real.log_pow, Real.log_inv]
    ring
  rw [rootCharacter, A.exceptional_cube, ← pow_mul]
  norm_num only [show (2 : ℕ) * 3 = 6 from rfl]
  simp only [normPower, hl, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  have hex : Complex.exp ((1 / 6 : ℂ) * (-6 * (Real.log (residueCardinality K : ℝ) : ℂ))) =
      (residueCardinality K : ℂ)⁻¹ := by
    rw [show (1 / 6 : ℂ) * (-6 * (Real.log (residueCardinality K : ℝ) : ℂ)) =
      -(Real.log (residueCardinality K : ℝ) : ℂ) by ring, Complex.exp_neg,
      ← Complex.ofReal_exp, Real.exp_log hq]
    simp
  rw [hex]
  unfold t r
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rootCharacter_weyl_inversion
    (A : LocalBorelData (K := K) (G := G) T) (s : ℂ) (u : Kˣ) :
    rootCharacter A .minus (-s) u = (rootCharacter A .plus s u)⁻¹ := by
  simp only [rootCharacter, A.weyl_cube, map_inv, Units.val_inv_eq_inv_val,
    neg_mul, normPower, Complex.exp_neg, mul_inv_rev]
  rw [mul_comm]

end
end DedekindZetaZeroFree.KPRankOneRootParameter
