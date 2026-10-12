module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CanonicalCenterFamiliesAndLevelNumerators
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubeCosetDiagonalRegulator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorSpecialization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RationalCompactPicture
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.ArithmeticInducingData
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ExceptionalPlusBruhatExactSequence
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CubicBeta.UnramifiedLargeNormShells
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicCharacterScalarSum
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ValuationShellIntegration
public import DedekindZetaZeroFree.Algebra.IntegerGeometricTails

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRankOneRegulatedDiagonalKernel

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShells KPRankOneReverseRegulatorSpecialization
open KPRankOneLiftedRegulatedDiagonalAlgebra

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def jointRationalDomain : Set (ℂ × ℂ) :=
  {p | (residueCardinality (LocalField F q) : ℝ)⁻¹ < ‖p.2‖ ∧
    ‖p.2‖ < 1 ∧ ‖p.2‖ ^ 3 < ‖t F q p.1‖ ∧ ‖t F q p.1‖ < 1}

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in

theorem jointRationalDomain_open_connected_nonempty :
    IsOpen (jointRationalDomain F q) ∧
      IsPreconnected (jointRationalDomain F q) ∧
      (jointRationalDomain F q).Nonempty := by
  let c : ℝ := residueCardinality (LocalField F q)
  have hc : 1 < c := by
    change (1 : ℝ) < (residueCardinality (LocalField F q) : ℝ)
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField (Valuation.integer (ValuativeRel.valuation (LocalField F q)))))
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  let l := Real.log c
  have hl : 0 < l := Real.log_pos hc
  let E : ℂ × ℂ → ℂ × ℂ := fun z => (Complex.exp z.1, Complex.exp z.2)
  let S : Set (ℂ × ℂ) := {z | -l < z.2.re ∧ z.2.re < 0 ∧ 3*z.2.re < 6*z.1.re-l ∧ 6*z.1.re-l < 0}
  have hn (z : ℂ) : ‖t F q (Complex.exp z)‖ = Real.exp (6*z.re-l) := by
    simp only [t, norm_mul, norm_inv, norm_pow, Complex.norm_exp]
    rw [show ‖(residueCardinality (LocalField F q) : ℂ)‖ = c by simp [c]]
    rw [← Real.exp_log hc0, ← Real.exp_neg, ← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  have hE (z : ℂ × ℂ) : E z ∈ jointRationalDomain F q ↔ z ∈ S := by
    change c⁻¹ < ‖Complex.exp z.2‖ ∧ ‖Complex.exp z.2‖ < 1 ∧ ‖Complex.exp z.2‖^3 < ‖t F q (Complex.exp z.1)‖ ∧ ‖t F q (Complex.exp z.1)‖ < 1 ↔ _
    rw [Complex.norm_exp, hn, ← Real.exp_log hc0, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_zero]
    simp only [Real.exp_lt_exp]
    rfl
  have hD : jointRationalDomain F q = E '' S := by
    apply Set.Subset.antisymm
    · intro p hp
      have hQ : p.2 ≠ 0 := norm_pos_iff.mp (lt_trans (inv_pos.mpr hc0) hp.1)
      have ht : t F q p.1 ≠ 0 := norm_pos_iff.mp (lt_trans (pow_pos (norm_pos_iff.mpr hQ) 3) hp.2.2.1)
      have hr : p.1 ≠ 0 := by intro hz; simp [hz, t] at ht
      have he : E (Complex.log p.1, Complex.log p.2) = p := by simp [E, Complex.exp_log hr, Complex.exp_log hQ]
      exact ⟨_, (hE _).mp (he.symm ▸ hp), he⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hE z).mpr hz
  have hs : Convex ℝ S := by
    rw [convex_iff_forall_pos]
    intro x hx y hy a b ha hb hab
    change -l < (a • x.2 + b • y.2).re ∧ (a • x.2 + b • y.2).re < 0 ∧ 3*(a • x.2 + b • y.2).re < 6*(a • x.1 + b • y.1).re-l ∧ 6*(a • x.1 + b • y.1).re-l < 0
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change -l < a*x.2.re+b*y.2.re ∧ a*x.2.re+b*y.2.re < 0 ∧ 3*(a*x.2.re+b*y.2.re) < 6*(a*x.1.re+b*y.1.re)-l ∧ 6*(a*x.1.re+b*y.1.re)-l < 0
    rcases hx with ⟨hx1,hx2,hx3,hx4⟩
    rcases hy with ⟨hy1,hy2,hy3,hy4⟩
    constructor
    · nlinarith [mul_pos ha (sub_pos.mpr hx1), mul_pos hb (sub_pos.mpr hy1)]
    constructor
    · nlinarith [mul_pos ha (neg_pos.mpr hx2), mul_pos hb (neg_pos.mpr hy2)]
    constructor
    · nlinarith [mul_pos ha (sub_pos.mpr hx3), mul_pos hb (sub_pos.mpr hy3)]
    · nlinarith [mul_pos ha (neg_pos.mpr hx4), mul_pos hb (neg_pos.mpr hy4)]
  have hSn : S.Nonempty := by
    refine ⟨(0, (-l/2 : ℝ)), ?_⟩
    change -l < -l/2 ∧ -l/2 < 0 ∧ 3*(-l/2) < 6*0-l ∧ 6*0-l < 0
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun z : ℂ × ℂ => t F q z.1) := continuous_const.mul (continuous_fst.pow 6)
    exact (isOpen_lt continuous_const continuous_snd.norm).inter ((isOpen_lt continuous_snd.norm continuous_const).inter ((isOpen_lt (continuous_snd.norm.pow 3) hcont.norm).inter (isOpen_lt hcont.norm continuous_const)))
  · rw [hD]
    exact hs.isPreconnected.image E ((Complex.continuous_exp.comp continuous_fst).prodMk (Complex.continuous_exp.comp continuous_snd)).continuousOn
  · rw [hD]
    exact hSn.image E

theorem cone_iff_jointRationalDomain (r t₀ : ℂˣ)
    (ht₀ : (t₀ : ℂ) = t F q (r : ℂ)) (lam : ℂ) :
    KPJointRegulator.cone (LocalField F q) t₀ lam ↔
      ((r : ℂ), Q F q lam) ∈ jointRationalDomain F q := by
  have hres : KPCubicUnitIndices.residueCard (LocalField F q) = residueCardinality (LocalField F q) := rfl
  have hq1 : 1 < (residueCardinality (LocalField F q) : ℝ) := by
    rw [← hres]
    exact_mod_cast (lt_of_lt_of_le (by norm_num)
      (KPCubicUnitIndices.two_le_residueCard (LocalField F q)))
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := lt_trans one_pos hq1
  have lt_iff : ∀ a b : ℝ,
      (residueCardinality (LocalField F q) : ℝ).rpow a
        < (residueCardinality (LocalField F q) : ℝ).rpow b ↔ a < b := by
    intro a b
    change (residueCardinality (LocalField F q) : ℝ) ^ a
      < (residueCardinality (LocalField F q) : ℝ) ^ b ↔ a < b
    exact Real.rpow_lt_rpow_left_iff hq1
  have hneg1 : (residueCardinality (LocalField F q) : ℝ)⁻¹
      = (residueCardinality (LocalField F q) : ℝ).rpow (-1) := by
    change (residueCardinality (LocalField F q) : ℝ)⁻¹
      = (residueCardinality (LocalField F q) : ℝ) ^ (-1 : ℝ)
    exact (Real.rpow_neg_one _).symm
  have hz0 : (1 : ℝ) = (residueCardinality (LocalField F q) : ℝ).rpow 0 := by
    change (1 : ℝ) = (residueCardinality (LocalField F q) : ℝ) ^ (0 : ℝ)
    exact (Real.rpow_zero _).symm
  have hQ : ‖Q F q lam‖ = (residueCardinality (LocalField F q) : ℝ).rpow (-lam.re) := by
    unfold Q
    rw [Complex.norm_exp]
    have hre : (-lam * (Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)).re
        = -lam.re * Real.log (residueCardinality (LocalField F q) : ℝ) := by
      rw [Complex.mul_re]
      simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    rw [hre]
    change Real.exp (-lam.re * Real.log (residueCardinality (LocalField F q) : ℝ))
      = (residueCardinality (LocalField F q) : ℝ) ^ (-lam.re)
    rw [Real.rpow_def_of_pos hq]
    ring_nf
  have hQ3' : ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)) ^ 3
      = (residueCardinality (LocalField F q) : ℝ).rpow (-3 * lam.re) := by
    have hcast : ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)) ^ 3
        = ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)).rpow (3 : ℝ) := by
      change ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)) ^ 3
        = ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)) ^ (3 : ℝ)
      exact (Real.rpow_natCast _ 3).symm
    rw [hcast]
    have hmul : ((residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)).rpow (3 : ℝ)
        = (residueCardinality (LocalField F q) : ℝ).rpow (-lam.re * 3) := by
      change ((residueCardinality (LocalField F q) : ℝ) ^ (-lam.re)) ^ (3 : ℝ)
        = (residueCardinality (LocalField F q) : ℝ) ^ (-lam.re * 3)
      rw [← Real.rpow_mul (le_of_lt hq)]
    rw [hmul]
    congr 1
    ring
  have ht : ‖t F q (r : ℂ)‖ = ‖(t₀ : ℂ)‖ := by rw [ht₀]
  unfold KPJointRegulator.cone jointRationalDomain
  simp only [Set.mem_setOf_eq, hQ, hQ3', ht, hres]
  constructor
  · rintro ⟨h0, h1, hlo, hhi⟩
    refine ⟨?_, ?_, hlo, hhi⟩
    · rw [hneg1]; exact (lt_iff _ _).mpr (by linarith)
    · rw [hz0]; exact (lt_iff _ _).mpr (by linarith)
  · rintro ⟨hlo, hhi, htlo, hthi⟩
    refine ⟨?_, ?_, htlo, hthi⟩
    · have h : (residueCardinality (LocalField F q) : ℝ).rpow (-lam.re)
          < (residueCardinality (LocalField F q) : ℝ).rpow 0 := by
        simpa only [hz0] using hhi
      have := (lt_iff _ _).mp h
      linarith
    · have h : (residueCardinality (LocalField F q) : ℝ).rpow (-1)
          < (residueCardinality (LocalField F q) : ℝ).rpow (-lam.re) := by
        simpa only [hneg1] using hlo
      have := (lt_iff _ _).mp h
      linarith

end

end DedekindZetaZeroFree.KPRankOneRegulatedDiagonalKernel

end
