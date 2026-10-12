module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

open scoped NumberField Classical
open NumberField

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

theorem nrComplexPlaces_pos {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) : 0 < InfinitePlace.nrComplexPlaces F := by
  classical
  let w : InfinitePlace F := Classical.arbitrary _
  have : Nonempty {w : InfinitePlace F // w.IsComplex} := ⟨⟨w, A.complex_place w⟩⟩
  exact Fintype.card_pos

def radialSection {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) : A.G :=
  (fun w =>
    Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)).symm.toMonoidHom
      (Units.mk0 ((T ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) : ℝ) : ℂ)
        (Complex.ofReal_ne_zero.mpr
          (Real.rpow_pos_of_pos hT (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))).ne')),
    fun _ => 1)

theorem norm_radialSection {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) :
    A.norm (A.radialSection T hT) = T := by
  classical
  have hlocal (w : InfinitePlace F) :
      ‖((A.radialSection T hT).1 w : w.Completion)‖ =
        T ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) := by
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)
    have hd := e.dist_eq ((A.radialSection T hT).1 w : w.Completion) 0
    change dist
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w))
        ((A.radialSection T hT).1 w : w.Completion))
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)) 0) = _ at hd
    simpa [radialSection, dist_zero_right, Complex.norm_real,
      abs_of_pos (Real.rpow_pos_of_pos hT _)] using hd.symm
  have hc : Fintype.card (InfinitePlace F) = InfinitePlace.nrComplexPlaces F :=
    (Fintype.card_congr (Equiv.subtypeUnivEquiv A.complex_place)).symm
  have hn : (InfinitePlace.nrComplexPlaces F : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr A.nrComplexPlaces_pos).ne'
  unfold norm
  simp_rw [hlocal]
  have hfinite : (∏ v : {v // v ∈ A.Sf},
      ‖((A.radialSection T hT).2 v : v.val.adicCompletion F)‖) = 1 := by
    simp [radialSection]
  rw [hfinite, mul_one, Finset.prod_const, Finset.card_univ, hc]
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  have hexp : 1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)) *
      ((2 * InfinitePlace.nrComplexPlaces F : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [hexp, Real.rpow_one]

theorem radialSection_one {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) : A.radialSection 1 (by norm_num) = 1 := by
  ext w <;> simp [radialSection]

theorem radialSection_mul {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') :
    A.radialSection (T * T') (mul_pos hT hT') =
      A.radialSection T hT * A.radialSection T' hT' := by
  ext w <;> simp [radialSection, Real.mul_rpow hT.le hT'.le]

theorem continuous_radialSection {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) :
    Continuous (fun T : {T : ℝ // 0 < T} => A.radialSection T.val T.property) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    let p : ℝ := 1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))
    have hp : Continuous (fun T : {T : ℝ // 0 < T} => T.val ^ p) :=
      continuous_subtype_val.rpow_const (fun T => Or.inl T.property.ne')
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place w)
    have he : Continuous e.symm :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (A.complex_place w)).symm.continuous
    have hu : Continuous (fun T : {T : ℝ // 0 < T} =>
        Units.mk0 ((T.val ^ p : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos T.property p).ne')) := by
      apply Units.continuous_iff.mpr
      constructor
      · exact Complex.continuous_ofReal.comp hp
      · simpa only [Units.val_inv_eq_inv_val, Units.val_mk0, Pi.inv_def, Function.comp_def] using
          (Complex.continuous_ofReal.comp hp).inv₀
            (fun T => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos T.property p).ne')
    exact (he.units_map e.symm.toMonoidHom).comp hu
  · exact continuous_const

theorem exteriorNorm_pos {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (I : A.Exterior) : 0 < A.exteriorNorm I := by
  exact lt_of_lt_of_le zero_lt_one (idealNorm_ge_one I.val I.property.1)

theorem normalized_generator_mem_G1 {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (I : A.Exterior) (r : A.R)
    (hr : A.Generates I r) (a : Fˣ) (ha : (a : F) = (r : F)) :
    A.diagonal a / A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I) ∈ A.G1 := by
  change A.norm _ = 1
  have hdiv (x y : A.G) : A.norm (x / y) = A.norm x / A.norm y := by
    simp [norm, norm_div, div_pow, Finset.prod_div_distrib, mul_div_mul_comm]
  rw [hdiv, A.generator_norm I r hr a ha, A.norm_radialSection]
  exact div_self (A.exteriorNorm_pos I).ne'

end
end SArithmeticData
end DedekindZetaZeroFree
