module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.NormalPrincipalCoefficient

@[expose] public section

open _root_.DedekindZetaZeroFree.KPMsFixedHaarDisintegration renaming toRawTransport → toRawTransport
open _root_.DedekindZetaZeroFree.KPMsFixedHaar.ComponentFiber renaming spherical_fiber_formula → spherical_fiber_formula
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming archEquiv → archEquiv
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming placeEquiv → placeEquiv
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming basepoint_eq → basepoint_eq

open _root_.DedekindZetaZeroFree.KPArithmeticAction renaming origin_fixed_row → origin_fixed_row
open _root_.DedekindZetaZeroFree.KPArithmeticAction renaming normalized_representative → normalized_representative
open _root_.DedekindZetaZeroFree.KPArithmeticAction renaming normalizedMatrixGL → normalizedMatrixGL
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient renaming su_origin → su_origin

noncomputable section
open scoped Classical ENNReal NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar
open KPCompactStabilizerHaarSources
local instance (d : ℕ) : BorelSpace (G d) := ⟨rfl⟩
local instance (d : ℕ) : LocallyCompactSpace (G d) := groupLocallyCompact d
local instance (d : ℕ) : SecondCountableTopology (G d) := groupSecondCountable d
local instance (d : ℕ) : BorelSpace (KPCompactStabilizerHaarSources.K d) := ⟨rfl⟩
local instance (d : ℕ) : CompactSpace (KPCompactStabilizerHaarSources.K d) := stabilizerCompactSpace d
local instance (d : ℕ) : SecondCountableTopology (KPCompactStabilizerHaarSources.K d) := stabilizerSecondCountable d
local instance (d : ℕ) : ContinuousSMul (G d) (KPArch.Space d) :=
  KPArithmeticAction.productContinuousSMul d

private theorem normalized_origin_unitary (a : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hfix : KPArch.action a (0,0) = (0,0))
    (hdet : ‖(a : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1) :
    (a : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨ht,hb⟩ := origin_fixed_row a hfix
  rw [hdet] at ht hb
  have hn := congrArg Prod.fst hfix
  have hz : a 0 0 * star (a 1 0) + a 0 1 * star (a 1 1) = 0 := by
    simp only [KPArch.action, KPArch.actionDenominator, KPArch.height, Real.exp_zero,
      mul_zero, zero_add, one_pow, Complex.ofReal_one, mul_one] at hn
    have hh : (‖a 1 1‖ ^ 2 + ‖a 1 0‖ ^ 2 : ℝ) ≠ 0 := by linarith
    simpa only [add_comm] using
      (div_eq_zero_iff).mp hn |>.resolve_right (by exact_mod_cast hh)
  have hzc : a 1 0 * star (a 0 0) + a 1 1 * star (a 0 1) = 0 := by
    have h := congrArg star hz
    simpa only [star_add, star_mul, star_star, star_zero, mul_comm] using h
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply,
      ↓reduceIte]
  · change a 0 0 * star (a 0 0) + a 0 1 * star (a 0 1) = 1
    simpa only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_add, Complex.ofReal_inj, Complex.ofReal_one] using
      congrArg Complex.ofReal ht
  · change a 0 0 * star (a 1 0) + a 0 1 * star (a 1 1) = 0
    exact hz
  · change a 1 0 * star (a 0 0) + a 1 1 * star (a 0 1) = 0
    exact hzc
  · change a 1 0 * star (a 1 0) + a 1 1 * star (a 1 1) = 1
    simpa only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_add, Complex.ofReal_inj, Complex.ofReal_one] using
      congrArg Complex.ofReal hb

 theorem compactSubgroup_eq_origin_stabilizer :
    KPCplxPrincipalSeriesCharts.compactSubgroup =
      MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) ℂ) ((0,0) : KPArch.H3) := by
  ext g
  constructor
  · rintro ⟨k,rfl⟩
    exact su_origin k
  · intro hg
    obtain ⟨a,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    obtain ⟨A,hA⟩ := normalized_representative a hg
    let b := normalizedMatrixGL A
    have hb : KPArch.action b (0,0) = (0,0) := by
      change Matrix.ProjGenLinGroup.mk b • ((0,0) : KPArch.H3) = (0,0)
      rw [hA]
      exact hg
    have hd : ‖(b : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 := A.property.1
    let u : Matrix.unitaryGroup (Fin 2) ℂ := ⟨b, normalized_origin_unitary b hb hd⟩
    obtain ⟨c,hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup u
    let k : KPCplxCharacterHaar.ComplexSU2 := ⟨(c : ℂ) • u.val,hc⟩
    refine ⟨k, ?_⟩
    change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k) =
      Matrix.ProjGenLinGroup.mk a
    rw [← hA, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 ((c : ℂ)⁻¹) (inv_ne_zero (Circle.coe_ne_zero c)), ?_⟩
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one]
    change (c : ℂ)⁻¹ • ((c : ℂ) • (b : Matrix (Fin 2) (Fin 2) ℂ)) = _
    rw [inv_smul_smul₀ (Circle.coe_ne_zero c)]

 def endpointCompactEquiv (d : ℕ) :
    (Fin d → KPCplxPrincipalSeriesCharts.compactSubgroup) ≃ₜ*
      KPCompactStabilizerHaarSources.K d where
  toMulEquiv :=
    { toFun k := ⟨fun i => (k i).val, by
        change (fun i => (k i).val) • o d = o d
        funext i
        exact (show (k i).val ∈
          MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) ℂ) ((0,0) : KPArch.H3) by
            rw [← compactSubgroup_eq_origin_stabilizer]; exact (k i).property)⟩
      invFun k := fun i => ⟨k.val i, by
        rw [compactSubgroup_eq_origin_stabilizer]
        have h := congrFun k.property i
        exact h⟩
      left_inv k := by ext i; rfl
      right_inv k := by ext i; rfl
      map_mul' k l := rfl }
  continuous_toFun :=
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

local instance (d : ℕ) : MeasurableSpace (Fin d → KPCplxPrincipalSeriesCharts.compactSubgroup) := borel _
local instance (d : ℕ) : BorelSpace (Fin d → KPCplxPrincipalSeriesCharts.compactSubgroup) := ⟨rfl⟩
local instance (d : ℕ) : CompactSpace (Fin d → KPCplxPrincipalSeriesCharts.compactSubgroup) :=
  (endpointCompactEquiv d).symm.toHomeomorph.compactSpace

section NumberField
open scoped NumberField
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 def endpointPlaceEquiv : KPMsGreenFlux.K F ≃ₜ*
    (Fin (KPCuspLogShape.dimension F) → KPCplxPrincipalSeriesCharts.compactSubgroup) where
  toMulEquiv :=
    { toFun k := fun i => k (KPCusp.complexPlace F i)
      invFun k := fun w => k (placeEquiv F ζ hζ w)
      left_inv k := by
        funext w
        exact congrArg k ((placeEquiv F ζ hζ).left_inv w)
      right_inv k := by
        funext i
        exact congrArg k ((placeEquiv F ζ hζ).right_inv i)
      map_mul' k l := rfl }
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun w => continuous_apply _

local instance : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
local instance : BorelSpace (KPMsGreenFlux.K F) := ⟨rfl⟩

end NumberField

end DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabFullAngularHaar

end
