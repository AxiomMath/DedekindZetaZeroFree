module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCentralCharacter
public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CenterCharacterPolarization

@[expose] public section

section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ProductPolarizationCharacterDescent
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem scalar_d (v : KPHilbert.Place F) (z y : (KPHilbert.Completion F v)ˣ) :
    KPScalarSplitCentral.scalarMatrix F v z * KubotaRankTwo.d _ y 1 =
      KubotaRankTwo.d _ (z * y) z := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPScalarSplitCentral.scalarMatrix, Matrix.mul_apply, Matrix.scalar]

private theorem scalar_diag_sigma (v : KPHilbert.Place F)
    (z y : (KPHilbert.Completion F v)ˣ)
    (hy : KPGlobalCubicIdelePairing.localClass F v y = 1) :
    KPLocalCover.sigmaTwo F ζ hζ v (KPScalarSplitCentral.scalarMatrix F v z)
      (KubotaRankTwo.d _ y 1) = 1 := by
  have hcube : y ∈ CubicCharacters.cubes (KPHilbert.Completion F v)ˣ :=
    (QuotientGroup.eq_one_iff y).mp hy
  obtain ⟨t, rfl⟩ := hcube
  have hB := (KPHilbert.B3_laws F ζ hζ v).2.2.2.2.1
  have hOne := KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ v).1
  have hx : KubotaRankTwo.X (KPHilbert.Completion F v)
      (KPScalarSplitCentral.scalarMatrix F v z) = z := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPScalarSplitCentral.scalarMatrix, Matrix.scalar]
  simp [KPLocalCover.sigmaTwo, KubotaElementaryLastArgument.tau, scalar_d,
    hx, KubotaRankTwo.det, hB, hOne, KPScalarSplitCentral.scalarMatrix]

private theorem localValue_scalar_diag (v : KPHilbert.Place F)
    (e : rootsOfUnity 3 F) (z y : (KPHilbert.Completion F v)ˣ)
    (hy : KPGlobalCubicIdelePairing.localClass F v y = 1) :
    KPGlobalCenterRationalCharacter.localValue F ζ hζ v
      (KPScalarSplitCentral.scalarHom F ζ hζ v z *
        (KPLocalCover.centralInjection F ζ hζ v e * KPStandardLocalRootLifts.A F ζ hζ v y)) =
      KPGlobalTorusFunctionData.iota F ζ hζ e *
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
            (KPGlobalCenterRationalCharacter.localAbs F v y)
            (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F v y)))) := by
  have hg : (KPScalarSplitCentral.scalarHom F ζ hζ v z *
      (KPLocalCover.centralInjection F ζ hζ v e * KPStandardLocalRootLifts.A F ζ hζ v y)).g =
      KubotaRankTwo.d _ (z * y) z := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPStandardLocalRootLifts.A, scalar_d]
  have he : (KPScalarSplitCentral.scalarHom F ζ hζ v z *
      (KPLocalCover.centralInjection F ζ hζ v e * KPStandardLocalRootLifts.A F ζ hζ v y)).epsilon = e := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPStandardLocalRootLifts.A, scalar_diag_sigma F ζ hζ v z y hy]
  have h1 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) (z * y) z :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) := by
    rw [KubotaRankTwo.coe_d]; exact Units.isUnit (z * y)
  have h2 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) (z * y) z :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) := by
    rw [KubotaRankTwo.coe_d]; exact Units.isUnit z
  unfold KPGlobalCenterRationalCharacter.localValue
  simp only [hg, he]
  rw [dif_pos ⟨h1, h2⟩]
  have hunit : h1.unit * h2.unit⁻¹ = y := by
    ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec, IsUnit.unit_spec,
      KubotaRankTwo.coe_d]
    change ((z * y : (KPHilbert.Completion F v)ˣ) : KPHilbert.Completion F v) *
      (z : KPHilbert.Completion F v)⁻¹ = (y : KPHilbert.Completion F v)
    simp only [Units.val_mul]
    field_simp
  congr 1
  congr 1
  congr 1
  apply Units.ext
  show KPGlobalCenterRationalCharacter.localAbs F v (h1.unit * h2.unit⁻¹) =
    KPGlobalCenterRationalCharacter.localAbs F v y
  rw [hunit]

theorem raw_value_on_cube_normal_word (v : KPHilbert.Place F)
    (e : rootsOfUnity 3 F) (y : (KPHilbert.Completion F v)ˣ)
    (hy : KPGlobalCubicIdelePairing.localClass F v y = 1)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg : KPPGLLocalCover.coverQuotient F ζ hζ v g =
      KPPGLLocalCover.centralInjection F ζ hζ v e * KPPGLLocalCover.A F ζ hζ v y) :
    KPGlobalCenterRationalCharacter.localValue F ζ hζ v g =
      KPGlobalTorusFunctionData.iota F ζ hζ e *
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
            (KPGlobalCenterRationalCharacter.localAbs F v y)
            (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F v y)))) := by
  have hq : KPPGLLocalCover.coverQuotient F ζ hζ v g =
      KPPGLLocalCover.coverQuotient F ζ hζ v
        (KPLocalCover.centralInjection F ζ hζ v e * KPStandardLocalRootLifts.A F ζ hζ v y) := by
    simpa [map_mul, KPPGLLocalCover.centralInjection, KPPGLLocalCover.A] using hg
  have hm : g / (KPLocalCover.centralInjection F ζ hζ v e *
      KPStandardLocalRootLifts.A F ζ hζ v y) ∈ KPPGLLocalCover.splitScalarSubgroup F ζ hζ v :=
    QuotientGroup.eq_iff_div_mem.mp hq
  obtain ⟨z, hz⟩ := hm
  have hrep : g = KPScalarSplitCentral.scalarHom F ζ hζ v z *
      (KPLocalCover.centralInjection F ζ hζ v e * KPStandardLocalRootLifts.A F ζ hζ v y) := by
    rw [hz]
    simp only [div_mul_cancel]
  rw [hrep]
  exact localValue_scalar_diag F ζ hζ v e z y hy

end
end DedekindZetaZeroFree.ProductPolarizationCharacterDescent

end

section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarizationCharacterDescent
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (w : InfinitePlace F)
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
variable (S : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w)))
variable (hS : ∀ z : S, ∃ y : (KPHilbert.Completion F (Sum.inl w))ˣ, KPPGLLocalCover.baseQuotient F (Sum.inl w) (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) y 1) = KPPGLLocalCover.projection F ζ hζ (Sum.inl w) z.val)
include hS in
 theorem raw_diag (g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)))) : ∃ a b : (KPHilbert.Completion F (Sum.inl w))ˣ, g.val.g = KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) a b := by
  obtain ⟨y, hy⟩ := hS ⟨_, g.property⟩
  change KPPGLLocalCover.baseQuotient F (Sum.inl w) (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) y 1) = KPPGLLocalCover.baseQuotient F (Sum.inl w) g.val.g at hy
  simp only [KPPGLLocalCover.baseQuotient] at hy
  rw [QuotientGroup.mk'_eq_mk'] at hy
  obtain ⟨z, ⟨b, rfl⟩, hz⟩ := hy
  refine ⟨y * b, b, hz.symm.trans ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [KPScalarSplitCentral.scalarMatrix, Matrix.mul_apply, Matrix.scalar]
include hS in
 theorem raw_nonzero (g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)))) : g.val.g 0 0 ≠ 0 ∧ g.val.g 1 1 ≠ 0 := by
  obtain ⟨a,b,h⟩ := raw_diag F ζ hζ w S hS g
  rw [h, KubotaRankTwo.coe_d]
  exact ⟨a.ne_zero, b.ne_zero⟩
 def ratio (g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)))) : (KPHilbert.Completion F (Sum.inl w))ˣ :=
  Units.mk0 (g.val.g 0 0 / g.val.g 1 1) (div_ne_zero (raw_nonzero F ζ hζ w S hS g).1 (raw_nonzero F ζ hζ w S hS g).2)
 theorem ratio_diag (g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)))) (a b : (KPHilbert.Completion F (Sum.inl w))ˣ) (h : g.val.g = KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) a b) : ratio F ζ hζ w S hS g = a / b := by
  apply Units.ext
  simp [ratio,h]
 def ratioHom : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) →* (KPHilbert.Completion F (Sum.inl w))ˣ where
  toFun := ratio F ζ hζ w S hS
  map_one' := by apply Units.ext; simp [ratio]
  map_mul' x y := by
    obtain ⟨a,b,hx⟩ := raw_diag F ζ hζ w S hS x
    obtain ⟨c,d,hy⟩ := raw_diag F ζ hζ w S hS y
    have hxy : (x*y).val.g = KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) (a*c) (b*d) := by
      change x.val.g * y.val.g = _
      rw [hx,hy]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
    rw [ratio_diag F ζ hζ w S hS x a b hx, ratio_diag F ζ hζ w S hS y c d hy, ratio_diag F ζ hζ w S hS (x*y) (a*c) (b*d) hxy]
    exact mul_div_mul_comm a c b d
private theorem ratio_cont : Continuous (ratioHom F ζ hζ w S hS) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  have hc : Continuous (fun g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) => g.val.g) := by
    have ht : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) := continuous_induced_dom
    exact (continuous_fst.comp ht).comp continuous_subtype_val
  have hm : Continuous (fun g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) => (g.val.g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))) := Units.continuous_val.comp hc
  have h00 : Continuous (fun g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) => g.val.g 0 0) := (continuous_apply _).comp ((continuous_apply _).comp hm)
  have h11 : Continuous (fun g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) => g.val.g 1 1) := (continuous_apply _).comp ((continuous_apply _).comp hm)
  apply Units.continuous_iff.mpr
  constructor
  · exact h00.div h11 (fun g => (raw_nonzero F ζ hζ w S hS g).2)
  · change Continuous (fun g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) => (g.val.g 0 0 / g.val.g 1 1)⁻¹)
    exact (h00.div h11 (fun g => (raw_nonzero F ζ hζ w S hS g).2)).inv₀ (fun g => div_ne_zero (raw_nonzero F ζ hζ w S hS g).1 (raw_nonzero F ζ hζ w S hS g).2)
 def normHom : (KPHilbert.Completion F (Sum.inl w))ˣ →* (ℝ≥0)ˣ :=
  (powMonoidHom 2).comp (Units.map nnnormHom.toMonoidHom)
private theorem normHom_formula (y : (KPHilbert.Completion F (Sum.inl w))ˣ) :
    normHom F w y = Units.mk0 (KPGlobalCenterRationalCharacter.localAbs F (Sum.inl w) y) (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inl w) y)) := by
  apply Units.ext
  rfl
 def sheetHom : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) →* rootsOfUnity 3 F where
  toFun g := g.epsilon
  map_one' := rfl
  map_mul' g h := by
    change g.epsilon * h.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) g.g h.g = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
 def rawChar : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) →* ℂˣ :=
  ((KPGlobalTorusFunctionData.iota F ζ hζ).comp ((sheetHom F ζ hζ w).comp (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))).subtype)) *
  (KPGlobalCenterRationalCharacter.positiveComplex.comp (KPGlobalCenterRationalCharacter.sixthPower.comp ((normHom F w).comp (ratioHom F ζ hζ w S hS))))
private theorem rawChar_cont : Continuous (rawChar F ζ hζ w S hS) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  have hc : Continuous (KPLocalChartTopology.complexCoordinates F ζ hζ w) := continuous_induced_dom
  have hs : Continuous (sheetHom F ζ hζ w) := continuous_snd.comp hc
  have hi : Continuous (KPGlobalTorusFunctionData.iota F ζ hζ) := continuous_of_discreteTopology
  have hn : Continuous (normHom F w) := by
    exact (continuous_pow 2).comp (Continuous.units_map _ continuous_nnnorm)
  have h6 : Continuous KPGlobalCenterRationalCharacter.sixthPower :=
    Continuous.units_map _ (NNReal.continuous_rpow_const (by positivity))
  have hp : Continuous KPGlobalCenterRationalCharacter.positiveComplex :=
    Continuous.units_map _ (Complex.continuous_ofReal.comp NNReal.continuous_coe)
  exact (hi.comp (hs.comp continuous_subtype_val)).mul (hp.comp (h6.comp (hn.comp (ratio_cont F ζ hζ w S hS))))
 def toS : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) →* S :=
  (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)).subgroupComap S
private theorem toS_surj : Function.Surjective (toS F ζ hζ w S) := by
  intro z
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inl w)) z.val
  refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) g ∈ S
  rw [show KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) g = z.val from hg]
  exact z.property
private theorem toS_open : IsOpenQuotientMap (toS F ζ hζ w S) := by
  letI : IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) := (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
  have hc : Continuous (toS F ζ hζ w S) :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have ho : IsOpenMap (toS F ζ hζ w S) :=
    (@QuotientGroup.isOpenMap_coe _ _ _ _ (KPPGLLocalCover.splitScalarSubgroup F ζ hζ (Sum.inl w))).restrictPreimage (S : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w)))
  exact ⟨toS_surj F ζ hζ w S, hc, ho⟩
private theorem toS_ker : (toS F ζ hζ w S).ker ≤ (rawChar F ζ hζ w S hS).ker := by
  intro g hg
  have hg1 : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) g.val = 1 := congrArg Subtype.val hg
  obtain ⟨a,ha⟩ := (QuotientGroup.eq_one_iff g.val).mp hg1
  have hm : g.val.g = KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) a a := by
    rw [← ha]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift, KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap, Matrix.scalar]
  have hr : ratioHom F ζ hζ w S hS g = 1 := by
    change ratio F ζ hζ w S hS g = 1
    rw [ratio_diag F ζ hζ w S hS g a a hm, div_self']
  have he : (sheetHom F ζ hζ w) g.val = 1 := by
    rw [← ha]
    rfl
  change rawChar F ζ hζ w S hS g = 1
  simp [rawChar, hr, he]

theorem complex_diagonal_subgroup_character (w : InfinitePlace F)
    (S : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w)))
    (hS : ∀ z : S, ∃ y : (KPHilbert.Completion F (Sum.inl w))ˣ,
      KPPGLLocalCover.baseQuotient F (Sum.inl w)
        (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) y 1) =
          KPPGLLocalCover.projection F ζ hζ (Sum.inl w) z.val) :
    ∃ ω : S →ₜ* ℂˣ, ∀ (z : S) (e : rootsOfUnity 3 F)
      (y : (KPHilbert.Completion F (Sum.inl w))ˣ),
      z.val = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inl w) e *
        KPPGLLocalCover.A F ζ hζ (Sum.inl w) y →
      ω z = KPGlobalTorusFunctionData.iota F ζ hζ e *
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
            (KPGlobalCenterRationalCharacter.localAbs F (Sum.inl w) y)
            (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inl w) y)))) := by
  let f := toS F ζ hζ w S
  have hf := toS_surj F ζ hζ w S
  let c := rawChar F ζ hζ w S hS
  have hk : f.ker ≤ c.ker := toS_ker F ζ hζ w S hS
  let ω : S →* ℂˣ := f.liftOfSurjective hf ⟨c, hk⟩
  have hw (g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)))) : ω (f g) = c g := by
    exact MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨c, hk⟩ g
  have hc : Continuous ω := by
    apply (toS_open F ζ hζ w S).continuous_comp_iff.mp
    have heq : ω ∘ f = c := funext hw
    rw [heq]
    exact rawChar_cont F ζ hζ w S hS
  refine ⟨{ ω with continuous_toFun := hc }, ?_⟩
  intro z e y hz
  let g : (S.comap (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w))) :=
    ⟨KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y, by
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (_ * _) ∈ S
      rw [map_mul]
      change KPPGLLocalCover.centralInjection F ζ hζ (Sum.inl w) e * KPPGLLocalCover.A F ζ hζ (Sum.inl w) y ∈ S
      rw [← hz]
      exact z.property⟩
  have hgz : f g = z := by
    apply Subtype.ext
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (_ * _) = z.val
    rw [map_mul]
    exact hz.symm
  change ω z = _
  rw [← hgz, hw]
  have hm : g.val.g = KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) y 1 := by
    simp [g, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
  have hr : ratioHom F ζ hζ w S hS g = y := by
    change ratio F ζ hζ w S hS g = y
    rw [ratio_diag F ζ hζ w S hS g y 1 hm, div_one]
  have he : sheetHom F ζ hζ w g.val = e := by
    change g.val.epsilon = e
    simp [g, KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
  change KPGlobalTorusFunctionData.iota F ζ hζ (sheetHom F ζ hζ w g.val) *
    KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.sixthPower (normHom F w (ratioHom F ζ hζ w S hS g))) = _
  rw [he, hr, normHom_formula]

end
end DedekindZetaZeroFree.ProductPolarizationCharacterDescent

end

section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ProductPolarization
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev D := KPGlobalCubicIdelePairing.D F
abbrev E := KPGlobalCenterRationalCharacter.E F ζ hζ
abbrev LocalD := KPGlobalCubicIdelePairing.LocalD F

attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology

def localCoverTopology (v : KPHilbert.Place F) :
    TopologicalSpace (KPPGLLocalCover.CubicPGL2 F ζ hζ v) := inferInstance

attribute [local instance] localCoverTopology

def diagonalHom (v : KPHilbert.Place F) :
    (KPHilbert.Completion F v)ˣ →* KPLocalCover.LocalGL2 F v where
  toFun y := KubotaRankTwo.d (KPHilbert.Completion F v) y 1
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def localOrdinaryTorus (v : KPHilbert.Place F) :
    Subgroup (KPPGLLocalCover.LocalPGL2 F v) :=
  ((KPPGLLocalCover.baseQuotient F v).comp (diagonalHom F v)).range

def localTorus (v : KPHilbert.Place F) :
    Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ v) :=
  (localOrdinaryTorus F v).comap (KPPGLLocalCover.projection F ζ hζ v)

abbrev LocalE (v : KPHilbert.Place F) := localTorus F ζ hζ v

def localRatioValue (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    (KPHilbert.Completion F v)ˣ := Classical.choose g.property

theorem baseQuotient_diagonalHom_injective (v : KPHilbert.Place F) :
    Function.Injective fun y : (KPHilbert.Completion F v)ˣ =>
      KPPGLLocalCover.baseQuotient F v (diagonalHom F v y) := by
  intro y y' h
  simp only [KPPGLLocalCover.baseQuotient] at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hzN, hz⟩ := h
  obtain ⟨w, hw⟩ := hzN
  have key : diagonalHom F v y * KPScalarSplitCentral.scalarMatrix F v w = diagonalHom F v y' := by
    rw [hw]; exact hz
  have h11 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) key
  have h00 := congrArg (fun g : KPLocalCover.LocalGL2 F v =>
    (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) key
  rw [Matrix.GeneralLinearGroup.coe_mul,
      show diagonalHom F v y = KubotaRankTwo.d (KPHilbert.Completion F v) y 1 from rfl,
      show diagonalHom F v y' = KubotaRankTwo.d (KPHilbert.Completion F v) y' 1 from rfl,
      KubotaRankTwo.coe_d, Matrix.GeneralLinearGroup.coe_scalar] at h11 h00
  simp [Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two] at h11 h00
  have hw1 : w = 1 := by
    apply Units.ext
    simpa using h11
  subst hw1
  exact Units.ext (by simpa using h00)

theorem localRatioValue_spec (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    KPPGLLocalCover.baseQuotient F v (diagonalHom F v (localRatioValue F ζ hζ v g)) =
      KPPGLLocalCover.projection F ζ hζ v g :=
  Classical.choose_spec g.property

theorem localRatioValue_eq (v : KPHilbert.Place F) {g : LocalE F ζ hζ v}
    {y : (KPHilbert.Completion F v)ˣ}
    (hy : KPPGLLocalCover.baseQuotient F v (diagonalHom F v y) =
      KPPGLLocalCover.projection F ζ hζ v g) :
    y = localRatioValue F ζ hζ v g :=
  (baseQuotient_diagonalHom_injective F v
    ((localRatioValue_spec F ζ hζ v g).trans hy.symm).symm)

theorem localRatioValue_one (v : KPHilbert.Place F) :
    localRatioValue F ζ hζ v 1 = 1 := by
  symm
  apply localRatioValue_eq F ζ hζ v
  simp

theorem localRatioValue_mul (v : KPHilbert.Place F) (g h : LocalE F ζ hζ v) :
    localRatioValue F ζ hζ v (g * h) =
      localRatioValue F ζ hζ v g * localRatioValue F ζ hζ v h := by
  symm
  apply localRatioValue_eq F ζ hζ v (g := g * h)
  have hgh : KPPGLLocalCover.projection F ζ hζ v (↑(g * h) : KPPGLLocalCover.CubicPGL2 F ζ hζ v) =
      KPPGLLocalCover.projection F ζ hζ v ↑g * KPPGLLocalCover.projection F ζ hζ v ↑h := by
    rw [show (↑(g * h) : KPPGLLocalCover.CubicPGL2 F ζ hζ v) = ↑g * ↑h from rfl, map_mul]
  rw [hgh, ← localRatioValue_spec F ζ hζ v g, ← localRatioValue_spec F ζ hζ v h]
  rw [map_mul, map_mul]

def localRatio (v : KPHilbert.Place F) :
    LocalE F ζ hζ v →* (KPHilbert.Completion F v)ˣ where
  toFun := localRatioValue F ζ hζ v
  map_one' := localRatioValue_one F ζ hζ v
  map_mul' := localRatioValue_mul F ζ hζ v

def localProjection (v : KPHilbert.Place F) : LocalE F ζ hζ v →* LocalD F v :=
  (KPGlobalCubicIdelePairing.localClass F v).comp (localRatio F ζ hζ v)

def localCenter (v : KPHilbert.Place F) : Subgroup (LocalE F ζ hζ v) :=
  (localProjection F ζ hζ v).ker

 theorem normalizedLocalAbs_norm (q : HeightOneSpectrum (𝓞 F))
    (y : (q.adicCompletion F)ˣ) :
    KPLocalPrincipalSeries.localAbs (q.adicCompletion F) y = ‖(y : q.adicCompletion F)‖ := by
  open MeasureTheory ValuativeRel in
  let K := q.adicCompletion F
  let μ : Measure K := Measure.addHaar
  letI : (Valued.v (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := (IntrinsicHaarScaling.map_mul K μ (y : K) y.ne_zero).symm.trans
    (CompletionHaarModule.map_mul F q μ y)
  have ha : IntrinsicHaarScaling.abs K (y : K) = KPLocalPrincipalSeries.localAbs K y := by
    simp only [IntrinsicHaarScaling.abs, if_neg y.ne_zero, IntrinsicHaarScaling.residueCard,
      KPLocalPrincipalSeries.localAbs, KPLocalPrincipalSeries.residueCardinality, Real.rpow_intCast]
  have hp := KPLocalPrincipalSeries.localAbs_pos K y
  rw [ha, ← ENNReal.ofReal_inv_of_pos hp,
    ← ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr y.ne_zero)] at h
  have hh := congrArg (fun ν : Measure K => ν ((valuation K).integer : Set K)) h
  simp only [Measure.smul_apply, smul_eq_mul] at hh
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have h0 : μ ((valuation K).integer : Set K) ≠ 0 := by
    have he : ((valuation K).integer : Set K) =
        ((Valued.v (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).integer : Set K) := by
      ext x
      change valuation K x ≤ 1 ↔ Valued.v x ≤ 1
      exact (Valuation.vle_one_iff (valuation K)).symm.trans (Valuation.vle_one_iff Valued.v)
    rw [he]
    exact (Valued.isOpen_integer K).measure_ne_zero μ ⟨0, by simp⟩
  have ht : μ ((valuation K).integer : Set K) ≠ ⊤ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
  have hi := (ENNReal.mul_right_inj h0 ht).mp (by simpa only [mul_comm] using hh)
  have hi' := congrArg ENNReal.toReal hi
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))] at hi'
  exact inv_injective hi'

theorem fullnorm_bridgefinite (q : HeightOneSpectrum (𝓞 F))
    (y : (q.adicCompletion F)ˣ) :
    KPGlobalCenterRationalCharacter.positiveComplex
      (KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
        (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y)
        (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) y)))) =
      ActualFiniteTorus.normUnit F q y := by
  apply Units.ext
  simp only [ActualFiniteTorus.normUnit, Units.val_mk0, KPLocalPrincipalSeries.normPower]
  rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by norm_num,
    KPLocalPrincipalSeriesNormWeights.exp_mul_log_real
      (KPLocalPrincipalSeries.localAbs_pos _ _) _, normalizedLocalAbs_norm F q y]
  simp [KPGlobalCenterRationalCharacter.positiveComplex,
    KPGlobalCenterRationalCharacter.sixthPower, KPGlobalCenterRationalCharacter.localAbs,
    NNReal.coe_rpow]
 lemma finiteH_eq (q : HeightOneSpectrum (𝓞 F)) :
    localTorus F ζ hζ (Sum.inr q) = ActualFiniteTorus.H F ζ hζ q := by
  letI : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  apply le_antisymm
  · intro g hg
    obtain ⟨y, hy⟩ := hg
    change KPLocalSmoothRepresentation.projection F ζ hζ q g ∈ KPRankOneInduction.diagonalTorus F q
    refine ⟨diagonalHom F (Sum.inr q) y, ?_, ?_, ?_⟩
    · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) hy
    · simp [diagonalHom, KubotaRankTwo.d]
    · simp [diagonalHom, KubotaRankTwo.d]
  · intro g hg
    let h : ActualFiniteTorus.H F ζ hζ q := ⟨g,hg⟩
    have hn := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 h
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g ∈ localOrdinaryTorus F (Sum.inr q)
    rw [show g = ActualFiniteTorus.normalWord F ζ hζ q _ _ from hn]
    refine ⟨ActualFiniteTorus.coordinate F ζ hζ q h, ?_⟩
    simp only [ActualFiniteTorus.normalWord, map_mul]
    have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (ActualFiniteTorus.sheet F ζ hζ q h)) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
      exact ⟨_, rfl⟩
    rw [hp, one_mul]
    rfl

 def finiteEquiv (q : HeightOneSpectrum (𝓞 F)) :
    LocalE F ζ hζ (Sum.inr q) ≃* ActualFiniteTorus.H F ζ hζ q :=
  MulEquiv.subgroupCongr (finiteH_eq F ζ hζ q)
private lemma finite_coordinate (q : HeightOneSpectrum (𝓞 F)) (g : LocalE F ζ hζ (Sum.inr q)) :
    ActualFiniteTorus.coordinate F ζ hζ q (finiteEquiv F ζ hζ q g) = localRatio F ζ hζ (Sum.inr q) g := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F q _ : ActualFiniteTorus.K F q) = _
  rw [KPRankOneInduction.borelRatio_eq _ _ _ (diagonalHom F (Sum.inr q) (localRatio F ζ hζ (Sum.inr q) g))]
  · simp [diagonalHom, KubotaRankTwo.d]
  · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) (localRatioValue_spec F ζ hζ (Sum.inr q) g)
  · simp [diagonalHom, KubotaRankTwo.d]
 lemma finite_center_eq (q : HeightOneSpectrum (𝓞 F)) :
    localCenter F ζ hζ (Sum.inr q) = Subgroup.center (LocalE F ζ hζ (Sum.inr q)) := by
  ext x
  have hker := (ActualFiniteTorus.actual_center_cube_normal_form F ζ hζ q).1
  have hcoord := finite_coordinate F ζ hζ q x
  change localProjection F ζ hζ (Sum.inr q) x = 1 ↔ x ∈ Subgroup.center _
  have hp : localProjection F ζ hζ (Sum.inr q) x = ActualFiniteTorus.π F ζ hζ q (finiteEquiv F ζ hζ q x) := by
    change KPGlobalCubicIdelePairing.localClass F (Sum.inr q) (localRatio F ζ hζ (Sum.inr q) x) = QuotientGroup.mk' _ (ActualFiniteTorus.coordinate F ζ hζ q (finiteEquiv F ζ hζ q x))
    rw [hcoord]; rfl
  rw [hp]
  change (finiteEquiv F ζ hζ q x) ∈ (ActualFiniteTorus.π F ζ hζ q).ker ↔ _
  rw [hker, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    exact (finiteEquiv F ζ hζ q).injective (by simpa using h (finiteEquiv F ζ hζ q y))
  · intro h y
    obtain ⟨y,rfl⟩ := (finiteEquiv F ζ hζ q).surjective y
    simpa using congrArg (finiteEquiv F ζ hζ q) (h y)
 def finiteCenterMap (q : HeightOneSpectrum (𝓞 F)) :
    localCenter F ζ hζ (Sum.inr q) →ₜ* ActualFiniteTorus.C F ζ hζ q where
  toFun z := ⟨finiteEquiv F ζ hζ q z.val, by
    have hh : z.val ∈ Subgroup.center (LocalE F ζ hζ (Sum.inr q)) := by rw [← finite_center_eq]; exact z.property
    rw [Subgroup.mem_center_iff] at hh ⊢
    intro y
    obtain ⟨y,rfl⟩ := (finiteEquiv F ζ hζ q).surjective y
    simpa using congrArg (finiteEquiv F ζ hζ q) (hh y)⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

 def finiteOmega (q : HeightOneSpectrum (𝓞 F)) :
    localCenter F ζ hζ (Sum.inr q) →ₜ* ℂˣ :=
  (ActualFiniteTorus.prescribedCenterCharacter F ζ hζ q).comp (finiteCenterMap F ζ hζ q)

private lemma finiteOmega_normal_formula (q : HeightOneSpectrum (𝓞 F))
    (z : localCenter F ζ hζ (Sum.inr q)) (e : rootsOfUnity 3 F)
    (y : (q.adicCompletion F)ˣ)
    (hz : z.val.val = ActualFiniteTorus.normalWord F ζ hζ q e y) :
    finiteOmega F ζ hζ q z = KPGlobalTorusFunctionData.iota F ζ hζ e *
      KPGlobalCenterRationalCharacter.positiveComplex
        (KPGlobalCenterRationalCharacter.sixthPower (Units.mk0
          (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y)
          (ne_of_gt (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q) y)))) := by
  have hs := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2
    e y (finiteEquiv F ζ hζ q z.val) hz
  change ActualFiniteTorus.ordinaryIota F ζ hζ
    (ActualFiniteTorus.sheet F ζ hζ q (finiteEquiv F ζ hζ q z.val)) *
    ActualFiniteTorus.normUnit F q
      (ActualFiniteTorus.coordinate F ζ hζ q (finiteEquiv F ζ hζ q z.val)) = _
  rw [hs.1, hs.2, ← fullnorm_bridgefinite]
  rfl

private lemma local_normal_exists (v : KPHilbert.Place F) (g : LocalE F ζ hζ v) :
    ∃ e, g.val = KPPGLLocalCover.centralInjection F ζ hζ v e *
      KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g) := by
  letI : (KPPGLLocalCover.scalarSubgroup F v).Normal := KPPGLLocalCover.scalarSubgroup_normal F v
  let p := KPPGLLocalCover.projection F ζ hζ v
  have hp : p (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g)) = p g.val := localRatioValue_spec F ζ hζ v g
  have hk : g.val * (KPPGLLocalCover.A F ζ hζ v (localRatio F ζ hζ v g))⁻¹ ∈ p.ker := by
    change p (_ * _) = 1
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rw [show p.ker = (KPPGLLocalCover.centralInjection F ζ hζ v).range from
    (KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ v).symm] at hk
  obtain ⟨e,he⟩ := hk
  exact ⟨e, by rw [he]; simp⟩
private lemma complex_center_eq (w : InfinitePlace F) :
    localCenter F ζ hζ (Sum.inl w) = Subgroup.center (LocalE F ζ hζ (Sum.inl w)) := by
  have htop : localCenter F ζ hζ (Sum.inl w) = ⊤ := by
    ext x
    change localProjection F ζ hζ (Sum.inl w) x = 1 ↔ True
    haveI := KPGlobalCubicIdelePairing.local_complex_trivial F w
    exact iff_of_true (Subsingleton.elim _ _) trivial
  rw [htop]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨e,he⟩ := local_normal_exists F ζ hζ (Sum.inl w) x
    obtain ⟨f,hf⟩ := local_normal_exists F ζ hζ (Sum.inl w) y
    change y.val * x.val = x.val * y.val
    rw [he,hf]
    have zcomm (z : rootsOfUnity 3 F) (a : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w)) :
        Commute (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inl w) z) a :=
      (Subgroup.mem_center_iff.mp (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inl w) ⟨z,rfl⟩) a).symm
    have ac (a b : (KPHilbert.Completion F (Sum.inl w))ˣ) :
        Commute (KPPGLLocalCover.A F ζ hζ (Sum.inl w) a) (KPPGLLocalCover.A F ζ hζ (Sum.inl w) b) := by
      change KPPGLLocalCover.A F ζ hζ (Sum.inl w) a * KPPGLLocalCover.A F ζ hζ (Sum.inl w) b = _
      simp only [KPPGLLocalCover.A_mul]
      simp [KPHilbert.B3, KPHilbert.B6, KPHilbert.squareToThree, mul_comm a b]
    have h1 := zcomm f (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inl w) e)
    have h2 := zcomm f (KPPGLLocalCover.A F ζ hζ (Sum.inl w) (localRatio F ζ hζ (Sum.inl w) x))
    have h3 := (zcomm e (KPPGLLocalCover.A F ζ hζ (Sum.inl w) (localRatio F ζ hζ (Sum.inl w) y))).symm
    have h4 := ac (localRatio F ζ hζ (Sum.inl w) y) (localRatio F ζ hζ (Sum.inl w) x)
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  · exact le_top

theorem local_center_character (v : KPHilbert.Place F) :
    localCenter F ζ hζ v = Subgroup.center (LocalE F ζ hζ v) ∧
    ∃ ω : localCenter F ζ hζ v →ₜ* ℂˣ,
      ∀ (z : localCenter F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v),
        KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val →
        ω z = KPGlobalCenterRationalCharacter.localValue F ζ hζ v g := by
  refine ⟨?_, ?_⟩
  · cases v with
    | inl w => exact complex_center_eq F ζ hζ w
    | inr q => exact finite_center_eq F ζ hζ q
  · cases v with
    | inl w =>
      let S : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inl w)) :=
        (localCenter F ζ hζ (Sum.inl w)).map (localTorus F ζ hζ (Sum.inl w)).subtype
      have hS : ∀ z : S, ∃ y : (KPHilbert.Completion F (Sum.inl w))ˣ,
          KPPGLLocalCover.baseQuotient F (Sum.inl w)
            (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w)) y 1) =
              KPPGLLocalCover.projection F ζ hζ (Sum.inl w) z.val := by
        intro z
        obtain ⟨a, ha, haz⟩ := z.property
        refine ⟨localRatio F ζ hζ (Sum.inl w) a, ?_⟩
        rw [← haz]
        exact localRatioValue_spec F ζ hζ (Sum.inl w) a
      obtain ⟨ω, hω⟩ :=
        ProductPolarizationCharacterDescent.complex_diagonal_subgroup_character
          F ζ hζ w S hS
      let j : localCenter F ζ hζ (Sum.inl w) →ₜ* S := {
        toFun := fun z => ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
        map_one' := by ext; rfl
        map_mul' := by intros; ext; rfl
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact continuous_subtype_val.comp continuous_subtype_val }
      refine ⟨ω.comp j, ?_⟩
      intro z g hg
      obtain ⟨e, he⟩ := local_normal_exists F ζ hζ (Sum.inl w) z.val
      have hc : KPGlobalCubicIdelePairing.localClass F (Sum.inl w)
          (localRatio F ζ hζ (Sum.inl w) z.val) = 1 := z.property
      change ω (j z) = _
      rw [hω (j z) e (localRatio F ζ hζ (Sum.inl w) z.val) he]
      exact (ProductPolarizationCharacterDescent.raw_value_on_cube_normal_word
        F ζ hζ (Sum.inl w) e _ hc g (hg.trans he)).symm
    | inr q =>
      refine ⟨finiteOmega F ζ hζ q, ?_⟩
      intro z g hg
      obtain ⟨e, he⟩ := local_normal_exists F ζ hζ (Sum.inr q) z.val
      have hc : KPGlobalCubicIdelePairing.localClass F (Sum.inr q)
          (localRatio F ζ hζ (Sum.inr q) z.val) = 1 := z.property
      exact (finiteOmega_normal_formula F ζ hζ q z e
        (localRatio F ζ hζ (Sum.inr q) z.val) he).trans
        (ProductPolarizationCharacterDescent.raw_value_on_cube_normal_word
          F ζ hζ (Sum.inr q) e _ hc g (hg.trans he)).symm

theorem exists_local_omega (v : KPHilbert.Place F) :
    ∃ ω : localCenter F ζ hζ v →ₜ* ℂˣ,
      ∀ (z : localCenter F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v),
        KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val →
        ω z = KPGlobalCenterRationalCharacter.localValue F ζ hζ v g :=
  (local_center_character F ζ hζ v).2

def localOmega (v : KPHilbert.Place F) : localCenter F ζ hζ v →ₜ* ℂˣ :=
  Classical.choose (exists_local_omega F ζ hζ v)

theorem localOmega_raw_formula (v : KPHilbert.Place F)
    (z : localCenter F ζ hζ v) (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg : KPPGLLocalCover.coverQuotient F ζ hζ v g = z.val.val) :
    localOmega F ζ hζ v z = KPGlobalCenterRationalCharacter.localValue F ζ hζ v g :=
  Classical.choose_spec (exists_local_omega F ζ hζ v) z g hg

def IsMaximalIsotropic {G : Type*} [CommGroup G]
    (b : G → G → rootsOfUnity 3 F) (L : Subgroup G) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, b x y = 1) ∧
    ∀ N : Subgroup G, L ≤ N → (∀ x ∈ N, ∀ y ∈ N, b x y = 1) → N = L

def localPreimage (v : KPHilbert.Place F) (L : Subgroup (LocalD F v)) :
    Subgroup (LocalE F ζ hζ v) := L.comap (localProjection F ζ hζ v)

end
end DedekindZetaZeroFree.ProductPolarization

end
