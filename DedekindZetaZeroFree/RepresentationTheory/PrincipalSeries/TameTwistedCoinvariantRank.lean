module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInductionAndBorelRetraction
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellTestVector
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProjectorGermsAndFrequencySupport
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TwistedOpenCellIsomorphism
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TorusEquivariantQuotient

@[expose] public section

open scoped NumberField Valued NNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
variable (S : RawFiniteInducingData F ζ hζ q)

local instance ambientPlusAddCommGroup (P : Polarization S.heisenberg) :
    AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance

namespace StandardPlusAux
open KPLocalSmoothRepresentation
variable (P : Polarization S.heisenberg)

 abbrev depth := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
 abbrev hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
 def bEq : S.borel.B ≃* Borel F ζ hζ q :=
  MulEquiv.subgroupCongr S.borel_eq
 def rawAction := (inducingAction S.borel P .plus 0).comp
  (bEq F ζ hζ q S).symm.toMonoidHom
 def invHalf : Borel F ζ hζ q →* ℂˣ where
  toFun b := Units.mk0 ((((dB F ζ hζ q b : ℝ≥0) : ℝ) : ℂ)⁻¹)
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))))
  map_one' := by apply Units.ext; simp only [map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one, inv_one, Units.val_mk0]
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mk0, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_inv]
 def unnormalized : Representation ℂ (Borel F ζ hζ q) (InducedModule P) where
  toFun b := (invHalf F ζ hζ q b : ℂ) • rawAction F ζ hζ q S P b
  map_one' := by rw [map_one, Units.val_one, one_smul, map_one]
  map_mul' a b := by
    rw [map_mul, Units.val_mul, map_mul]
    ext v : 1
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    congr 1
    ring
 def torusAction := (unnormalized F ζ hζ q S P).comp
  (KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ q
    (depth F ζ hζ q) (hm F ζ hζ q))
private theorem raw_root (x : Multiplicative (LocalField F q)) :
    rawAction F ζ hζ q S P (KPJacquetTwistedCell.rootToBorel F ζ hζ q x) = 1 := by
  have hx : (bEq F ζ hζ q S).symm (KPJacquetTwistedCell.rootToBorel F ζ hζ q x) =
      S.borel.upperRoot x := by
    apply Subtype.ext
    exact ((S.openCell P).upper_eq (Multiplicative.toAdd x)).symm
  ext v : 1
  change inducingAction S.borel P .plus 0
    ((bEq F ζ hζ q S).symm (KPJacquetTwistedCell.rootToBorel F ζ hζ q x)) v = v
  rw [hx]
  exact upperRoot_trivial S.borel P .plus 0 x v
 theorem norm_action (b : Borel F ζ hζ q) (v : InducedModule P) :
    KPJacquetClosedCellBump.inducingRepresentation F ζ hζ q
      (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q
        (torusAction F ζ hζ q S P)) b v = rawAction F ζ hζ q S P b v := by
  obtain ⟨x, hx⟩ := KPLocalInductionJacquetReciprocity.borelRetraction_decomposition F ζ hζ q b
  let t := KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ q
    (depth F ζ hζ q) (hm F ζ hζ q)
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ q b)
  have hb : b = t * KPJacquetTwistedCell.rootToBorel F ζ hζ q x := Subtype.ext hx
  have hr : rawAction F ζ hζ q S P b = rawAction F ζ hζ q S P t := by
    rw [hb, map_mul, raw_root, mul_one]
  have hd := KPLocalInductionJacquetReciprocity.dB_retraction F ζ hζ q
    (depth F ζ hζ q) (hm F ζ hζ q) b
  change ((((dB F ζ hζ q b : ℝ≥0) : ℝ) : ℂ)) •
    ((invHalf F ζ hζ q t : ℂ) • rawAction F ζ hζ q S P t v) = _
  rw [smul_smul, hr]
  have hi : (invHalf F ζ hζ q t : ℂ) =
      ((((dB F ζ hζ q b : ℝ≥0) : ℝ) : ℂ)⁻¹) := by
    change ((((dB F ζ hζ q t : ℝ≥0) : ℝ) : ℂ)⁻¹) = _
    rw [show dB F ζ hζ q t = dB F ζ hζ q b from hd]
  rw [hi, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (Units.ne_zero _))), one_smul]
private theorem scalar_lc : IsLocallyConstant (fun b : S.borel.B =>
    inducingScalar S.borel 0 b) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro b
  have hv := (valuation (LocalField F q)).locally_const
    ((Valuation.ne_zero_iff _).mpr (Units.ne_zero (S.borel.coordinate (S.borel.retract b))))
  have hc := Units.continuous_val.comp (S.borel.coordinate_continuous.comp S.borel.retract_continuous)
  filter_upwards [hc.continuousAt.tendsto.eventually hv] with a ha
  change valuation (LocalField F q) (S.borel.coordinate (S.borel.retract a) : LocalField F q) = _ at ha
  simp only [inducingScalar, deltaHalf, normPower, localAbs, ha]
private theorem raw_smooth : SmoothRepresentation (rawAction F ζ hζ q S P) := by
  have hs : SmoothRepresentation (inducingAction S.borel P .plus 0) := by
    intro v
    obtain ⟨J, hJ⟩ := tau_smooth S.heisenberg P v
    let r := S.borel.retract
    have hscalar : IsOpen {b : S.borel.B | inducingScalar S.borel 0 b = 1} :=
      (scalar_lc F ζ hζ q S).isOpen_fiber 1
    let K : Subgroup S.borel.B := (inducingAction S.borel P .plus 0).stabilizer v
    have hopen : IsOpen (K : Set S.borel.B) := by
      apply isOpen_iff_mem_nhds.mpr
      intro b hb
      have hnear : ∀ᶠ a in nhds (1 : S.borel.B), inducingScalar S.borel 0 a = 1 ∧
          r a ∈ J := by
        have h1 : inducingScalar S.borel 0 (1 : S.borel.B) = 1 := by
          simp [inducingScalar, deltaHalf, normPower, localAbs_one]
        exact Filter.Eventually.and (hscalar.mem_nhds h1)
          ((J.isOpen.preimage S.borel.retract_continuous).mem_nhds (by simp [r]))
      have ht : ContinuousAt (fun a : S.borel.B => b⁻¹ * a) b :=
        (continuous_const.mul continuous_id).continuousAt
      have hz : (fun a : S.borel.B => b⁻¹ * a) b = 1 := inv_mul_cancel b
      have he := ht.tendsto.eventually (hz ▸ hnear)
      filter_upwards [he] with a ha
      have hfix : inducingAction S.borel P .plus 0 (b⁻¹ * a) v = v := by
        change inducingScalar S.borel 0 (b⁻¹ * a) • tau P (r (b⁻¹ * a)) v = v
        rw [ha.1, hJ _ ha.2, one_smul]
      change inducingAction S.borel P .plus 0 a v = v
      have heq : a = b * (b⁻¹ * a) := by simp
      rw [heq, map_mul, Module.End.mul_apply, hfix]
      exact hb
    exact ⟨⟨K, hopen⟩, fun a ha => ha⟩
  intro v
  obtain ⟨J, hJ⟩ := hs v
  have hc : Continuous (bEq F ζ hζ q S).symm := by
    exact continuous_subtype_val.subtype_mk _
  exact ⟨J.comap (bEq F ζ hζ q S).symm.toMonoidHom hc, fun a ha => hJ _ ha⟩
private theorem torus_smooth : SmoothRepresentation (torusAction F ζ hζ q S P) := by
  have hu : SmoothRepresentation (unnormalized F ζ hζ q S P) := by
    have hp : Continuous (projection F ζ hζ q) := by
      have ho : Continuous (ordinaryPGLMap F q) := by
        apply (QuotientGroup.isQuotientMap_mk (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))).continuous_iff.mpr
        change Continuous (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := LocalField F q))
        exact (QuotientGroup.isQuotientMap_mk _).continuous
      exact ho.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ q
        (depth F ζ hζ q) (hm F ζ hζ q)).2.2.2.1.continuous
    have hd := KPRankOneInduction.dB_locallyConstant F q (projection F ζ hζ q) hp
    let D : OpenSubgroup (Borel F ζ hζ q) := ⟨(dB F ζ hζ q).ker, hd.isOpen_fiber 1⟩
    intro v
    obtain ⟨J, hJ⟩ := raw_smooth F ζ hζ q S P v
    refine ⟨J ⊓ D, ?_⟩
    intro b hb
    change (invHalf F ζ hζ q b : ℂ) • rawAction F ζ hζ q S P b v = v
    have hi : (invHalf F ζ hζ q b : ℂ) = 1 := by
      change ((((dB F ζ hζ q b : ℝ≥0) : ℝ) : ℂ)⁻¹) = 1
      rw [show dB F ζ hζ q b = 1 from hb.2]
      simp only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, inv_one]
    rw [hi, hJ _ hb.1, one_smul]
  intro v
  obtain ⟨J, hJ⟩ := hu v
  exact ⟨J.comap _ (continuous_subtype_val.subtype_mk _), fun a ha => hJ _ ha⟩
 abbrev actualInd := Induced F ζ hζ q (depth F ζ hζ q)
  (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q (torusAction F ζ hζ q S P))
local instance actualAdd : AddCommGroup (actualInd F ζ hζ q S P) := by
  letI : AddCommGroup (EqSections (Borel F ζ hζ q)
    (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q (torusAction F ζ hζ q S P))
    (dB F ζ hζ q)) := Submodule.addCommGroup _
  exact Submodule.addCommGroup _
 def toRaw : actualInd F ζ hζ q S P →ₗ[ℂ] sectionSpace S.borel P .plus 0 where
  toFun f := ⟨f.val.val, by
    constructor
    · intro b g
      have h := f.val.property ((bEq F ζ hζ q S) b) g
      change f.val.val ((b : ActualCover F ζ hζ q) * g) = _ at h
      rw [show normalizedSectionRepresentation _ _ _ ((bEq F ζ hζ q S) b)
        (f.val.val g) = rawAction F ζ hζ q S P ((bEq F ζ hζ q S) b) (f.val.val g)
        from norm_action F ζ hζ q S P _ _] at h
      exact h
    · obtain ⟨J, hJ⟩ := (mem_smoothSubmodule _ _).mp f.property
      refine ⟨J, ?_⟩
      intro a ha
      funext g
      exact congrArg (fun f => f.val g) (hJ a ha)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
private theorem toRaw_surjective : Function.Surjective (toRaw F ζ hζ q S P) := by
  intro f
  let f₀ : EqSections (Borel F ζ hζ q)
      (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q (torusAction F ζ hζ q S P))
      (dB F ζ hζ q) := ⟨f.val, by
        intro b g
        rw [show normalizedSectionRepresentation _ _ _ b (f.val g) =
          rawAction F ζ hζ q S P b (f.val g) from norm_action F ζ hζ q S P _ _]
        exact f.property.1 ((bEq F ζ hζ q S).symm b) g⟩
  have hf₀ : f₀ ∈ SmoothInd _ _ _ := by
    apply (mem_smoothSubmodule _ _).mpr
    obtain ⟨J, hJ⟩ := f.property.2
    refine ⟨J, ?_⟩
    intro a ha
    apply Subtype.ext
    exact hJ a ha
  exact ⟨⟨f₀, hf₀⟩, rfl⟩
 def toRawIntertwiner :
    (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ q
      (depth F ζ hζ q) (hm F ζ hζ q)
      (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q (torusAction F ζ hζ q S P))).IntertwiningMap
    (IPlus S.borel P) where
  toLinearMap := toRaw F ζ hζ q S P
  isIntertwining' g := by ext f x; rfl
end StandardPlusAux

private theorem continuous_circleToUnits : Continuous (Circle.toUnits : Circle → ℂˣ) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (fun z : Circle => (z : ℂ))
    exact continuous_subtype_val
  · have : (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ)) =
        fun z : Circle => ((z : ℂ))⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    rw [this]
    exact continuous_subtype_val.inv₀ (fun z => Circle.coe_ne_zero z)

private theorem circleToUnits_injective : Function.Injective (Circle.toUnits : Circle → ℂˣ) :=
  fun a b hab => Subtype.ext (by
    simpa [Circle.toUnits_apply] using congrArg (fun u : ℂˣ => (u : ℂ)) hab)

private theorem frequencyCharacter_continuous_nontrivial :
    Continuous ⇑(KPKirillovProjectorGerms.frequencyCharacter F q 1) ∧
      KPKirillovProjectorGerms.frequencyCharacter F q 1 ≠ 1 := by
  refine ⟨?_, ?_⟩
  · exact continuous_circleToUnits.comp ((continuous_localFiniteCharacter F q).comp
      (continuous_const.mul (continuous_toAdd (X := LocalField F q))))
  · intro h
    have hx : ∀ y : LocalField F q, localFiniteCharacter F q ((1 : LocalField F q) * y) = 1 := by
      intro y
      have hy := congrArg (fun χ : Multiplicative (LocalField F q) →* ℂˣ =>
        χ (Multiplicative.ofAdd y)) h
      simp only [MonoidHom.one_apply] at hy
      exact circleToUnits_injective (by rw [map_one]; exact hy)
    exact one_ne_zero ((localFiniteCharacter_nondegenerate F q 1).mp hx)

theorem standard_plus_coinvariant_rank_le_three
    (P : Polarization S.heisenberg)
    (hroot : ∃ ξ : LocalField F q, IsPrimitiveRoot ξ 12)
    (ht : ringChar (IsLocalRing.ResidueField
      (valuation (LocalField F q)).integer) ≠ 3) :
    Module.rank ℂ (RootCoinvariants (IPlus S.borel P)
      (KPLocalJacquetImage.root S.borel)
      (KPKirillovProjectorGerms.frequencyCharacter F q 1)) ≤ 3 := by
  obtain ⟨hψc, hψne⟩ := frequencyCharacter_continuous_nontrivial F q
  have hr : KPLocalJacquetImage.root S.borel =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ q := by
    ext x
    exact (S.openCell P).upper_eq (Multiplicative.toAdd x)
  haveI : Module.Finite ℂ (InducedModule P) :=
    (finite_heisenberg_induction S.heisenberg P).1
  obtain ⟨e⟩ := KPJacquetTwistedCell.nonempty_coefficient_equiv F ζ hζ q
    (StandardPlusAux.depth F ζ hζ q) (StandardPlusAux.hm F ζ hζ q)
    (StandardPlusAux.torusAction F ζ hζ q S P)
    (StandardPlusAux.torus_smooth F ζ hζ q S P)
    (KPKirillovProjectorGerms.frequencyCharacter F q 1) hψc hψne
  letI : AddCommGroup (StandardPlusAux.actualInd F ζ hζ q S P) :=
    StandardPlusAux.actualAdd F ζ hζ q S P
  have hY : Module.rank ℂ (RootCoinvariants
      (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ q
        (StandardPlusAux.depth F ζ hζ q) (StandardPlusAux.hm F ζ hζ q)
        (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q
          (StandardPlusAux.torusAction F ζ hζ q S P)))
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
      (KPKirillovProjectorGerms.frequencyCharacter F q 1)) =
      (3 : Cardinal) := by
    haveI : Module.Finite ℂ (RootCoinvariants
      (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ q
        (StandardPlusAux.depth F ζ hζ q) (StandardPlusAux.hm F ζ hζ q)
        (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q
          (StandardPlusAux.torusAction F ζ hζ q S P)))
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
      (KPKirillovProjectorGerms.frequencyCharacter F q 1)) := e.symm.finiteDimensional
    rw [← Module.finrank_eq_rank]
    rw [e.finrank_eq]
    obtain ⟨ξ, hξ⟩ := hroot
    let ζ3 : LocalField F q := ξ ^ 4
    have hζ3 : IsPrimitiveRoot ζ3 3 := by
      have h := hξ.pow_of_dvd (p := 4) (by norm_num) (by norm_num)
      simpa [ζ3] using h
    have htame : (3 : (valuation (LocalField F q)).integer) ∉
        IsLocalRing.maximalIdeal ((valuation (LocalField F q)).integer) := by
      intro hmem
      apply ht
      have h0 : (3 : IsLocalRing.ResidueField (valuation (LocalField F q)).integer) = 0 := by
        change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
          (valuation (LocalField F q)).integer)
          (3 : (valuation (LocalField F q)).integer)) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      exact CharP.ringChar_of_prime_eq_zero Nat.prime_three h0
    rw [(finite_heisenberg_induction S.heisenberg P).2.2.2.2.2,
      Nat.card_congr S.cubeClassEquiv.toEquiv,
      KPLocalTorus.card_cubeClasses_tame (LocalField F q) ζ3 hζ3 htame]
    norm_num
  have hsurj : Function.Surjective (rootCoinvariantsMap
      (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ q
        (StandardPlusAux.depth F ζ hζ q) (StandardPlusAux.hm F ζ hζ q)
        (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q
          (StandardPlusAux.torusAction F ζ hζ q S P)))
      (IPlus S.borel P) (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
      (KPKirillovProjectorGerms.frequencyCharacter F q 1)
      (StandardPlusAux.toRawIntertwiner F ζ hζ q S P)) := by
    intro w
    obtain ⟨v, rfl⟩ := rootCoinvariantsMk_surjective _ _ _ w
    obtain ⟨u, rfl⟩ := StandardPlusAux.toRaw_surjective F ζ hζ q S P v
    exact ⟨rootCoinvariantsMk _ _ _ u,
      LinearMap.congr_fun (rootCoinvariantsMap_comp_mk _ _ _ _ _) u⟩
  calc Module.rank ℂ (RootCoinvariants (IPlus S.borel P)
        (KPLocalJacquetImage.root S.borel)
        (KPKirillovProjectorGerms.frequencyCharacter F q 1))
      = Module.rank ℂ (RootCoinvariants (IPlus S.borel P)
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
        (KPKirillovProjectorGerms.frequencyCharacter F q 1)) := by rw [hr]
    _ ≤ Module.rank ℂ (RootCoinvariants
        (KPJacquetClosedCellBump.inducedRepresentation F ζ hζ q
          (StandardPlusAux.depth F ζ hζ q) (StandardPlusAux.hm F ζ hζ q)
          (KPJacquetTwistedCell.coefficientRepresentation F ζ hζ q
            (StandardPlusAux.torusAction F ζ hζ q S P)))
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
        (KPKirillovProjectorGerms.frequencyCharacter F q 1)) :=
        LinearMap.rank_le_of_surjective _ hsurj
    _ = (3 : Cardinal) := hY

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.Uniqueness
