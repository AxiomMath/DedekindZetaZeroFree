module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxis
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces

@[expose] public section

open NumberField
namespace DedekindZetaZeroFree.NormSheetsCoordinates
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
abbrev Axis := NormSheetsPositiveAxis.Axis

def sqrtUnit (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : Axis) : v₀.Completionˣ :=
  Units.map
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (A.complex_place v₀)).symm.toMonoidHom
    (Units.mk0 (Real.sqrt (x : ℝ) : ℂ) (by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 x.property))))

def normSectionRaw (A : SArithmeticData F) (v₀ : InfinitePlace F) (x : Axis) : A.G :=
  (Pi.mulSingle v₀ (sqrtUnit A v₀ x), 1)

theorem section_at_place (A : SArithmeticData F) (v₀ : InfinitePlace F) (x : Axis) :
    InfinitePlace.Completion.extensionEmbedding v₀
      ((normSectionRaw A v₀ x).1 v₀ : v₀.Completion) = (Real.sqrt (x : ℝ) : ℂ) := by
  simp only [normSectionRaw, Pi.mulSingle_eq_same]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v₀))
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (A.complex_place v₀)).symm (Real.sqrt (x : ℝ) : ℂ)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem section_at_other_place (A : SArithmeticData F)
    (v₀ v : InfinitePlace F) (hv : v ≠ v₀) (x : Axis) :
    (normSectionRaw A v₀ x).1 v = 1 := by
  simp [normSectionRaw, Pi.mulSingle_eq_of_ne hv]

theorem norm_mul (A : SArithmeticData F) (y z : A.G) :
    A.norm (y * z) = A.norm y * A.norm z := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, _root_.norm_mul, mul_pow, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem norm_inv (A : SArithmeticData F) (y : A.G) :
    A.norm y⁻¹ = (A.norm y)⁻¹ := by
  simp [SArithmeticData.norm, _root_.norm_inv, inv_pow, Finset.prod_inv_distrib,
    mul_inv, mul_comm]

theorem norm_positive (A : SArithmeticData F) (y : A.G) : 0 < A.norm y := by
  unfold SArithmeticData.norm
  apply mul_pos
  · exact Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr (y.1 v).ne_zero) _
  · exact Finset.prod_pos fun v _ => norm_pos_iff.mpr (y.2 v).ne_zero

private theorem continuous_norm_raw (A : SArithmeticData F) : Continuous A.norm := by
  unfold SArithmeticData.norm
  fun_prop

theorem section_laws (A : SArithmeticData F) (v₀ : InfinitePlace F) :
    (∀ x : Axis, A.norm (normSectionRaw A v₀ x) = (x : ℝ)) ∧
    (∀ x y : Axis, normSectionRaw A v₀ (x * y) = normSectionRaw A v₀ x * normSectionRaw A v₀ y) ∧
    Continuous (normSectionRaw A v₀) ∧ Continuous A.norm := by
  refine ⟨?_, ?_, ?_, continuous_norm_raw A⟩
  · intro x
    have hs : ‖(sqrtUnit A v₀ x : v₀.Completion)‖ ^ 2 = (x : ℝ) := by
      rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v₀).norm_map_of_map_zero
        (map_zero _) (sqrtUnit A v₀ x : v₀.Completion),
        show InfinitePlace.Completion.extensionEmbedding v₀ (sqrtUnit A v₀ x : v₀.Completion) =
          (Real.sqrt (x : ℝ) : ℂ) by simpa [normSectionRaw] using section_at_place A v₀ x,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (le_of_lt x.property)]
    unfold SArithmeticData.norm
    simp only [normSectionRaw, Pi.one_apply, Units.val_one, norm_one, Finset.prod_const_one,
      mul_one]
    rw [Finset.prod_eq_single v₀]
    · simpa using hs
    · intro v _ hv
      simp [Pi.mulSingle_eq_of_ne hv]
    · simp
  · intro x y
    apply Prod.ext
    · funext v
      by_cases hv : v = v₀
      · subst v
        simp only [normSectionRaw, Pi.mulSingle_eq_same, Pi.mul_apply]
        apply Units.ext
        apply (InfinitePlace.Completion.extensionEmbedding v₀).injective
        simp only [Prod.fst_mul, Pi.mul_apply, Pi.mulSingle_eq_same, Units.val_mul, map_mul]
        have he (t : Axis) : InfinitePlace.Completion.extensionEmbedding v₀
            (sqrtUnit A v₀ t : v₀.Completion) = (Real.sqrt (t : ℝ) : ℂ) := by
          simpa [normSectionRaw] using section_at_place A v₀ t
        rw [he, he, he]
        change (Real.sqrt ((x : ℝ) * (y : ℝ)) : ℂ) =
          (Real.sqrt (x : ℝ) : ℂ) * (Real.sqrt (y : ℝ) : ℂ)
        rw [Real.sqrt_mul (le_of_lt x.property), Complex.ofReal_mul]
      · simp [normSectionRaw, Pi.mulSingle_eq_of_ne hv]
    · simp [normSectionRaw]
  · have hu : Continuous (sqrtUnit A v₀) := by
      apply Units.continuous_iff.mpr
      have hc : Continuous (fun x : Axis =>
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (A.complex_place v₀)).symm
            (Real.sqrt (x : ℝ) : ℂ)) :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (A.complex_place v₀)).symm.continuous.comp
          (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_subtype_val))
      refine ⟨hc, ?_⟩
      simp only [Units.val_inv_eq_inv_val]
      have hc' : Continuous (fun x : Axis => (sqrtUnit A v₀ x : v₀.Completion)) := hc
      exact hc'.inv₀ (fun x => (sqrtUnit A v₀ x).ne_zero)
    exact (continuous_mulSingle v₀ |>.comp hu).prodMk continuous_const

theorem normOne_geometry (A : SArithmeticData F) :
    LocallyCompactSpace A.G1 ∧ SecondCountableTopology A.G1 := by
  letI (v : A.Sf) : LocallyCompactSpace (v.val.adicCompletion F) := by
    letI : LocallyCompactSpace (NumberField.HeightOneSpectrum.adicAbv F v.val).Completion :=
      AbsoluteValue.Completion.locallyCompactSpace (finitePlaceCompletionBaseMap_isometry v.val)
    exact (finitePlaceCompletionContinuousMulEquiv v.val).toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace A.G := inferInstance
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : A.Sf) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F) := inferInstance
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  letI (v : A.Sf) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology A.G := inferInstance
  exact ⟨IsClosed.locallyCompactSpace (isClosed_singleton.preimage (continuous_norm_raw A)),
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

theorem inverse_section_mem (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (x : Axis) (y : A.G) (hy : A.norm y = (x : ℝ)) :
    (normSectionRaw A v₀ x)⁻¹ * y ∈ A.G1 := by
  change A.norm ((normSectionRaw A v₀ x)⁻¹ * y) = 1
  rw [norm_mul, norm_inv, (section_laws A v₀).1, hy,
    inv_mul_cancel₀ (ne_of_gt x.property)]

def split (A : SArithmeticData F) (v₀ : InfinitePlace F) : (Axis × A.G1) ≃ₜ* A.G where
  toFun p := normSectionRaw A v₀ p.1 * p.2.val
  invFun y := (⟨A.norm y, norm_positive A y⟩,
    ⟨(normSectionRaw A v₀ ⟨A.norm y, norm_positive A y⟩)⁻¹ * y,
      inverse_section_mem A v₀ _ y rfl⟩)
  left_inv := by
    intro p
    have hn : A.norm (normSectionRaw A v₀ p.1 * p.2.val) = (p.1 : ℝ) := by
      rw [norm_mul, (section_laws A v₀).1, p.2.property, mul_one]
    apply Prod.ext
    · exact Subtype.ext hn
    · apply Subtype.ext
      simp only
      have hx : (⟨A.norm (normSectionRaw A v₀ p.1 * p.2.val),
        norm_positive A (normSectionRaw A v₀ p.1 * p.2.val)⟩ : Axis) = p.1 := Subtype.ext hn
      rw [hx, inv_mul_cancel_left]
  right_inv := by
    intro y
    exact mul_inv_cancel_left _ y
  map_mul' := by
    intro p q
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [(section_laws A v₀).2.1]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun :=
    ((section_laws A v₀).2.2.1.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hn := (section_laws A v₀).2.2.2.subtype_mk (norm_positive A)
    exact hn.prodMk (((section_laws A v₀).2.2.1.comp hn).inv.mul continuous_id |>.subtype_mk _)

abbrev Fiber (A : SArithmeticData F) (x : Axis) := {y : A.G // A.norm y = (x : ℝ)}

def translation (A : SArithmeticData F) (v₀ : InfinitePlace F) (x : Axis) :
    A.G1 ≃ₜ Fiber A x where
  toFun z := ⟨normSectionRaw A v₀ x * z.val, by
    rw [norm_mul, (section_laws A v₀).1, z.property, mul_one]⟩
  invFun y := ⟨(normSectionRaw A v₀ x)⁻¹ * y.val,
    inverse_section_mem A v₀ x y.val y.property⟩
  left_inv := by intro z; apply Subtype.ext; exact inv_mul_cancel_left _ _
  right_inv := by intro y; apply Subtype.ext; exact mul_inv_cancel_left _ _
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val : Continuous (fun z : A.G1 => z.val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val : Continuous (fun y : Fiber A x => y.val))

end
end DedekindZetaZeroFree.NormSheetsCoordinates
