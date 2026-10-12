module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.GaussianSmoothing
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
open MomentSources ThetaProfileHaarSheets

 def castMeasure {X : Type*} {m n : MeasurableSpace X} (h : m = n)
    (μ : @Measure X m) : @Measure X n := h ▸ μ

private theorem castMeasure_haar {X : Type*} [Group X] [TopologicalSpace X]
    {m n : MeasurableSpace X} (h : m = n) (μ : @Measure X m)
    (hμ : @Measure.IsHaarMeasure X _ _ m μ) :
    @Measure.IsHaarMeasure X _ _ n (castMeasure h μ) := by
  subst n
  exact hμ

def probeHaar (R : PrincipalMellin.ActualRecipe S η) : Measure R.A.G1 :=
  castMeasure (BorelSpace.measurable_eq (α := R.A.G1)).symm R.probe.domain.measure

theorem probeHaar_isHaar (R : PrincipalMellin.ActualRecipe S η) :
    (probeHaar R).IsHaarMeasure :=
  castMeasure_haar _ _ R.probe.domain.haar

private theorem map_prod_cast {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {m n : MeasurableSpace Y} (h : m = n) (μ : Measure X) (ν : @Measure Y m)
    (e : X × Y → Z) :
    @Measure.map _ _ (@Prod.instMeasurableSpace _ _ _ n) _ e
      (@Measure.prod X Y _ n μ (castMeasure h ν)) =
    @Measure.map _ _ (@Prod.instMeasurableSpace _ _ _ m) _ e
      (@Measure.prod X Y _ m μ ν) := by
  subst n
  rfl

private theorem integral_cast {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : MeasurableSpace X} (h : m = n) (μ : @Measure X m) (f : X → E) :
    @integral X E _ _ n (castMeasure h μ) f = @integral X E _ _ m μ f := by
  subst n
  rfl

private theorem integrable_cast {X E : Type*} [NormedAddCommGroup E]
    {m n : MeasurableSpace X} (h : m = n) (μ : @Measure X m) (f : X → E) :
    @Integrable E _ _ X n f (castMeasure h μ) ↔ @Integrable E _ _ X m f μ := by
  subst n
  rfl

theorem probeHaar_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : R.A.G1 → E) :
    (∫ z, f z ∂probeHaar R) =
      @integral R.A.G1 E _ _ (borel _) R.probe.domain.measure f :=
  integral_cast _ _ _

theorem probeHaar_integrable {E : Type*} [NormedAddCommGroup E] (f : R.A.G1 → E) :
    Integrable f (probeHaar R) ↔
      @Integrable E _ _ R.A.G1 (borel _) f R.probe.domain.measure :=
  integrable_cast _ _ _

theorem kernelHaar_eq_probe (N : TraceHaarTransport R) (w : InfinitePlace F) :
    letI := N.groupHaar_isHaar
    kernelHaar R.A w N.groupHaar = probeHaar R := by
  letI := N.groupHaar_isHaar
  apply (exists_unique_kernelHaar R.A w N.groupHaar).unique
  · exact ⟨kernelHaar_isHaarMeasure R.A w N.groupHaar,
      map_product_kernelHaar R.A w N.groupHaar⟩
  · refine ⟨probeHaar_isHaar R, ?_⟩
    exact (map_prod_cast _ _ _ _).trans (N.disintegration w)

def sectionRatio (A : SArithmeticData F) (w : InfinitePlace F) (x : PositiveAxis) : A.G1 :=
  ⟨normSection A w x / A.radialSection x.val x.property, by
    change A.norm _ = 1
    have hdiv (a b : A.G) : A.norm (a / b) = A.norm a / A.norm b := by
      simp [SArithmeticData.norm, norm_div, div_pow, Finset.prod_div_distrib,
        mul_div_mul_comm]
    rw [hdiv, norm_normSection, A.norm_radialSection, div_self x.property.ne']⟩

theorem integrable_uniform_iff (N : TraceHaarTransport R) (w : InfinitePlace F)
    (x : PositiveAxis) (f : R.A.G → ℝ) :
    Integrable (fun z : R.A.G1 => f (normSection R.A w x * z.val)) (probeHaar R) ↔
    Integrable (fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))
      (probeHaar R) := by
  letI := probeHaar_isHaar R
  let q := sectionRatio R.A w x
  have h (z : R.A.G1) : normSection R.A w x * z.val =
      (q * z).val * R.A.radialSection x.val x.property := by
    change _ = (normSection R.A w x / R.A.radialSection x.val x.property * z.val) * _
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [h]
  exact (measurePreserving_mul_left (probeHaar R) q).integrable_comp_emb
    (Homeomorph.mulLeft q).measurableEmbedding
    (g := fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property))

theorem integral_uniform_eq (N : TraceHaarTransport R) (w : InfinitePlace F)
    (x : PositiveAxis) (f : R.A.G → ℝ)
    (_hf : Integrable (fun z : R.A.G1 => f (normSection R.A w x * z.val)) (probeHaar R)) :
    (∫ z : R.A.G1, f (normSection R.A w x * z.val) ∂(probeHaar R)) =
    ∫ z : R.A.G1, f (z.val * R.A.radialSection x.val x.property) ∂(probeHaar R) := by
  letI := probeHaar_isHaar R
  let q := sectionRatio R.A w x
  have h (z : R.A.G1) : normSection R.A w x * z.val =
      (q * z).val * R.A.radialSection x.val x.property := by
    change _ = (normSection R.A w x / R.A.radialSection x.val x.property * z.val) * _
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [h]
  exact integral_mul_left_eq_self (μ := probeHaar R)
    (fun z : R.A.G1 => f (z.val * R.A.radialSection x.val x.property)) q
end DedekindZetaZeroFree.GaussianSmoothing

end
