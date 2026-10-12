module

public import DedekindZetaZeroFree.Adeles.Haar.FiniteRestrictedProductMeasure
public import DedekindZetaZeroFree.Adeles.Lattices.AdditiveFundamentalDomain

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPAdditiveRationalDilation

variable (F : Type) [Field F] [NumberField F]

def dilation (t : Fˣ) (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F :=
  algebraMap F (AdeleRing (𝓞 F) F) (t : F) * x

theorem dilation_inverse (t : Fˣ) :
    Function.LeftInverse (dilation F t⁻¹) (dilation F t) ∧
    Function.RightInverse (dilation F t⁻¹) (dilation F t) := by
  constructor <;> intro x <;> simp [dilation, ← mul_assoc, ← map_mul]

theorem dilation_diagonal (t : Fˣ) (a : F) :
    dilation F t (algebraMap F (AdeleRing (𝓞 F) F) a) =
      algebraMap F (AdeleRing (𝓞 F) F) ((t : F) * a) := by
  exact (map_mul (algebraMap F (AdeleRing (𝓞 F) F)) _ _).symm

theorem dilation_principal_image (t : Fˣ) :
    dilation F t '' (AdeleRing.principalSubgroup (𝓞 F) F : Set _) =
      (AdeleRing.principalSubgroup (𝓞 F) F : Set _) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨(t : F) * a, (dilation_diagonal F t a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) ((↑t⁻¹ : F) * a),
      ⟨(↑t⁻¹ : F) * a, rfl⟩, ?_⟩
    rw [dilation_diagonal]
    simp [← mul_assoc]

def dilationHom (t : Fˣ) : AdeleRing (𝓞 F) F →+ AdeleRing (𝓞 F) F where
  toFun := dilation F t
  map_zero' := by exact mul_zero _
  map_add' := by intro x y; exact mul_add _ _ _

def quotientDilation (t : Fˣ) :
    (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) →+
      (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  QuotientAddGroup.map _ _ (dilationHom F t) (by
    intro x hx
    change dilation F t x ∈ AdeleRing.principalSubgroup (𝓞 F) F
    change dilation F t x ∈ (AdeleRing.principalSubgroup (𝓞 F) F : Set _)
    rw [← dilation_principal_image F t]
    exact Set.mem_image_of_mem _ hx)

theorem quotientDilation_is_additive_homeomorphism (t : Fˣ) :
    ∃ e : (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ≃ₜ+
        (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F),
      ∀ q, e q = quotientDilation F t q := by
  have hcont (u : Fˣ) : Continuous (quotientDilation F u) := by
    apply (QuotientAddGroup.isQuotientMap_mk
      (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
    change Continuous (fun x => QuotientAddGroup.mk
      (dilation F u x))
    exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
  have hinv (u : Fˣ) : Function.LeftInverse
      (quotientDilation F u⁻¹) (quotientDilation F u) := by
    intro x
    induction x using Quotient.inductionOn with
    | h x =>
      change QuotientAddGroup.mk (dilation F u⁻¹ (dilation F u x)) = QuotientAddGroup.mk x
      rw [(dilation_inverse F u).1 x]
  refine ⟨{
    toFun := quotientDilation F t
    invFun := quotientDilation F t⁻¹
    left_inv := hinv t
    right_inv := ?_
    map_add' := (quotientDilation F t).map_add
    continuous_toFun := hcont t
    continuous_invFun := hcont t⁻¹ }, fun _ => rfl⟩
  intro x
  simpa only [inv_inv] using hinv t⁻¹ x

local instance quotientMeasurable :
    MeasurableSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) :=
  borel _

theorem quotientDilation_measurePreserving (t : Fˣ)
    (μ : Measure (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    MeasurePreserving (quotientDilation F t) μ μ := by
  letI : BorelSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := ⟨rfl⟩
  letI := KPAdditiveFundamentalDomain.quotient_compactSpace F
  obtain ⟨e, he⟩ := quotientDilation_is_additive_homeomorphism F t
  apply (quotientDilation F t).measurePreserving
  · have hef : (e : _ → _) = quotientDilation F t := funext he
    rw [← hef]
    exact e.continuous
  · have hef : (e : _ → _) = quotientDilation F t := funext he
    rw [← hef]
    exact e.surjective
  · rfl

end DedekindZetaZeroFree.KPAdditiveRationalDilation

end
