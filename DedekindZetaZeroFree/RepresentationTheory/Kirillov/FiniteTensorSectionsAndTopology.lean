module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrdinarySectionCoinvariants
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.TensorShuffle
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.TensorSlotCoinvariants

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPKirillovFiniteTensor.ActualGauge

open scoped NumberField Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (ψ : Multiplicative (K F w) →* ℂˣ)

def diagonalLift (t : (K F w)ˣ) : P F ζ hζ w :=
  ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr w) t,
    KPRankOneInduction.diagonalElement_mem F w t⟩

theorem diagonalLift_slope (t : (K F w)ˣ) :
    slope F ζ hζ w (diagonalLift F ζ hζ w t) = t := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F w _ : K F w) = t
  rw [KPRankOneInduction.borelRatio_eq F w _ (KPRankOneInduction.diagonalMatrix F w t)
    rfl (by simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d])]
  simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d]

variable (lift : (K F w)ˣ → P F ζ hζ w)
  (hslope : ∀ t, slope F ζ hζ w (lift t) = t)

def gaugeCoordinate (t : (K F w)ˣ) : H F ζ hζ w :=
  ⟨lift t * (diagonalLift F ζ hζ w t)⁻¹, by
    change slope F ζ hζ w _ = 1
    simp only [map_mul, map_inv, hslope, diagonalLift_slope, mul_inv_cancel]⟩

def gauge (t : (K F w)ˣ) : ℂˣ :=
  inducingCharacter F ζ hζ w ψ (gaugeCoordinate F ζ hζ w lift hslope t)

end DedekindZetaZeroFree.KPKirillovFiniteTensor.ActualGauge

end

end

section

noncomputable section

set_option maxHeartbeats 10000000

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 10000000

namespace DedekindZetaZeroFree.KPKirillovFiniteTensor

open scoped NumberField TensorProduct Classical

open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

noncomputable instance scalarSectionAddCommGroup
    (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
    (ψ : Multiplicative (K F w) →* ℂˣ) :
    AddCommGroup (Sections F ζ hζ w m ψ ℂ) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI : AddCommGroup (EqSections (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ ℂ) 1) := Submodule.addCommGroup _
  letI : AddCommGroup (SmoothInd (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ ℂ) 1) := Submodule.addCommGroup _
  exact Submodule.addCommGroup (CompactSmoothInd (H F ζ hζ w)
    (coefficientRepresentation F ζ hζ w ψ ℂ) 1)

variable (W : Finset (HeightOneSpectrum (RingOfIntegers F)))
  (m : W → ℕ) (hm : ∀ v, KPLocalChartTopology.MatrixChartDepth F v.val (m v))
  (ψ : ∀ v : W, Multiplicative (K F v.val) →* ℂˣ)
  (V : W → Type*) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  (ρ : ∀ v : W, Representation ℂ (G F ζ hζ v.val) (V v))

abbrev Jacquet (v : W) := KPLocalSmoothRepresentation.TwistedCoinvariants
  F ζ hζ v.val (ρ v) (ψ v)

abbrev ScalarSections (v : W) := Sections F ζ hζ v.val (m v) (ψ v) ℂ

def localEvaluation (v : W) :
    ScalarSections F ζ hζ W m ψ v ⊗[ℂ] Jacquet F ζ hζ W ψ V ρ v →ₗ[ℂ]
      Jacquet F ζ hζ W ψ V ρ v := by
  exact TensorProduct.lift
    { toFun := fun f => sectionValue F ζ hζ v.val (m v) (ψ v) f 1 •
        (LinearMap.id : Jacquet F ζ hζ W ψ V ρ v →ₗ[ℂ] _)
      map_add' := by intros; ext; simp [sectionValue, add_smul]
      map_smul' := by intros; ext; simp [sectionValue, smul_smul] }

@[simp]theorem localEvaluation_tmul (v : W)
    (f : ScalarSections F ζ hζ W m ψ v) (e : Jacquet F ζ hζ W ψ V ρ v) :
    localEvaluation F ζ hζ W m ψ V ρ v (f ⊗ₜ[ℂ] e) =
      sectionValue F ζ hζ v.val (m v) (ψ v) f 1 • e := by
  rfl

abbrev SectionTensor := ⨂[ℂ] v : W, ScalarSections F ζ hζ W m ψ v

end DedekindZetaZeroFree.KPKirillovFiniteTensor

end

end

section

noncomputable section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 10000000

namespace DedekindZetaZeroFree.KPKirillovFiniteTensor

open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (W : Finset (HeightOneSpectrum (RingOfIntegers F)))
  (m : W → ℕ) (hm : ∀ v, KPLocalChartTopology.MatrixChartDepth F v.val (m v))
  (ψ : ∀ v : W, Multiplicative (K F v.val) →* ℂˣ)
  (V : W → Type*) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  (ρ : ∀ v : W, Representation ℂ (G F ζ hζ v.val) (V v))

structure LocalEmbeddingData where
  character_lc : ∀ v, IsLocallyConstant (ψ v)
  character_ne : ∀ v, ψ v ≠ 1
  smooth_genuine : ∀ v, KPLocalSmoothRepresentation.smoothGenuine
    F ζ hζ v.val (m v) (ρ v)

  j : ∀ v, ScalarSections F ζ hζ W m ψ v ⊗[ℂ]
    Jacquet F ζ hζ W ψ V ρ v →ₗ[ℂ] V v
  injective : ∀ v, Function.Injective (j v)
  equivariant : ∀ v (a : P F ζ hζ v.val) x,
    j v (TensorProduct.map (rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ a)
      LinearMap.id x) = ρ v a.val (j v x)
  evaluation : ∀ v, (rootCoinvariantsMk (ρ v)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ v.val) (ψ v)).comp (j v) =
      localEvaluation F ζ hζ W m ψ V ρ v

abbrev JacquetTensor := ⨂[ℂ] v : W, Jacquet F ζ hζ W ψ V ρ v

noncomputable instance tensorSectionAddCommGroup
    (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (SectionTensor F ζ hζ W m ψ ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

abbrev AmbientTensor := ⨂[ℂ] v : W, V v
abbrev ProductAffine := ∀ v : W, P F ζ hζ v.val

abbrev InducedTensor (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :=
  SectionTensor F ζ hζ W m ψ ⊗[ℂ] E

def coefficientInclusion (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :
    InducedTensor F ζ hζ W m ψ V ρ E →ₗ[ℂ]
      SectionTensor F ζ hζ W m ψ ⊗[ℂ] JacquetTensor F ζ hζ W ψ V ρ :=
  TensorProduct.map LinearMap.id E.subtype

def tensorShuffle :
    (SectionTensor F ζ hζ W m ψ ⊗[ℂ] JacquetTensor F ζ hζ W ψ V ρ) ≃ₗ[ℂ]
      (⨂[ℂ] v : W, ScalarSections F ζ hζ W m ψ v ⊗[ℂ]
        Jacquet F ζ hζ W ψ V ρ v) :=
  ShuffleHelpers.shuffle _ _

@[simp]theorem tensorShuffle_tmul
    (f : ∀ v, ScalarSections F ζ hζ W m ψ v)
    (e : ∀ v, Jacquet F ζ hζ W ψ V ρ v) :
    tensorShuffle F ζ hζ W m ψ V ρ
      (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ e) =
      PiTensorProduct.tprod ℂ (fun v => f v ⊗ₜ[ℂ] e v) := by
  exact ShuffleHelpers.shuffle_tmul _ _ f e

variable (D : LocalEmbeddingData F ζ hζ W m hm ψ V ρ)

def tensorEmbedding :
    SectionTensor F ζ hζ W m ψ ⊗[ℂ] JacquetTensor F ζ hζ W ψ V ρ →ₗ[ℂ]
      AmbientTensor F W V :=
  (PiTensorProduct.map D.j).comp (tensorShuffle F ζ hζ W m ψ V ρ).toLinearMap

def subspaceEmbedding (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :
    InducedTensor F ζ hζ W m ψ V ρ E →ₗ[ℂ] AmbientTensor F W V :=
  (tensorEmbedding F ζ hζ W m hm ψ V ρ D).comp
    (coefficientInclusion F ζ hζ W m ψ V ρ E)

def ambientAction : Representation ℂ (ProductAffine F ζ hζ W) (AmbientTensor F W V) where
  toFun a := PiTensorProduct.map (fun v => ρ v (a v).val)
  map_one' := by
    simp only [Pi.one_apply, Subgroup.coe_one, map_one, PiTensorProduct.map_one]
  map_mul' := by
    intro a b
    simp only [Pi.mul_apply, Subgroup.coe_mul, map_mul, PiTensorProduct.map_mul]

def inducedAction (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Representation ℂ (ProductAffine F ζ hζ W) (SectionTensor F ζ hζ W m ψ ⊗[ℂ] E) where
  toFun a := TensorProduct.map (PiTensorProduct.map
    (fun v => rightAction F ζ hζ v.val (m v) (hm v) (ψ v) ℂ (a v))) LinearMap.id
  map_one' := by
    simp only [Pi.one_apply, map_one, PiTensorProduct.map_one, show (LinearMap.id : E →ₗ[ℂ] E) = 1 from rfl, TensorProduct.map_one]
  map_mul' := by
    intro a b
    simp only [Pi.mul_apply, map_mul, PiTensorProduct.map_mul]
    rw [← TensorProduct.map_mul]
    rfl

def tensorQuotient : AmbientTensor F W V →ₗ[ℂ] JacquetTensor F ζ hζ W ψ V ρ :=
  PiTensorProduct.map (fun v => rootCoinvariantsMk (ρ v)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ v.val) (ψ v))

def tensorEvaluation : SectionTensor F ζ hζ W m ψ ⊗[ℂ]
    JacquetTensor F ζ hζ W ψ V ρ →ₗ[ℂ] JacquetTensor F ζ hζ W ψ V ρ :=
  (PiTensorProduct.map (localEvaluation F ζ hζ W m ψ V ρ)).comp
    (tensorShuffle F ζ hζ W m ψ V ρ).toLinearMap

variable (hW : W.Nonempty)

theorem tensorEmbedding_equivariant (a : ProductAffine F ζ hζ W) x :
    tensorEmbedding F ζ hζ W m hm ψ V ρ D
      (inducedAction F ζ hζ W m hm ψ (JacquetTensor F ζ hζ W ψ V ρ) a x) =
      ambientAction F ζ hζ W V ρ a (tensorEmbedding F ζ hζ W m hm ψ V ρ D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f e =>
    induction f using PiTensorProduct.induction_on with
    | add f g hf hg => simp only [TensorProduct.add_tmul, map_add, hf, hg]
    | smul_tprod c f =>
      induction e using PiTensorProduct.induction_on with
      | add e d he hd => simp only [TensorProduct.tmul_add, map_add, he, hd]
      | smul_tprod d e =>
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
        congr 2
        simp only [tensorEmbedding, inducedAction, ambientAction,
          LinearMap.comp_apply, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
          LinearMap.id_apply, tensorShuffle_tmul]
        dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]
        simp only [TensorProduct.map_tmul, PiTensorProduct.map_tprod,
          LinearMap.id_apply, LinearEquiv.coe_coe, tensorShuffle_tmul]
        apply congrArg (PiTensorProduct.tprod ℂ)
        funext v
        exact D.equivariant v (a v) (f v ⊗ₜ[ℂ] e v)

theorem tensor_evaluation_square :
    (tensorQuotient F ζ hζ W ψ V ρ).comp (tensorEmbedding F ζ hζ W m hm ψ V ρ D) =
      tensorEvaluation F ζ hζ W m ψ V ρ := by
  unfold tensorQuotient tensorEmbedding tensorEvaluation
  rw [← LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
  congr 2
  funext v
  exact D.evaluation v

private theorem coefficientInclusion_action
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ))
    (a : ProductAffine F ζ hζ W) x :
    coefficientInclusion F ζ hζ W m ψ V ρ E
      (inducedAction F ζ hζ W m hm ψ E a x) =
      inducedAction F ζ hζ W m hm ψ (JacquetTensor F ζ hζ W ψ V ρ) a
        (coefficientInclusion F ζ hζ W m ψ V ρ E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f e =>
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem image_stable (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ))
    (a : ProductAffine F ζ hζ W) :
    LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E) ≤
      (LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E)).comap
        (ambientAction F ζ hζ W V ρ a) := by
  rintro x ⟨y, rfl⟩
  refine ⟨inducedAction F ζ hζ W m hm ψ E a y, ?_⟩
  unfold subspaceEmbedding
  simp only [LinearMap.comp_apply, coefficientInclusion_action,
    tensorEmbedding_equivariant]

theorem subspaceEmbedding_equivariant
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ))
    (a : ProductAffine F ζ hζ W) x :
    subspaceEmbedding F ζ hζ W m hm ψ V ρ D E
      (inducedAction F ζ hζ W m hm ψ E a x) =
      ambientAction F ζ hζ W V ρ a
        (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E x) := by
  unfold subspaceEmbedding
  simp only [LinearMap.comp_apply, coefficientInclusion_action,
    tensorEmbedding_equivariant]

 def rootSlot (v : W) :
    Multiplicative (K F v.val) →* ProductAffine F ζ hζ W where
  toFun b := Function.update 1 v (n F ζ hζ v.val b.toAdd)
  map_one' := by
    have hn : n F ζ hζ v.val 0 = 1 := by
      apply Subtype.ext
      exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ v.val).map_one
    simp only [toAdd_one, hn]
    exact Function.update_eq_self v (1 : ProductAffine F ζ hζ W)
  map_mul' := by
    intro a b
    have hn : n F ζ hζ v.val (a.toAdd + b.toAdd) =
        n F ζ hζ v.val a.toAdd * n F ζ hζ v.val b.toAdd := by
      apply Subtype.ext
      exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ v.val).map_mul a b
    funext w
    by_cases h : w = v
    · subst w
      simp only [toAdd_mul, hn, Function.update_self, Pi.mul_apply]
    · simp [Function.update_of_ne h]

def slotRootAction (v : W) (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Representation ℂ (Multiplicative (K F v.val))
      (SectionTensor F ζ hζ W m ψ ⊗[ℂ] E) := by
  exact (inducedAction F ζ hζ W m hm ψ E).comp (rootSlot F ζ hζ W v)

include D in

theorem slot_relationSpan_eq_top (v : W)
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :
    Representation.Coinvariants.ker (k := ℂ)
      (V := SectionTensor F ζ hζ W m ψ ⊗[ℂ] E) (slotRootAction F ζ hζ W m hm ψ v E) = ⊤ := by
  classical
  apply KPKirillovFiniteTensorProve.slot_relationSpan_eq_top v
    (KPKirillovSectionOrdinaryVanishing.ordinaryRootAction
      F ζ hζ v.val (m v) (hm v) (ψ v) ℂ)
  · intro b f e
    change TensorProduct.map _ _ _ = _
    simp only [TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearMap.id_apply]
    congr 2
    funext w
    by_cases h : w = v
    · subst w
      simp [rootSlot, KPKirillovSectionOrdinaryVanishing.ordinaryRootAction]
    · simp [rootSlot, Function.update_of_ne h]
  · exact Submodule.Quotient.subsingleton_iff.mp
      (KPKirillovSectionOrdinaryVanishing.ordinary_section_coinvariants_vanish
        F ζ hζ v.val (m v) (hm v) (ψ v) (D.character_lc v) (D.character_ne v) ℂ)

include D in

def imageSlotRootAction (v : W)
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :
    Representation ℂ (Multiplicative (K F v.val))
      (LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E)) :=
  ((ambientAction F ζ hζ W V ρ).subrepresentation
    (LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E))
    (image_stable F ζ hζ W m hm ψ V ρ D E)).comp (rootSlot F ζ hζ W v)

theorem imageSlotRootAction_apply (v : W)
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) (b : K F v.val)
    (x : LinearMap.range (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E)) :
    (imageSlotRootAction F ζ hζ W m hm ψ V ρ D v E (Multiplicative.ofAdd b) x).val =
      ambientAction F ζ hζ W V ρ
        (Function.update (1 : ProductAffine F ζ hζ W) v (n F ζ hζ v.val b)) x.val := by
  rfl

theorem image_slot_coinvariants_vanish (v : W)
    (E : Submodule ℂ (JacquetTensor F ζ hζ W ψ V ρ)) :
    Subsingleton (Representation.Coinvariants
      (imageSlotRootAction F ζ hζ W m hm ψ V ρ D v E))  := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply KPKirillovFiniteTensorProve.relationSpan_eq_top_of_surjective
    (A := SectionTensor F ζ hζ W m ψ ⊗[ℂ] E)
    (slotRootAction F ζ hζ W m hm ψ v E)
    (imageSlotRootAction F ζ hζ W m hm ψ V ρ D v E)
    (subspaceEmbedding F ζ hζ W m hm ψ V ρ D E).rangeRestrict
  · rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  · intro b x
    apply Subtype.ext
    exact subspaceEmbedding_equivariant F ζ hζ W m hm ψ V ρ D E
      (rootSlot F ζ hζ W v b) x
  · exact slot_relationSpan_eq_top F ζ hζ W m hm ψ V ρ D v E

abbrev RawProduct := ∀ v : W, KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v.val)

def rawAffineSubgroup : Subgroup (RawProduct F ζ hζ W) where
  carrier := {g | ∀ v, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v.val) (g v) ∈
    P F ζ hζ v.val}
  one_mem' := by
    intro v
    simpa only [Pi.one_apply, map_one] using (P F ζ hζ v.val).one_mem
  mul_mem' := by
    intro a b ha hb v
    simpa only [Pi.mul_apply, map_mul] using (P F ζ hζ v.val).mul_mem (ha v) (hb v)
  inv_mem' := by
    intro g hg v
    simpa only [Pi.inv_apply, map_inv] using (P F ζ hζ v.val).inv_mem (hg v)

def productSplitScalars : (∀ v : W, (K F v.val)ˣ) →* RawProduct F ζ hζ W where
  toFun t v := KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr v.val) (t v)
  map_one' := by
    funext v
    exact map_one (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr v.val))
  map_mul' := by
    intro a b
    funext v
    exact map_mul (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr v.val)) (a v) (b v)

variable (τ : ∀ v : W,
  Representation ℂ (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v.val)) (V v))

def rawAmbientAction : Representation ℂ (RawProduct F ζ hζ W) (AmbientTensor F W V) where
  toFun g := PiTensorProduct.map (fun v => τ v (g v))
  map_one' := by
    simp only [Pi.one_apply, map_one, PiTensorProduct.map_one]
  map_mul' := by
    intro a b
    simp only [Pi.mul_apply, map_mul, PiTensorProduct.map_mul]

structure LocalTrivialization (v : W) where
  lift : (K F v.val)ˣ → P F ζ hζ v.val
  slope_lift : ∀ t, slope F ζ hζ v.val (lift t) = t
  toFunctions : ScalarSections F ζ hζ W m ψ v ≃ₗ[ℂ]
    CompactFunctions (K F v.val)ˣ ℂ
  value : ∀ f t, (toFunctions f).val t =
    sectionValue F ζ hζ v.val (m v) (ψ v) f (lift t)

variable (T : ∀ v : W, LocalTrivialization F ζ hζ W m ψ v)

end DedekindZetaZeroFree.KPKirillovFiniteTensor

end
end
