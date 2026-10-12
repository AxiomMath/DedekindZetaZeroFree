module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SubmodulesAndQuotients

@[expose] public section

namespace DedekindZetaZeroFree

open scoped Topology NNReal

section Sections
variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup E] [Module ℂ E]
    (H : Subgroup G) (τ : Representation ℂ H E) (d : H →* (ℝ≥0)ˣ)

def normalizedSectionRepresentation : Representation ℂ H E where
  toFun h := (((d h : ℝ≥0) : ℝ) : ℂ) • τ h
  map_one' := by ext v; simp
  map_mul' := by
    intro h k
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_mul, Units.val_mul,
      NNReal.coe_mul, Complex.ofReal_mul, map_smul, smul_smul]
    rw [mul_comm]

@[simp] theorem normalizedSectionRepresentation_apply (h : H) (v : E) :
    normalizedSectionRepresentation H τ d h v =
      (((d h : ℝ≥0) : ℝ) : ℂ) • τ h v := rfl

def EqSections : Submodule ℂ (G → E) where
  carrier := {f | ∀ (h : H) (g : G),
    f ((h : G) * g) = normalizedSectionRepresentation H τ d h (f g)}
  zero_mem' := by intro h g; simp
  add_mem' := by intro f k hf hk h g; simp [hf h g, hk h g]
  smul_mem' := by intro a f hf h g; simp [hf h g]

@[simp] theorem mem_EqSections (f : G → E) : f ∈ EqSections H τ d ↔
    ∀ (h : H) (g : G), f ((h : G) * g) =
      (((d h : ℝ≥0) : ℝ) : ℂ) • τ h (f g) := Iff.rfl

def eqSectionsRepresentation : Representation ℂ G (EqSections H τ d) where
  toFun a :=
    { toFun := fun f => ⟨fun g => f.val (g * a), by
        intro h g
        simpa only [mul_assoc] using f.property h (g * a)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

@[simp] theorem eqSectionsRepresentation_apply (a g : G) (f : EqSections H τ d) :
    (eqSectionsRepresentation H τ d a f).val g = f.val (g * a) := rfl

def LCSections : Submodule ℂ (EqSections H τ d) where
  carrier := {f | IsLocallyConstant (f : G → E)}
  zero_mem' := IsLocallyConstant.zero
  add_mem' := by intro f k hf hk; exact hf.add hk
  smul_mem' := by
    intro a f hf
    exact hf.comp (fun v => a • v)

@[simp] theorem mem_LCSections (f : EqSections H τ d) :
    f ∈ LCSections H τ d ↔ IsLocallyConstant (f : G → E) := Iff.rfl

def SmoothInd : Submodule ℂ (EqSections H τ d) :=
  smoothSubmodule (eqSectionsRepresentation H τ d)

def smoothIndRepresentation : Representation ℂ G (SmoothInd H τ d) :=
  smoothPart (eqSectionsRepresentation H τ d)

theorem smoothIndRepresentation_smooth :
    SmoothRepresentation (G := G) (V := SmoothInd H τ d) (smoothIndRepresentation H τ d) :=
  smoothPart_smooth (eqSectionsRepresentation H τ d)

theorem SmoothInd_le_LCSections : SmoothInd H τ d ≤ LCSections H τ d := by
  intro f hf
  rw [mem_LCSections]
  rw [SmoothInd, mem_smoothSubmodule] at hf
  rcases hf with ⟨J, hJ⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(x * ·) '' (J : Set G), ?_, ?_, ?_⟩
  · exact (Homeomorph.mulLeft x).isOpenMap _ J.isOpen
  · exact ⟨1, J.one_mem, by simp⟩
  · rintro y ⟨j, hj, rfl⟩
    have h := congrFun (congrArg Subtype.val (hJ j hj)) x
    simpa using h

abbrev SectionCosetSpace := Quotient (QuotientGroup.rightRel H)

def HasCompactSupportModH (f : G → E) : Prop :=
  IsCompact (closure ((Quotient.mk (QuotientGroup.rightRel H)) '' Function.support f))

def cosetRightMap (a : G) :
    Quotient (QuotientGroup.rightRel H) → Quotient (QuotientGroup.rightRel H) :=
  Quot.map (· * a)
    (fun x y (h : (QuotientGroup.rightRel H).r x y) =>
      (by
        rw [QuotientGroup.rightRel_apply] at h ⊢
        have : (y * a) * (x * a)⁻¹ = y * x⁻¹ := by group
        rwa [this] : (QuotientGroup.rightRel H).r (x * a) (y * a)))

private theorem cosetRightMap_mk (a x : G) :
    cosetRightMap H a (Quotient.mk (QuotientGroup.rightRel H) x) =
      Quotient.mk (QuotientGroup.rightRel H) (x * a) := rfl

theorem continuous_cosetRightMap (a : G) : Continuous (cosetRightMap H a) := by
  unfold cosetRightMap
  exact continuous_quot_map _ (continuous_mul_const a)

theorem cosetRightMap_left_inv (a : G) (q : Quotient (QuotientGroup.rightRel H)) :
    cosetRightMap H a⁻¹ (cosetRightMap H a q) = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [cosetRightMap_mk, cosetRightMap_mk]
    refine Quot.sound ?_
    rw [QuotientGroup.rightRel_apply]
    have : x * ((x * a) * a⁻¹)⁻¹ = 1 := by group
    rw [this]
    exact H.one_mem

def cosetRightHomeomorph (a : G) :
    Quotient (QuotientGroup.rightRel H) ≃ₜ Quotient (QuotientGroup.rightRel H) where
  toFun := cosetRightMap H a
  invFun := cosetRightMap H a⁻¹
  left_inv := cosetRightMap_left_inv H a
  right_inv := fun q => by simpa using cosetRightMap_left_inv H a⁻¹ q
  continuous_toFun := continuous_cosetRightMap H a
  continuous_invFun := continuous_cosetRightMap H a⁻¹

def CompactSmoothInd : Submodule ℂ (SmoothInd H τ d) where
  carrier := {f | HasCompactSupportModH H (f.val : G → E)}
  zero_mem' := by
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support ((0 : SmoothInd H τ d).val : G → E)))
    simp
  add_mem' := by
    intro f k hf hk
    have hsub : Function.support ((f + k).val : G → E) ⊆
        Function.support (f.val : G → E) ∪ Function.support (k.val : G → E) := by
      intro g hg
      simp only [Set.mem_union, Function.mem_support]
      by_contra h
      simp only [not_or, not_not] at h
      exact hg (by simp [Submodule.coe_add, h.1, h.2])
    have himg : Quotient.mk (QuotientGroup.rightRel H) '' Function.support ((f + k).val : G → E) ⊆
        Quotient.mk (QuotientGroup.rightRel H) '' Function.support (f.val : G → E) ∪
        Quotient.mk (QuotientGroup.rightRel H) '' Function.support (k.val : G → E) :=
      (Set.image_mono hsub).trans (le_of_eq (Set.image_union _ _ _))
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support ((f + k).val : G → E)))
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support (f.val : G → E))) at hf
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support (k.val : G → E))) at hk
    exact (hf.union hk).of_isClosed_subset isClosed_closure
      ((closure_mono himg).trans (le_of_eq closure_union))
  smul_mem' := by
    intro c f hf
    have hsub : Function.support ((c • f).val : G → E) ⊆ Function.support (f.val : G → E) := by
      intro g hg
      simp only [Function.mem_support]
      intro h
      exact hg (by simp [Submodule.coe_smul, h])
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support ((c • f).val : G → E)))
    change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
      Function.support (f.val : G → E))) at hf
    exact hf.of_isClosed_subset isClosed_closure (closure_mono (Set.image_mono hsub))

private theorem smoothIndRepresentation_val (a : G) (f : SmoothInd H τ d) (g : G) :
    ((smoothIndRepresentation H τ d a f).val : G → E) g = (f.val : G → E) (g * a) := rfl

theorem CompactSmoothInd_stable (a : G) :
    CompactSmoothInd H τ d ≤ (CompactSmoothInd H τ d).comap
      (smoothIndRepresentation H τ d a) := by
  intro f hf
  rw [Submodule.mem_comap]
  change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
    Function.support ((smoothIndRepresentation H τ d a f).val : G → E)))
  change IsCompact (closure (Quotient.mk (QuotientGroup.rightRel H) ''
    Function.support (f.val : G → E))) at hf
  have hsupp : Function.support ((smoothIndRepresentation H τ d a f).val : G → E) =
      (· * a⁻¹) '' Function.support (f.val : G → E) := by
    ext g
    simp only [Function.mem_support, Set.mem_image, smoothIndRepresentation_val]
    constructor
    · intro hg
      exact ⟨g * a, hg, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hsupp]
  have hcomp : (Quotient.mk (QuotientGroup.rightRel H)) ∘ (· * a⁻¹) =
      cosetRightMap H a⁻¹ ∘ (Quotient.mk (QuotientGroup.rightRel H)) := by
    funext x
    exact (cosetRightMap_mk H a⁻¹ x).symm
  have himg : Quotient.mk (QuotientGroup.rightRel H) ''
        ((· * a⁻¹) '' Function.support (f.val : G → E)) =
      cosetRightMap H a⁻¹ '' (Quotient.mk (QuotientGroup.rightRel H) ''
        Function.support (f.val : G → E)) := by
    rw [← Set.image_comp (Quotient.mk (QuotientGroup.rightRel H)) (· * a⁻¹)
        (Function.support (f.val : G → E)),
      ← Set.image_comp (cosetRightMap H a⁻¹) (Quotient.mk (QuotientGroup.rightRel H))
        (Function.support (f.val : G → E)), hcomp]
  rw [himg]
  have hcompact : IsCompact (cosetRightMap H a⁻¹ '' closure
      (Quotient.mk (QuotientGroup.rightRel H) '' Function.support (f.val : G → E))) :=
    hf.image (cosetRightHomeomorph H a⁻¹).continuous
  have hcl : closure (cosetRightMap H a⁻¹ ''
      (Quotient.mk (QuotientGroup.rightRel H) '' Function.support (f.val : G → E))) =
      cosetRightMap H a⁻¹ '' closure
        (Quotient.mk (QuotientGroup.rightRel H) '' Function.support (f.val : G → E)) :=
    (Homeomorph.image_closure (cosetRightHomeomorph H a⁻¹) _).symm
  rw [hcl]
  exact hcompact

def compactSmoothIndRepresentation :
    Representation ℂ G (CompactSmoothInd H τ d) :=
  (smoothIndRepresentation H τ d).subrepresentation
    (CompactSmoothInd H τ d) (CompactSmoothInd_stable H τ d)

end Sections

end DedekindZetaZeroFree
