module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.EquivariantSmoothSections
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactOpenFixedExactness

@[expose] public section

namespace DedekindZetaZeroFree.CompactInductionProjectivity

open scoped Topology

section CompactInduction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] (U : CompactOpenLevel G)

abbrev inducingSubgroup : Subgroup G := U.toOpenSubgroup.toSubgroup

abbrev Cosets := SectionCosetSpace (inducingSubgroup U)

abbrev P := CompactSmoothInd (inducingSubgroup U)
  (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1

noncomputable def representation : Representation ℂ G (P U) :=
  compactSmoothIndRepresentation (inducingSubgroup U)
    (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1

def sectionValue (F : P U) (g : G) : ℂ := F.val.val.val g

@[simp] theorem representation_apply (h g : G) (F : P U) :
    sectionValue U (representation U h F) g = sectionValue U F (g * h) := by
  rfl

theorem sectionValue_left_invariant (F : P U) (u : inducingSubgroup U) (g : G) :
    sectionValue U F ((u : G) * g) = sectionValue U F g := by
  have h := F.val.val.property u g
  change sectionValue U F ((u : G) * g) =
    (1 : ℂ) • sectionValue U F g at h
  simpa only [one_smul] using h

omit [IsTopologicalGroup G] [T2Space G] in
theorem coset_left (u : inducingSubgroup U) (g : G) :
    Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) ((u : G) * g) =
      Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g := by
  apply Quotient.sound
  change (QuotientGroup.rightRel (inducingSubgroup U)) ((u : G) * g) g
  rw [QuotientGroup.rightRel_apply]
  simpa using (inducingSubgroup U).inv_mem u.property

theorem sectionValue_out (F : P U) (g : G) :
    sectionValue U F (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g).out =
      sectionValue U F g := by
  have h := Quotient.exact (Quotient.out_eq
    (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g))
  change (QuotientGroup.rightRel (inducingSubgroup U)) (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g).out g at h
  rw [QuotientGroup.rightRel_apply] at h
  have hi := sectionValue_left_invariant U F ⟨g *
    (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g).out⁻¹, h⟩
    (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g).out
  simpa using hi.symm

noncomputable def finiteCosetSection : (Cosets U →₀ ℂ) →ₗ[ℂ]
    EqSections (inducingSubgroup U)
      (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1 where
  toFun f := ⟨fun g => f (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g),
    by
      intro u g
      change f (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) ((u : G) * g)) =
        (1 : ℂ) • f (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g)
      rw [coset_left, one_smul]⟩
  map_add' := by intros; ext g; simp
  map_smul' := by intros; ext g; simp

@[simp] theorem finiteCosetSection_apply (f : Cosets U →₀ ℂ) (g : G) :
    (finiteCosetSection U f).val g =
      f (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g) := rfl

theorem finiteCosetSection_smooth (f : Cosets U →₀ ℂ) :
    finiteCosetSection U f ∈ SmoothInd (inducingSubgroup U)
      (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simpa using (SmoothInd (inducingSubgroup U)
      (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1).zero_mem
  | add f k hf hk => simpa only [map_add] using
      (SmoothInd (inducingSubgroup U)
        (Representation.trivial ℂ (inducingSubgroup U) ℂ) 1).add_mem hf hk
  | single c a =>
    apply (mem_smoothSubmodule _ _).mpr
    refine ⟨U.toOpenSubgroup.comap (MulAut.conj c.out).toMonoidHom
      (IsTopologicalGroup.continuous_conj c.out), ?_⟩
    intro j hj
    apply Subtype.ext
    funext g
    change Finsupp.single c a (Quotient.mk _ (g * j)) =
      Finsupp.single c a (Quotient.mk _ g)
    have hj' : c.out * j * c.out⁻¹ ∈ inducingSubgroup U := hj
    have heq : (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) (g * j) = c) ↔
        (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g = c) := by
      conv_lhs => rw [← Quotient.out_eq c]
      conv_rhs => rw [← Quotient.out_eq c]
      rw [Quotient.eq, Quotient.eq, QuotientGroup.rightRel_apply,
        QuotientGroup.rightRel_apply]
      have hi : c.out * j⁻¹ * c.out⁻¹ ∈ inducingSubgroup U := by
        simpa [mul_assoc] using (inducingSubgroup U).inv_mem hj'
      have he : c.out * (g * j)⁻¹ =
          (c.out * j⁻¹ * c.out⁻¹) * (c.out * g⁻¹) := by group
      rw [he]
      exact mul_mem_cancel_left hi
    simp only [Finsupp.single_apply, eq_comm (a := c), heq]

noncomputable instance cosetsDiscrete : DiscreteTopology (Cosets U) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro c
  rw [isOpen_coinduced]
  have heq : (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U))) ⁻¹' {c} =
      (fun g : G => c.out * g⁻¹) ⁻¹' (inducingSubgroup U : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    conv_lhs => rw [← Quotient.out_eq c]
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
    rfl
  change IsOpen ((Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U))) ⁻¹' {c})
  rw [heq]
  exact U.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_inv)

theorem finiteCosetSection_compact_support (f : Cosets U →₀ ℂ) :
    HasCompactSupportModH (inducingSubgroup U) (finiteCosetSection U f).val := by
  have heq : (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U))) ''
      Function.support (finiteCosetSection U f).val = Function.support f := by
    ext c
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hc
      refine ⟨c.out, ?_, Quotient.out_eq c⟩
      simpa only [Function.mem_support, finiteCosetSection_apply, Quotient.out_eq] using hc
  unfold HasCompactSupportModH
  rw [heq, (f.finite_support.isClosed).closure_eq]
  exact f.finite_support.isCompact

theorem sectionValue_finite_coset_support (F : P U) :
    (Function.support (fun c : Cosets U => sectionValue U F c.out)).Finite := by
  apply Set.Finite.subset F.property.finite_of_discrete
  intro c hc
  apply subset_closure
  exact ⟨c.out, hc, Quotient.out_eq c⟩

noncomputable def finiteSupportEquiv : P U ≃ₗ[ℂ] (Cosets U →₀ ℂ) where
  toFun F := Finsupp.ofSupportFinite
    (fun c => sectionValue U F c.out) (sectionValue_finite_coset_support U F)
  invFun f := ⟨⟨finiteCosetSection U f, finiteCosetSection_smooth U f⟩,
    finiteCosetSection_compact_support U f⟩
  left_inv := by
    intro F
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact sectionValue_out U F g
  right_inv := by
    intro f
    ext c
    change f (Quotient.mk _ c.out) = f c
    rw [Quotient.out_eq]
  map_add' := by intros; ext c; rfl
  map_smul' := by intros; ext c; rfl

theorem finiteSupportEquiv_apply (F : P U) (g : G) :
    finiteSupportEquiv U F
      (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g) =
        sectionValue U F g := by
  exact sectionValue_out U F g

noncomputable def finiteSupportRepresentation : Representation ℂ G (Cosets U →₀ ℂ) where
  toFun h := (finiteSupportEquiv U).toLinearMap ∘ₗ representation U h ∘ₗ
    (finiteSupportEquiv U).symm.toLinearMap
  map_one' := by
    ext f
    simp
  map_mul' := by
    intro g h
    ext f
    simp [map_mul, Module.End.mul_apply]

noncomputable def delta : P U :=
  (finiteSupportEquiv U).symm
    (Finsupp.single (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) 1) 1)

theorem delta_apply (g : G) :
    sectionValue U (delta U) g =
      Set.indicator (inducingSubgroup U : Set G) (fun _ => (1 : ℂ)) g := by
  classical
  rw [← finiteSupportEquiv_apply]
  simp only [delta, LinearEquiv.apply_symm_apply]
  change Finsupp.single (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) 1) 1
    (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g) = _
  simp [Finsupp.single_apply, Quotient.eq, QuotientGroup.rightRel_apply, Set.indicator]

theorem delta_fixed (u : inducingSubgroup U) :
    representation U (u : G) (delta U) = delta U := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change sectionValue U (representation U (u : G) (delta U)) g = sectionValue U (delta U) g
  rw [representation_apply, delta_apply, delta_apply]
  have he : g * (u : G) ∈ inducingSubgroup U ↔ g ∈ inducingSubgroup U :=
    mul_mem_cancel_right u.property
  simp only [Set.indicator, Set.mem_setOf_eq]
  change (if g * (u : G) ∈ inducingSubgroup U then (1 : ℂ) else 0) =
    (if g ∈ inducingSubgroup U then 1 else 0)
  rw [he]

theorem finiteSupportEquiv_translate_delta (g : G) :
    finiteSupportEquiv U (representation U g⁻¹ (delta U)) =
      Finsupp.single (Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g) 1 := by
  classical
  ext c
  obtain ⟨k, rfl⟩ := Quotient.exists_rep c
  rw [finiteSupportEquiv_apply, representation_apply, delta_apply]
  simp only [Finsupp.single_apply, Quotient.eq, QuotientGroup.rightRel_apply]
  change (if k * g⁻¹ ∈ inducingSubgroup U then (1 : ℂ) else 0) =
    (if k * g⁻¹ ∈ inducingSubgroup U then 1 else 0)
  rfl

section Target
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)

theorem evaluation_fixed (T : Representation.IntertwiningMap (representation U) ρ) :
    T (delta U) ∈ fixedSubmodule ρ (inducingSubgroup U) := by
  intro u
  rw [← Representation.IntertwiningMap.isIntertwining (representation U) ρ T (u : G) (delta U), delta_fixed]

theorem intertwiningMap_ext
    (S T : Representation.IntertwiningMap (representation U) ρ)
    (h : S (delta U) = T (delta U)) : S = T := by
  classical
  ext F
  obtain ⟨f, rfl⟩ := (finiteSupportEquiv U).symm.surjective F
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk => simpa only [map_add] using congrArg₂ (· + ·) hf hk
  | single c a =>
    have he : Finsupp.single c a = a • finiteSupportEquiv U
        (representation U c.out⁻¹ (delta U)) := by
      rw [finiteSupportEquiv_translate_delta, Quotient.out_eq]
      ext d
      simp [Finsupp.single_apply]
    rw [he]
    simp only [map_smul, LinearEquiv.symm_apply_apply]
    change a • S (representation U c.out⁻¹ (delta U)) =
      a • T (representation U c.out⁻¹ (delta U))
    rw [Representation.IntertwiningMap.isIntertwining (representation U) ρ S,
      Representation.IntertwiningMap.isIntertwining (representation U) ρ T, h]

theorem inverse_translate_well_defined (x : fixedSubmodule ρ (inducingSubgroup U))
    (g g' : G)
    (hgg' : Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g =
      Quotient.mk (QuotientGroup.rightRel (inducingSubgroup U)) g') :
    ρ g⁻¹ x.val = ρ g'⁻¹ x.val := by
  have h : g' * g⁻¹ ∈ inducingSubgroup U :=
    (QuotientGroup.rightRel_apply).mp (Quotient.eq.mp hgg')
  have hx := x.property (⟨g' * g⁻¹, h⟩ : inducingSubgroup U)
  have he : g⁻¹ = g'⁻¹ * (g' * g⁻¹) := by group
  conv_lhs => rw [he]
  rw [map_mul, Module.End.mul_apply, hx]

noncomputable def sumLinear (x : fixedSubmodule ρ (inducingSubgroup U)) :
    P U →ₗ[ℂ] X :=
  (Finsupp.linearCombination ℂ (fun c : Cosets U => ρ c.out⁻¹ x.val)).comp
    (finiteSupportEquiv U).toLinearMap

private theorem sumLinear_translate (x : fixedSubmodule ρ (inducingSubgroup U)) (g : G) :
    sumLinear U ρ x (representation U g⁻¹ (delta U)) = ρ g⁻¹ x.val := by
  change Finsupp.linearCombination ℂ _ (finiteSupportEquiv U _) = _
  rw [finiteSupportEquiv_translate_delta, Finsupp.linearCombination_single, one_smul]
  exact inverse_translate_well_defined U ρ x _ g (Quotient.out_eq _)

theorem sumLinear_intertwining (x : fixedSubmodule ρ (inducingSubgroup U))
    (h : G) (F : P U) :
    sumLinear U ρ x (representation U h F) = ρ h (sumLinear U ρ x F) := by
  classical
  obtain ⟨f, rfl⟩ := (finiteSupportEquiv U).symm.surjective F
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f k hf hk => simpa only [map_add] using congrArg₂ (· + ·) hf hk
  | single c a =>
    have he : Finsupp.single c a = a • finiteSupportEquiv U
        (representation U c.out⁻¹ (delta U)) := by
      rw [finiteSupportEquiv_translate_delta, Quotient.out_eq]
      ext d
      simp [Finsupp.single_apply]
    rw [he]
    simp only [map_smul, LinearEquiv.symm_apply_apply]
    congr 1
    have hm : representation U h (representation U c.out⁻¹ (delta U)) =
        representation U (c.out * h⁻¹)⁻¹ (delta U) := by
      simp [map_mul, Module.End.mul_apply]
    rw [hm, sumLinear_translate, sumLinear_translate]
    simp [map_mul, Module.End.mul_apply]

noncomputable def finiteSumMap (x : fixedSubmodule ρ (inducingSubgroup U)) :
    Representation.IntertwiningMap (representation U) ρ where
  toLinearMap :=
    { toFun := fun F => (finiteSupportEquiv U F).sum
        (fun c a => a • ρ c.out⁻¹ x.val)
      map_add' := by
        intro F K
        exact (sumLinear U ρ x).map_add F K
      map_smul' := by
        intro a F
        exact (sumLinear U ρ x).map_smul a F }
  isIntertwining' := by
    intro h
    ext F
    exact sumLinear_intertwining U ρ x h F

@[simp] theorem finiteSumMap_delta (x : fixedSubmodule ρ (inducingSubgroup U)) :
    finiteSumMap U ρ x (delta U) = x.val := by
  change sumLinear U ρ x (delta U) = x.val
  simpa using sumLinear_translate U ρ x (1 : G)

noncomputable def evaluationEquiv :
    Representation.IntertwiningMap (representation U) ρ ≃ₗ[ℂ]
      fixedSubmodule ρ (inducingSubgroup U) where
  toFun T := ⟨T (delta U), evaluation_fixed U ρ T⟩
  invFun := finiteSumMap U ρ
  left_inv := by
    intro T
    apply intertwiningMap_ext U ρ
    exact finiteSumMap_delta U ρ _
  right_inv := by
    intro x
    apply Subtype.ext
    exact finiteSumMap_delta U ρ x
  map_add' := by intros; apply Subtype.ext; rfl
  map_smul' := by intros; apply Subtype.ext; rfl

@[simp] theorem evaluationEquiv_apply
    (T : Representation.IntertwiningMap (representation U) ρ) :
    (evaluationEquiv U ρ T).val = T (delta U) := rfl

end Target

theorem lift_equivariant_surjection
    (hcompactOpen : ∀ N ∈ 𝓝 (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ N)
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (hρ : SmoothRepresentation ρ) (hσ : SmoothRepresentation σ)
    (q : Representation.IntertwiningMap ρ σ) (hq : Function.Surjective q)
    (T : Representation.IntertwiningMap (representation U) σ) :
    ∃ T' : Representation.IntertwiningMap (representation U) ρ, q.comp T' = T := by
  obtain ⟨x, hx⟩ := fixedSpaceMap_surjective ρ σ hρ hσ U q hq
    (evaluationEquiv U σ T)
  refine ⟨finiteSumMap U ρ x, ?_⟩
  apply intertwiningMap_ext U σ
  change q (finiteSumMap U ρ x (delta U)) = T (delta U)
  rw [finiteSumMap_delta]
  exact congrArg Subtype.val hx

end CompactInduction

end DedekindZetaZeroFree.CompactInductionProjectivity
