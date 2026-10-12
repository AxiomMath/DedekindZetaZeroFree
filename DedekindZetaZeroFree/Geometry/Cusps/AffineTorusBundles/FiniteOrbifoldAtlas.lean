module

public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.QuotientCoordinates

@[expose] public section

section
noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.KPCuspChart

 def placeRing (F : Type*) [Field F] [NumberField F] : F →+* Horizontal F where
  toFun := embedding F
  map_zero' := (embedding F).map_zero
  map_add' := (embedding F).map_add
  map_one' := by ext i; simp [embedding]
  map_mul' := by intro x y; ext i; simp [embedding]

theorem raw_translation_lattice_stable (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S) :
    ∀ (u : D.E) (x : F), x ∈ D.L → ((u : Fˣ) : F) * x ∈ D.L :=
  KPCuspLogShape.actual_translation_lattice_stable F S D.upper D.L D.E
    D.inclusion D.ratio D.surjective D.exact D.unipotentFormula D.ratioFormula

section
variable (F : Type*) [Field F] [NumberField F]
variable (L : AddSubgroup F) (E : Subgroup Fˣ)
variable (hinv : ∀ (u : E) (x : F), x ∈ L → ((u : Fˣ) : F) * x ∈ L)

 def scalarMap (u : E) : Torus F L →+ Torus F L :=
  QuotientAddGroup.map (translationLattice F L) (translationLattice F L)
    (AddMonoidHom.mulLeft (placeRing F ((u : Fˣ) : F))) (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨((u : Fˣ) : F) * a, hinv u a ha, (placeRing F).map_mul _ _⟩)

private theorem scalarMap_mk (u : E) (x : Horizontal F) :
    scalarMap F L E hinv u (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (placeRing F ((u : Fˣ) : F) * x) := rfl

private theorem scalarMap_one : scalarMap F L E hinv 1 = AddMonoidHom.id _ := by
  ext x
  simp [scalarMap_mk]

private theorem scalarMap_mul (u v : E) : scalarMap F L E hinv (u * v) =
    (scalarMap F L E hinv u).comp (scalarMap F L E hinv v) := by
  ext x
  simp [scalarMap_mk, mul_assoc]

private theorem scalarMap_continuous (u : E) : Continuous (scalarMap F L E hinv u) := by
  rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
  exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
end

theorem raw_parabolic_torus_action (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S) :
    ∃ α : S →* (Torus F D.L ≃ₜ Torus F D.L),
      ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : Horizontal F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
        α g (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
            embedding F (A 0 1 / A 1 1) i) := by
  let hinv := raw_translation_lattice_stable F S D
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ :=
    KPCuspLogShape.upper_translation_cocycle F S D.upper D.E D.ratio D.ratioFormula
  let b : S → Torus F D.L → Torus F D.L := fun g x =>
    scalarMap F D.L D.E hinv (D.ratio g) x + QuotientAddGroup.mk (placeRing F (τ g))
  have hb1 (x : Torus F D.L) : b 1 x = x := by
    simp only [b, map_one, hτ1, map_zero, QuotientAddGroup.mk_zero, add_zero]
    exact DFunLike.congr_fun (scalarMap_one F D.L D.E hinv) x
  have hbmul (g k : S) (x : Torus F D.L) : b (g * k) x = b g (b k x) := by
    simp only [b, map_mul, hτmul, map_add, QuotientAddGroup.mk_add]
    rw [scalarMap_mul]
    change scalarMap F D.L D.E hinv (D.ratio g)
      (scalarMap F D.L D.E hinv (D.ratio k) x) +
      (QuotientAddGroup.mk (placeRing F ((D.ratio g : Fˣ) : F) * placeRing F (τ k)) +
        QuotientAddGroup.mk (placeRing F (τ g))) = _
    rw [scalarMap_mk]
    abel
  have hbcont (g : S) : Continuous (b g) :=
    (scalarMap_continuous F D.L D.E hinv (D.ratio g)).add continuous_const
  let e : S → (Torus F D.L ≃ₜ Torus F D.L) := fun g => {
    toFun := b g
    invFun := b g⁻¹
    left_inv := fun x => by rw [← hbmul, inv_mul_cancel, hb1]
    right_inv := fun x => by rw [← hbmul, mul_inv_cancel, hb1]
    continuous_toFun := hbcont g
    continuous_invFun := hbcont g⁻¹ }
  let α : S →* (Torus F D.L ≃ₜ Torus F D.L) := {
    toFun := e
    map_one' := by apply Homeomorph.ext; exact hb1
    map_mul' := fun g k => by apply Homeomorph.ext; exact hbmul g k }
  refine ⟨α, ?_⟩
  intro g A x hA hc
  change b g (QuotientAddGroup.mk x) = _
  simp only [b, scalarMap_mk, ← QuotientAddGroup.mk_add, hτformula g A hA]
  rfl

theorem raw_parabolic_torus_kernel (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (α : S →* (Torus F D.L ≃ₜ Torus F D.L))
    (hα : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : Horizontal F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      α g (QuotientAddGroup.mk x) = QuotientAddGroup.mk
        (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
          embedding F (A 0 1 / A 1 1) i)) : D.ratio.ker ≤ α.ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  have hgr : g ∈ D.inclusion.range := by rw [D.exact]; exact hg
  obtain ⟨v, rfl⟩ := hgr
  obtain ⟨A, hA, hc⟩ := D.upper _ (D.inclusion v).property
  obtain ⟨_, hd, ht⟩ := D.unipotentFormula v.toAdd A hA
  have hn : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hc, hz])
  have hv : A 0 1 / A 1 1 = (v.toAdd : F) := by rw [ht, hd, mul_div_cancel_right₀ _ hn]
  apply Homeomorph.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [hα _ A x hA hc, hg, hv]
  change QuotientAddGroup.mk (placeRing F 1 * x + placeRing F (v.toAdd : F)) = _
  rw [map_one, one_mul, QuotientAddGroup.mk_add]
  have hz : (QuotientAddGroup.mk (placeRing F (v.toAdd : F)) : Torus F D.L) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨v.toAdd, v.toAdd.property, rfl⟩
  rw [hz, add_zero]
  rfl

theorem raw_ratio_torus_action (F : Type*) [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S) :
    ∃ β : D.E →* (Torus F D.L ≃ₜ Torus F D.L),
      ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : Horizontal F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
        β (D.ratio g) (QuotientAddGroup.mk x) = QuotientAddGroup.mk
          (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
            embedding F (A 0 1 / A 1 1) i) := by
  obtain ⟨α, hα⟩ := raw_parabolic_torus_action F S D
  have hk := raw_parabolic_torus_kernel F S D α hα
  choose σ hσ using D.surjective
  have heq (g k : S) (h : D.ratio g = D.ratio k) : α g = α k :=
    (α.eq_iff).mpr (hk ((D.ratio.eq_iff).mp h))
  let β : D.E →* (Torus F D.L ≃ₜ Torus F D.L) := {
    toFun := fun u => α (σ u)
    map_one' := by
      rw [heq (σ 1) 1 (by rw [hσ, map_one]), map_one]
    map_mul' := fun u v => by
      rw [heq (σ (u * v)) (σ u * σ v) (by rw [hσ, map_mul, hσ, hσ]), map_mul] }
  refine ⟨β, ?_⟩
  intro g A x hA hc
  change α (σ (D.ratio g)) (QuotientAddGroup.mk x) = _
  rw [heq _ g (hσ _)]
  exact hα g A x hA hc

end DedekindZetaZeroFree.KPCuspChart

end

end

section
noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.KPCuspChart

private theorem upper_action (g : Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (hc : g 1 0 = 0) (u : ℂ) (hu : u ≠ 0) (ha : g 0 0 = u * g 1 1)
    (z : KPArch.H3) :
    KPArch.action g z = (u * z.1 + g 0 1 / g 1 1, z.2 + Real.log ‖u‖) := by
  have hd : g 1 1 ≠ 0 := by
    intro h
    apply g.det_ne_zero
    simp [Matrix.det_fin_two, hc, h]
  have hdR : ‖g 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have huR : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  apply Prod.ext
  · simp only [KPArch.action, KPArch.actionDenominator, hc, zero_mul, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), star_zero, mul_zero, add_zero]
    have hn : (‖g 1 1‖ ^ 2 : ℝ) = (g 1 1 * star (g 1 1) : ℂ) := by
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj (g 1 1)).symm
    rw [hn, ha]
    have hds : star (g 1 1) ≠ 0 := star_ne_zero.mpr hd
    field_simp
  · exact KPCuspLogShape.upper_action_snd g hc u hu ha z

theorem raw_actual_cross_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Cross F) :
    g • toArch F (p, 0) = toArch F
      (crossAffine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p, 0) := by
  change KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F) _ = _
  rw [← hA, KPCuspSiegel.action_mk]
  funext i
  let σ := (KPCusp.complexPlace F i).embedding
  have hi : (Matrix.GeneralLinearGroup.map σ A) 1 0 = 0 := by
    change σ (A 1 0) = 0
    simp [hc]
  have hu : σ ((D.ratio g : Fˣ) : F) ≠ 0 :=
    (map_ne_zero σ).mpr (Units.ne_zero _)
  have ha : (Matrix.GeneralLinearGroup.map σ A) 0 0 =
      σ ((D.ratio g : Fˣ) : F) * (Matrix.GeneralLinearGroup.map σ A) 1 1 := by
    change σ (A 0 0) = _
    rw [D.ratioFormula g A hA hc, map_mul]
    rfl
  change KPArch.action (Matrix.GeneralLinearGroup.map σ A) (toArch F (p, 0) i) = _
  rw [upper_action _ hi _ hu ha]
  apply Prod.ext
  · change σ ((D.ratio g : Fˣ) : F) * p.1 i + σ (A 0 1) / σ (A 1 1) =
      σ ((D.ratio g : Fˣ) : F) * p.1 i + σ (A 0 1 / A 1 1)
    rw [map_div₀]
  · change 0 + (p.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i + Real.log ‖σ _‖ =
      0 + ((p.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
        Real.log ((KPCusp.complexPlace F i) ((D.ratio g : Fˣ) : F)))
    rw [NumberField.InfinitePlace.norm_embedding_eq]
    ring

theorem raw_toArch_cross_injective (F : Type*) [Field F] [NumberField F] :
    Function.Injective (fun p : Cross F => toArch F (p, 0)) := by
  intro p q h
  apply Prod.ext
  · funext i
    exact congrArg Prod.fst (congrFun h i)
  · apply Subtype.ext
    funext i
    simpa [toArch] using congrArg Prod.snd (congrFun h i)

theorem raw_cross_action (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S) :
    ∃ α : S →* (Cross F ≃ₜ Cross F),
      ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
        ∀ p : Cross F, α g p =
          crossAffine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p := by
  obtain ⟨τ, hτ1, hτmul, hτformula⟩ :=
    KPCuspLogShape.upper_translation_cocycle F S D.upper D.E D.ratio D.ratioFormula
  let b : S → Cross F → Cross F := fun g =>
    crossAffine F hF D.E D.integralUnits (D.ratio g) (τ g)
  have hb1 (p : Cross F) : b 1 p = p := by
    ext i <;> simp [b, crossAffine, affine, embedding, hτ1]
  have hbmul (g k : S) (p : Cross F) : b (g * k) p = b g (b k p) := by
    apply Prod.ext
    · funext i
      dsimp [b, crossAffine, affine, embedding]
      simp only [map_mul, hτmul, Subgroup.coe_mul, Units.val_mul, map_add]
      ring
    · change p.2 + KPCuspLogShape.logarithm F hF D.E D.integralUnits
        (Additive.ofMul (D.ratio (g * k))) =
          (p.2 + KPCuspLogShape.logarithm F hF D.E D.integralUnits
            (Additive.ofMul (D.ratio k))) +
              KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio g))
      rw [map_mul, ofMul_mul, map_add]
      abel
  have hbcont (g : S) : Continuous (b g) := by
    unfold b crossAffine affine
    fun_prop
  let e : S → (Cross F ≃ₜ Cross F) := fun g => {
    toFun := b g
    invFun := b g⁻¹
    left_inv := fun p => by rw [← hbmul, inv_mul_cancel, hb1]
    right_inv := fun p => by rw [← hbmul, mul_inv_cancel, hb1]
    continuous_toFun := hbcont g
    continuous_invFun := hbcont g⁻¹ }
  refine ⟨{ toFun := e
            map_one' := by apply Homeomorph.ext; exact hb1
            map_mul' := fun g k => by apply Homeomorph.ext; exact hbmul g k }, ?_⟩
  intro g A hA _ p
  change b g p = _
  dsimp only [b]
  rw [hτformula g A hA]

theorem raw_cross_relation_iff (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (α : S →* (Cross F ≃ₜ Cross F))
    (hα : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      ∀ p : Cross F, α g p =
        crossAffine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p)
    (p q : Cross F) : crossRelation F S p q ↔ ∃ g : S, α g p = q := by
  have heq (g : S) (p : Cross F) :
      g • toArch F (p, 0) = toArch F (α g p, 0) := by
    obtain ⟨A, hA, hc⟩ := D.upper g g.property
    rw [hα g A hA hc]
    exact raw_actual_cross_action F hF S D g A hA hc p
  change MulAction.orbitRel S _ _ _ ↔ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, raw_toArch_cross_injective F ((heq g p).symm.trans hg)⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, heq g p⟩

end DedekindZetaZeroFree.KPCuspChart

end

end

section
noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.KPCuspChart

section
variable (F : Type*) [Field F] [NumberField F]
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
variable (α : S →* (Cross F ≃ₜ Cross F))
variable (hα : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F),
  Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
  ∀ p : Cross F, α g p =
    crossAffine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p)
include hα

theorem raw_cross_action_shape (g : S) (p : Cross F) :
    (α g p).2 = p.2 +
      KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio g)) := by
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  rw [hα g A hA hc]
  rfl

theorem raw_cross_action_translation (v : D.L) (p : Cross F) :
    α (D.inclusion (Multiplicative.ofAdd v)) p = (p.1 + embedding F v, p.2) := by
  obtain ⟨A, hA, hc⟩ := D.upper _ (D.inclusion (Multiplicative.ofAdd v)).property
  obtain ⟨_, hd, ht⟩ := D.unipotentFormula v A hA
  have hn : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hc, hz])
  have hv : A 0 1 / A 1 1 = (v : F) := by rw [ht, hd, mul_div_cancel_right₀ _ hn]
  have hr : D.ratio (D.inclusion (Multiplicative.ofAdd v)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← D.exact]
    exact ⟨_, rfl⟩
  rw [hα _ A hA hc, hv, hr]
  ext i <;> simp [crossAffine, affine, embedding]

theorem raw_cross_action_torus
    (β : D.E →* (Torus F D.L ≃ₜ Torus F D.L))
    (hβ : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : Horizontal F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      β (D.ratio g) (QuotientAddGroup.mk x) = QuotientAddGroup.mk
        (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
          embedding F (A 0 1 / A 1 1) i))
    (g : S) (p : Cross F) :
    (QuotientAddGroup.mk (α g p).1 : Torus F D.L) = β (D.ratio g) (QuotientAddGroup.mk p.1) := by
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  rw [hα g A hA hc, hβ g A p.1 hA hc]
  rfl

theorem raw_cross_eq_of_torus_eq (x y : Horizontal F) (b : Shape F)
    (h : (QuotientAddGroup.mk x : Torus F D.L) = QuotientAddGroup.mk y) :
    (Quotient.mk (crossRelation F S) (x, b) : CrossQuotient F S) = Quotient.mk _ (y, b) := by
  have hm : y - x ∈ translationLattice F D.L := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [QuotientAddGroup.mk_sub, h, sub_self]
  obtain ⟨v, hv, hvec⟩ := hm
  apply Quotient.sound
  apply (raw_cross_relation_iff F hF S D α hα _ _).mpr
  refine ⟨D.inclusion (Multiplicative.ofAdd (⟨v, hv⟩ : D.L)), ?_⟩
  rw [raw_cross_action_translation F hF S D α hα]
  apply Prod.ext
  · change x + embedding F v = y
    rw [hvec]
    abel
  · rfl

theorem raw_cross_quotient_open :
    IsOpenQuotientMap (Quotient.mk (crossRelation F S) : Cross F → CrossQuotient F S) := by
  letI := homeomorphAction α
  haveI : ContinuousConstSMul S (Cross F) := ⟨fun g => (α g).continuous⟩
  let e : Quotient (MulAction.orbitRel S (Cross F)) ≃ₜ CrossQuotient F S :=
    Homeomorph.Quotient.congrRight (fun p q => by
      rw [raw_cross_relation_iff F hF S D α hα]
      change p ∈ MulAction.orbit S q ↔ ∃ g : S, α g p = q
      rw [MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]
      rfl)
  exact e.isOpenQuotientMap.comp MulAction.isOpenQuotientMap_quotientMk

def rawProjection : CrossQuotient F S → Base F hF D.E D.integralUnits :=
  Quotient.lift (fun p : Cross F => QuotientAddGroup.mk p.2) (by
    intro p q hpq
    obtain ⟨g, rfl⟩ := (raw_cross_relation_iff F hF S D α hα p q).mp hpq
    rw [raw_cross_action_shape F hF S D α hα, QuotientAddGroup.mk_add]
    have hz : (QuotientAddGroup.mk
        (KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio g))) :
        Base F hF D.E D.integralUnits) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨Additive.ofMul (D.ratio g), rfl⟩
    rw [hz, add_zero])

@[simp] theorem rawProjection_mk (p : Cross F) :
    rawProjection F hF S D α hα (Quotient.mk _ p) = QuotientAddGroup.mk p.2 := rfl

theorem rawProjection_continuous : Continuous (rawProjection F hF S D α hα) :=
  (QuotientAddGroup.continuous_mk.comp continuous_snd).quotient_lift _

def rawLift : Torus F D.L × Shape F → CrossQuotient F S := fun p =>
  Quotient.liftOn p.1 (fun x => Quotient.mk _ (x, p.2)) (fun x y h =>
    raw_cross_eq_of_torus_eq F hF S D α hα x y p.2 (Quotient.sound h))

@[simp] theorem rawLift_mk (x : Horizontal F) (b : Shape F) :
    rawLift F hF S D α hα (QuotientAddGroup.mk x, b) = Quotient.mk _ (x, b) := rfl

theorem rawLift_open : IsOpenQuotientMap (rawLift F hF S D α hα) := by
  have hq := (QuotientAddGroup.isOpenQuotientMap_mk (N := translationLattice F D.L)).prodMap
    (IsOpenQuotientMap.id (X := Shape F))
  exact hq.of_comp_iff.mp (raw_cross_quotient_open F hF S D α hα)

theorem rawProjection_lift (z : Torus F D.L) (b : Shape F) :
    rawProjection F hF S D α hα (rawLift F hF S D α hα (z, b)) = QuotientAddGroup.mk b := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rfl

theorem rawLift_orbit_equivalence
    (β : D.E →* (Torus F D.L ≃ₜ Torus F D.L))
    (hβ : ∀ (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F) (x : Horizontal F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) → A 1 0 = 0 →
      β (D.ratio g) (QuotientAddGroup.mk x) = QuotientAddGroup.mk
        (fun i => embedding F ((D.ratio g : Fˣ) : F) i * x i +
          embedding F (A 0 1 / A 1 1) i))
    (z z' : Torus F D.L) (b b' : Shape F) :
    rawLift F hF S D α hα (z, b) = rawLift F hF S D α hα (z', b') ↔
      ∃ u : D.E, β u z = z' ∧ b' = b +
        KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z'
  simp only [rawLift_mk, Quotient.eq]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (raw_cross_relation_iff F hF S D α hα _ _).mp h
    refine ⟨D.ratio g, ?_, ?_⟩
    · rw [← raw_cross_action_torus F hF S D α hα β hβ g (x, b), hg]
    · simpa only [hg] using (raw_cross_action_shape F hF S D α hα g (x, b))
  · rintro ⟨u, hu, hb⟩
    obtain ⟨g, rfl⟩ := D.surjective u
    have htor : (QuotientAddGroup.mk (α g (x, b)).1 : Torus F D.L) = QuotientAddGroup.mk y := by
      rw [raw_cross_action_torus F hF S D α hα β hβ, hu]
    have hs : (α g (x, b)).2 = b' :=
      (raw_cross_action_shape F hF S D α hα g (x, b)).trans hb.symm
    have he := raw_cross_eq_of_torus_eq F hF S D α hα (α g (x, b)).1 y b' htor
    have he' : (Quotient.mk (crossRelation F S) (x, b) : CrossQuotient F S) =
        Quotient.mk _ (α g (x, b)) :=
      Quotient.sound ((raw_cross_relation_iff F hF S D α hα _ _).mpr ⟨g, rfl⟩)
    apply Quotient.exact
    exact he'.trans (by simpa only [← hs] using he)
end
end DedekindZetaZeroFree.KPCuspChart

end

end

section
noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPCuspChart

private theorem finite_local_charts {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty Y] [CompactSpace Y] (f : X → Y)
    (hf : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    ∃ (n : ℕ), 0 < n ∧ ∃ e : Fin n → OpenPartialHomeomorph X Y,
      (∀ i, f = e i) ∧ (∀ i, (e i).source.Nonempty) ∧
      (⋃ i, (e i).target) = Set.univ := by
  choose x hx using hs
  choose e he hfe using fun y => hf (x y)
  have hmem (y : Y) : y ∈ (e y).target := by
    have h := (e y).map_source (he y)
    rw [← hfe y, hx y] at h
    exact h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (e y).target)
    (fun y => (e y).open_target) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, hmem y⟩)
  have htn : t.Nonempty := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨z, hz, _⟩ := hy
    exact ⟨z, hz⟩
  let a : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, by simpa using Finset.card_pos.mpr htn,
    fun i => e (a i).val, fun i => hfe _, fun i => ⟨x _, he _⟩, ?_⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro y hy
  have hy' := ht hy
  simp only [Set.mem_iUnion] at hy'
  obtain ⟨z, hz, hyz⟩ := hy'
  exact Set.mem_iUnion.mpr ⟨a.symm ⟨z, hz⟩, by simpa using hyz⟩

structure RawShapeCover (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) where
  chartCount : ℕ
  positive_chartCount : 0 < chartCount
  shapeLift : Fin chartCount → Set (Shape F)
  open_shapeLift : ∀ i, IsOpen (shapeLift i)
  nonempty_shapeLift : ∀ i, (shapeLift i).Nonempty
  small_shapeLift : ∀ (i : Fin chartCount) (b b' : Shape F) (u : E),
    b ∈ shapeLift i → b' ∈ shapeLift i →
    b' = b + KPCuspLogShape.logarithm F hF E hE (Additive.ofMul u) →
    KPCuspLogShape.logarithm F hF E hE (Additive.ofMul u) = 0
  baseOpen : Fin chartCount → Set (Base F hF E hE)
  open_baseOpen : ∀ i, IsOpen (baseOpen i)
  baseOpen_formula : ∀ i, baseOpen i = QuotientAddGroup.mk '' shapeLift i
  cover : (⋃ i, baseOpen i) = Set.univ
  baseChart : ∀ i, shapeLift i ≃ₜ baseOpen i
  baseChart_formula : ∀ (i : Fin chartCount) (b : shapeLift i),
    (baseChart i b).val = QuotientAddGroup.mk b.val

theorem rawShapeCover_exists (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (hindex : (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex) :
    Nonempty (RawShapeCover F hF E hE) := by
  let Λ := KPCuspLogShape.logLattice F hF E hE
  obtain ⟨hdisc, _⟩ := (kp_cusp_log_unit_shape F hF E hE hindex).1
  letI := hdisc
  letI := (kp_cusp_log_unit_shape F hF E hE hindex).2.1
  let f : Shape F → Base F hF E hE := QuotientAddGroup.mk
  have hf : IsLocalHomeomorph f :=
    (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isLocalHomeomorph
  obtain ⟨n, hn, e, hfe, hne, hcover⟩ :=
    finite_local_charts f hf QuotientAddGroup.mk_surjective
  refine ⟨{
    chartCount := n
    positive_chartCount := hn
    shapeLift := fun i => (e i).source
    open_shapeLift := fun i => (e i).open_source
    nonempty_shapeLift := hne
    small_shapeLift := ?_
    baseOpen := fun i => (e i).target
    open_baseOpen := fun i => (e i).open_target
    baseOpen_formula := ?_
    cover := hcover
    baseChart := fun i => (e i).toHomeomorphSourceTarget
    baseChart_formula := ?_
  }⟩
  · intro i b b' u hb hb' h
    have hlog : KPCuspLogShape.logarithm F hF E hE (Additive.ofMul u) ∈
        Λ.toAddSubgroup := by
      exact AddMonoidHom.mem_range.mpr ⟨Additive.ofMul u, rfl⟩
    have heq : f b = f b' := by
      rw [h]
      change (QuotientAddGroup.mk b : Base F hF E hE) = QuotientAddGroup.mk (b + _)
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr hlog, add_zero]
    rw [hfe i] at heq
    have hbb := (e i).injOn hb hb' heq
    rw [← hbb] at h
    exact add_left_cancel (h.symm.trans (add_zero b).symm)
  · intro i
    change (e i).target = f '' (e i).source
    rw [hfe i]
    exact (e i).image_source_eq_target.symm
  · intro i b
    change e i b.val = f b.val
    rw [hfe i]

end DedekindZetaZeroFree.KPCuspChart

end

end

section
noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.KPCuspChart

theorem raw_coarse_eq_iff (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (L : AddSubgroup F) (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (β : E →* (Torus F L ≃ₜ Torus F L)) (z z' : Torus F L) :
    coarseProjection F hF L E hE β z = coarseProjection F hF L E hE β z' ↔
      ∃ u : kernelUnits F hF E hE, β u.val z = z' := by
  letI := homeomorphAction (β.comp (kernelUnits F hF E hE).subtype)
  change Quotient.mk _ z = Quotient.mk _ z' ↔ _
  rw [Quotient.eq]
  change z ∈ MulAction.orbit (kernelUnits F hF E hE) z' ↔ _
  rw [MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]
  rfl

theorem raw_coarse_open (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (L : AddSubgroup F) (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (β : E →* (Torus F L ≃ₜ Torus F L)) :
    IsOpenQuotientMap (coarseProjection F hF L E hE β) := by
  letI := homeomorphAction (β.comp (kernelUnits F hF E hE).subtype)
  haveI : ContinuousConstSMul (kernelUnits F hF E hE) (Torus F L) :=
    ⟨fun u => (β u.val).continuous⟩
  exact MulAction.isOpenQuotientMap_quotientMk

section
variable (F : Type*) [Field F] [NumberField F]
variable (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
variable (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
variable (β : D.E →* (Torus F D.L ≃ₜ Torus F D.L))
variable (π : CrossQuotient F S → Base F hF D.E D.integralUnits)
variable (l : Torus F D.L × Shape F → CrossQuotient F S)
variable (hlopen : IsOpenQuotientMap l)
variable (hπl : ∀ z b, π (l (z,b)) = QuotientAddGroup.mk b)
variable (heq : ∀ z z' b b', l (z,b) = l (z',b') ↔ ∃ u : D.E,
  β u z = z' ∧ b' = b + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u))
variable (V : Set (Shape F)) (W : Set (Base F hF D.E D.integralUnits))
variable (hV : IsOpen V) (hW : W = QuotientAddGroup.mk '' V)
variable (hsmall : ∀ b b' (u : D.E), b ∈ V → b' ∈ V →
  b' = b + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) →
  KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) = 0)
include hπl heq hW

 def chartLift : Torus F D.L × V → {c : CrossQuotient F S // π c ∈ W} :=
  fun p => ⟨l (p.1, p.2.val), by rw [hπl, hW]; exact ⟨p.2.val, p.2.property, rfl⟩⟩

include hlopen in
private theorem chartLift_surjective : Function.Surjective (chartLift F hF S D π l hπl V W hW) := by
  intro c
  obtain ⟨⟨z, b⟩, hz⟩ := hlopen.surjective c.val
  have hb : (QuotientAddGroup.mk b : Base F hF D.E D.integralUnits) ∈ W := by
    rw [← hπl z b, hz]; exact c.property
  rw [hW] at hb
  obtain ⟨b', hb', hbb⟩ := hb
  have hm : b' - b ∈ (KPCuspLogShape.logLattice F hF D.E D.integralUnits).toAddSubgroup := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [QuotientAddGroup.mk_sub, hbb, sub_self]
  obtain ⟨u, hu⟩ := hm
  have hbu : b' = b + KPCuspLogShape.logarithm F hF D.E D.integralUnits u := by rw [hu]; abel
  refine ⟨(β u.toMul z, ⟨b', hb'⟩), Subtype.ext ?_⟩
  change l (β u.toMul z, b') = c.val
  rw [← hz]
  exact ((heq z (β u.toMul z) b b').mpr ⟨u.toMul, rfl, hbu⟩).symm

include hsmall
 def coarseChartMap : CoarseFiber F hF D.L D.E D.integralUnits β × V →
    {c : CrossQuotient F S // π c ∈ W} := fun p =>
  Quotient.liftOn p.1 (fun z => chartLift F hF S D π l hπl V W hW (z,p.2)) (by
    intro z z' h
    have hc := (raw_coarse_eq_iff F hF D.L D.E D.integralUnits β z z').mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hc
    apply Subtype.ext
    exact (heq z z' p.2.val p.2.val).mpr ⟨u.val, hu, by rw [u.property, add_zero]⟩)

private theorem coarseChartMap_injective :
    Function.Injective (coarseChartMap F hF S D β π l hπl heq V W hW) := by
  rintro ⟨c,b⟩ ⟨c',b'⟩ h
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective c
  obtain ⟨z', rfl⟩ := Quotient.mk_surjective c'
  have hh : l (z,b.val) = l (z',b'.val) := congrArg Subtype.val h
  obtain ⟨u, hu, hb⟩ := (heq z z' b.val b'.val).mp hh
  have hz := hsmall b.val b'.val u b.property b'.property hb
  have hbb : b' = b := Subtype.ext (by simpa only [hz, add_zero] using hb)
  apply Prod.ext
  · exact (raw_coarse_eq_iff F hF D.L D.E D.integralUnits β z z').mpr ⟨⟨u,hz⟩,hu⟩
  · exact hbb.symm

include hlopen hV in

theorem raw_coarse_chart :
    ∃ e : CoarseFiber F hF D.L D.E D.integralUnits β × V ≃ₜ
      {c : CrossQuotient F S // π c ∈ W},
      ∀ (z : Torus F D.L) (b : V),
        (e (coarseProjection F hF D.L D.E D.integralUnits β z,b)).val = l (z,b.val) := by
  let f := coarseChartMap F hF S D β π l hπl heq V W hW
  let q : Torus F D.L × V → CoarseFiber F hF D.L D.E D.integralUnits β × V :=
    Prod.map (coarseProjection F hF D.L D.E D.integralUnits β) id
  have hq : IsOpenQuotientMap q := (raw_coarse_open F hF D.L D.E D.integralUnits β).prodMap .id
  have hcomp : f ∘ q = chartLift F hF S D π l hπl V W hW := rfl
  have hfcont : Continuous f := by
    apply hq.continuous_comp_iff.mp
    rw [hcomp]
    exact (hlopen.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hfopen : IsOpenMap f := by
    apply hq.isOpenMap_iff.mpr
    rw [hcomp]
    apply IsOpenMap.subtype_mk
    exact hlopen.isOpenMap.comp (IsOpenMap.id.prodMap hV.isOpenMap_subtype_val)
  have hfsurj : Function.Surjective f := by
    intro c
    obtain ⟨p, hp⟩ := chartLift_surjective F hF S D β π l hlopen hπl heq V W hW c
    exact ⟨q p,hp⟩
  let e := Equiv.ofBijective f ⟨coarseChartMap_injective F hF S D β π l hπl heq V W hW hsmall, hfsurj⟩
  exact ⟨e.toHomeomorphOfContinuousOpen hfcont hfopen, fun z b => rfl⟩
end
end DedekindZetaZeroFree.KPCuspChart

end

end

section
noncomputable section
open scoped Classical Matrix
open MeasureTheory
namespace DedekindZetaZeroFree.KPCuspChart

theorem finite_kernelUnits_of_logarithm
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    Finite (kernelUnits F hF E hE) := by
  letI := KPCuspLogShape.finite_logarithm_ker F hF E hE
  refine Finite.of_injective
    (fun u : kernelUnits F hF E hE =>
      (⟨Additive.ofMul u.val, u.property⟩ : (KPCuspLogShape.logarithm F hF E hE).ker)) ?_
  intro u v huv
  have h : Additive.ofMul u.val = Additive.ofMul v.val := congrArg Subtype.val huv
  exact Subtype.ext (Additive.ofMul.injective h)

theorem compact_torus_of_lattice
    (F : Type*) [Field F] [NumberField F]
    (L : AddSubgroup F)
    (hdisc : DiscreteTopology (translationLattice F L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F L).toIntSubmodule) :
    CompactSpace (Torus F L) := by
  letI := hdisc
  haveI := hlattice
  exact KPCuspLogShape.compact_quotient_of_isZLattice (translationLattice F L).toIntSubmodule

theorem compact_base_of_shape
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F)
    (hindex : (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex) :
    CompactSpace (Base F hF E hE) :=
  (DedekindZetaZeroFree.kp_cusp_log_unit_shape F hF E hE hindex).2.1

theorem finite_affine_bundle_atlas
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ExtensionData F S)
    (hdisc : DiscreteTopology (translationLattice F D.L).toIntSubmodule)
    (hlattice : letI := hdisc; IsZLattice ℝ (translationLattice F D.L).toIntSubmodule) :
    Nonempty (GeometryData F hF S D) := by
  obtain ⟨β, hβ⟩ := raw_ratio_torus_action F S D
  obtain ⟨α, hα⟩ := raw_cross_action F hF S D
  obtain ⟨C⟩ := rawShapeCover_exists F hF D.E D.integralUnits D.unitIndex
  let π := rawProjection F hF S D α hα
  let l := rawLift F hF S D α hα
  have hlopen : IsOpenQuotientMap l := rawLift_open F hF S D α hα
  have hπl : ∀ z b, π (l (z,b)) = QuotientAddGroup.mk b :=
    rawProjection_lift F hF S D α hα
  have heq := rawLift_orbit_equivalence F hF S D α hα β hβ
  choose e he using fun i => raw_coarse_chart F hF S D β π l hlopen hπl heq
    (C.shapeLift i) (C.baseOpen i) (C.open_shapeLift i) (C.baseOpen_formula i)
    (C.small_shapeLift i)
  let A : AtlasData F hF S D β := {
    projection := π
    continuous_projection := rawProjection_continuous F hF S D α hα
    projection_formula := fun p => rfl
    lift := l
    continuous_lift := hlopen.continuous
    lift_formula := fun x b => rfl
    orbit_equivalence := heq
    chartCount := C.chartCount
    positive_chartCount := C.positive_chartCount
    shapeLift := C.shapeLift
    open_shapeLift := C.open_shapeLift
    nonempty_shapeLift := C.nonempty_shapeLift
    small_shapeLift := C.small_shapeLift
    baseOpen := C.baseOpen
    open_baseOpen := C.open_baseOpen
    baseOpen_formula := C.baseOpen_formula
    cover := C.cover
    baseChart := C.baseChart
    baseChart_formula := C.baseChart_formula
    coarseChart := e
    coarseChart_formula := he
    transitions := by
      intro i j b b' hbb
      have hm : b'.val - b.val ∈
          (KPCuspLogShape.logLattice F hF D.E D.integralUnits).toAddSubgroup := by
        apply (QuotientAddGroup.eq_zero_iff _).mp
        rw [QuotientAddGroup.mk_sub, hbb, sub_self]
      obtain ⟨u, hu⟩ := hm
      obtain ⟨g, hg⟩ := D.surjective u.toMul
      have hb : b'.val = b.val +
          KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio g)) := by
        rw [hg]
        change b'.val = b.val + KPCuspLogShape.logarithm F hF D.E D.integralUnits u
        rw [hu]
        abel
      exact ⟨g, hb, fun z => (heq z (β (D.ratio g) z) b.val b'.val).mpr
        ⟨D.ratio g, rfl, hb⟩⟩ }
  letI := compact_torus_of_lattice F D.L hdisc hlattice
  have hcompact : CompactSpace (CrossQuotient F S) := by
    obtain ⟨_, _, _, _, _, B, _, hB, hcover, _⟩ :=
      kp_cusp_log_unit_shape F hF D.E D.integralUnits D.unitIndex
    have hc := (isCompact_univ (X := Torus F D.L)).prod hB
    have hfull : l '' ((Set.univ : Set (Torus F D.L)) ×ˢ parallelepiped B) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro c
      obtain ⟨⟨z,b⟩, rfl⟩ := hlopen.surjective c
      obtain ⟨u, hu⟩ := hcover b
      have hshift : b - KPCuspLogShape.logarithm F hF D.E D.integralUnits
          (Additive.ofMul u) = b +
            KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u⁻¹) := by
        change b - KPCuspLogShape.logarithm F hF D.E D.integralUnits
          (Additive.ofMul u) = b +
            KPCuspLogShape.logarithm F hF D.E D.integralUnits (-Additive.ofMul u)
        rw [map_neg, sub_eq_add_neg]
      refine ⟨(β u⁻¹ z, b - KPCuspLogShape.logarithm F hF D.E D.integralUnits
        (Additive.ofMul u)), ⟨Set.mem_univ _, hu⟩, ?_⟩
      exact ((heq z (β u⁻¹ z) b _).mpr ⟨u⁻¹, rfl, hshift⟩).symm
    exact ⟨hfull ▸ hc.image hlopen.continuous⟩
  exact ⟨{
    compact_torus := inferInstance
    compact_base := compact_base_of_shape F hF D.E D.integralUnits D.unitIndex
    finite_isotropy := finite_kernelUnits_of_logarithm F hF D.E D.integralUnits
    torusAction := β
    torusAction_formula := hβ
    atlas := A
    compact_cross := hcompact
    crossAction := α
    crossAction_formula := hα }⟩

end DedekindZetaZeroFree.KPCuspChart

end

end
