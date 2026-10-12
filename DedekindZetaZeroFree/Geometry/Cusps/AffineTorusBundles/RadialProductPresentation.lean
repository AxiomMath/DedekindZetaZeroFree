module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EquivariantAffineUnitCharts

@[expose] public section

section
noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.KPCuspCharts

def coordinatesAction (F : Type*) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : S →* (Coordinates F ≃ₜ Coordinates F) where
  toFun g := ((toArchHomeomorph F hd).trans (projectiveHomeomorph F g.val)).trans
    (toArchHomeomorph F hd).symm
  map_one' := by
    apply Homeomorph.ext
    intro p
    change (toArchHomeomorph F hd).symm
      ((↑(1 : S) : KPCuspArithmetic.PGL2 F) • (toArchHomeomorph F hd p)) = p
    rw [Subgroup.coe_one]
    simp
  map_mul' g k := by
    apply Homeomorph.ext
    intro p
    change (toArchHomeomorph F hd).symm ((g.val * k.val) • (toArchHomeomorph F hd p)) =
      (toArchHomeomorph F hd).symm (g.val • ((toArchHomeomorph F hd)
        ((toArchHomeomorph F hd).symm (k.val • ((toArchHomeomorph F hd) p)))))
    simp only [Homeomorph.apply_symm_apply, mul_smul]

theorem coordinatesAction_formula (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Coordinates F) :
    coordinatesAction F (positive_dimension F hF) S g p =
      affine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p := by
  apply (toArchHomeomorph F (positive_dimension F hF)).injective
  change (toArchHomeomorph F (positive_dimension F hF))
    ((toArchHomeomorph F (positive_dimension F hF)).symm
      (KPCuspSiegel.action F g.val (toArch F p))) = _
  rw [Homeomorph.apply_symm_apply]
  exact actual_affine_action F hF S D g A hA hc p

theorem coordinatesAction_radial (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (p : Coordinates F) :
    (coordinatesAction F (positive_dimension F hF) S g p).2 = p.2 := by
  obtain ⟨A, hA, hc⟩ := D.upper g.val g.property
  rw [coordinatesAction_formula F hF S D g A hA hc]
  rfl

def actualCrossHomeomorph (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) : Cross F ≃ₜ Cross F where
  toFun p := (coordinatesAction F (positive_dimension F hF) S g (p, 0)).1
  invFun p := (coordinatesAction F (positive_dimension F hF) S g⁻¹ (p, 0)).1
  left_inv p := by
    have he : ((coordinatesAction F (positive_dimension F hF) S g (p, 0)).1, 0) =
      coordinatesAction F (positive_dimension F hF) S g (p, 0) := by
      refine Prod.ext (by rfl) ?_
      exact (coordinatesAction_radial F hF S D g (p, 0)).symm
    change (coordinatesAction F (positive_dimension F hF) S g⁻¹
      ((coordinatesAction F (positive_dimension F hF) S g (p, 0)).1, 0)).1 = p
    rw [he]
    have h := congrArg (fun f : Coordinates F ≃ₜ Coordinates F => f (p, 0))
      ((coordinatesAction F (positive_dimension F hF) S).map_mul g⁻¹ g).symm
    simpa using congrArg Prod.fst h
  right_inv p := by
    have he : ((coordinatesAction F (positive_dimension F hF) S g⁻¹ (p, 0)).1, 0) =
      coordinatesAction F (positive_dimension F hF) S g⁻¹ (p, 0) := by
      refine Prod.ext (by rfl) ?_
      exact (coordinatesAction_radial F hF S D g⁻¹ (p, 0)).symm
    change (coordinatesAction F (positive_dimension F hF) S g
      ((coordinatesAction F (positive_dimension F hF) S g⁻¹ (p, 0)).1, 0)).1 = p
    rw [he]
    have h := congrArg (fun f : Coordinates F ≃ₜ Coordinates F => f (p, 0))
      ((coordinatesAction F (positive_dimension F hF) S).map_mul g g⁻¹).symm
    simpa using congrArg Prod.fst h
  continuous_toFun := (coordinatesAction F (positive_dimension F hF) S g).continuous.fst.comp
    (continuous_id.prodMk continuous_const)
  continuous_invFun := (coordinatesAction F (positive_dimension F hF) S g⁻¹).continuous.fst.comp
    (continuous_id.prodMk continuous_const)

def actualCrossAction (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) :
    S →* (Cross F ≃ₜ Cross F) where
  toFun := actualCrossHomeomorph F hF S D
  map_one' := by
    apply Homeomorph.ext
    intro p
    change (coordinatesAction F (positive_dimension F hF) S 1 (p, 0)).1 = p
    rw [map_one]
    rfl
  map_mul' g k := by
    apply Homeomorph.ext
    intro p
    change (coordinatesAction F (positive_dimension F hF) S (g * k) (p, 0)).1 =
      (coordinatesAction F (positive_dimension F hF) S g
        ((coordinatesAction F (positive_dimension F hF) S k (p, 0)).1, 0)).1
    have he : ((coordinatesAction F (positive_dimension F hF) S k (p, 0)).1, 0) =
      coordinatesAction F (positive_dimension F hF) S k (p, 0) := by
      refine Prod.ext (by rfl) ?_
      exact (coordinatesAction_radial F hF S D k (p, 0)).symm
    rw [he, map_mul]
    rfl

theorem actualCrossAction_formula (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (p : Cross F) :
    actualCrossAction F hF S D g p =
      crossAffine F hF D.E D.integralUnits (D.ratio g) (A 0 1 / A 1 1) p := by
  exact congrArg Prod.fst (coordinatesAction_formula F hF S D g A hA hc (p, 0))

theorem coordinatesAction_product (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (p : Coordinates F) :
    coordinatesAction F (positive_dimension F hF) S g p =
      (actualCrossAction F hF S D g p.1, p.2) := by
  obtain ⟨A, hA, hc⟩ := D.upper g.val g.property
  rw [coordinatesAction_formula F hF S D g A hA hc,
    actualCrossAction_formula F hF S D g A hA hc]
  rfl

theorem actualCrossAction_toArch (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (g : S) (p : Cross F) :
    toArch F (actualCrossAction F hF S D g p, 0) =
      KPCuspSiegel.action F g.val (toArch F (p, 0)) := by
  rw [← coordinatesAction_product F hF S D g (p, 0)]
  exact (toArchHomeomorph F (positive_dimension F hF)).apply_symm_apply _

theorem crossRelation_actualCrossAction (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) :
    letI := homeomorphAction (actualCrossAction F hF S D)
    crossRelation F S = MulAction.orbitRel S (Cross F) := by
  letI := homeomorphAction (actualCrossAction F hF S D)
  apply Setoid.ext
  intro p r
  change MulAction.orbitRel S _ (toArch F (p, 0)) (toArch F (r, 0)) ↔
    MulAction.orbitRel S _ p r
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change actualCrossAction F hF S D g r = p
    have he : toArch F (actualCrossAction F hF S D g r, 0) = toArch F (p, 0) := by
      rw [actualCrossAction_toArch F hF S D]
      exact hg
    exact congrArg Prod.fst ((toArchHomeomorph F (positive_dimension F hF)).injective he)
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change KPCuspSiegel.action F g.val (toArch F (r, 0)) = toArch F (p, 0)
    rw [← actualCrossAction_toArch F hF S D]
    exact congrArg (fun c => toArch F (c, 0)) hg
end DedekindZetaZeroFree.KPCuspCharts

end

end

section
noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree.KPCuspCharts

theorem totalRelation_product (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (p r : Coordinates F) :
    totalRelation F S p r ↔ crossRelation F S p.1 r.1 ∧ p.2 = r.2 := by
  have hi := (toArchHomeomorph F (positive_dimension F hF)).injective
  have he (g : S) (p : Coordinates F) :
      KPCuspSiegel.action F g.val (toArch F p) =
        toArch F (actualCrossAction F hF S D g p.1, p.2) := by
    rw [← coordinatesAction_product F hF S D g p]
    exact ((toArchHomeomorph F (positive_dimension F hF)).apply_symm_apply _).symm
  change MulAction.orbitRel S _ (toArch F p) (toArch F r) ↔ _
  rw [crossRelation_actualCrossAction F hF S D]
  letI := homeomorphAction (actualCrossAction F hF S D)
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hpr : (actualCrossAction F hF S D g r.1, r.2) = p := hi ((he g r).symm.trans hg)
    refine ⟨⟨g, ?_⟩, (congrArg Prod.snd hpr).symm⟩
    change actualCrossAction F hF S D g r.1 = p.1
    have hfst := congrArg (fun a : Coordinates F => a.1) hpr
    exact hfst
  · rintro ⟨⟨g, hg⟩, ht⟩
    refine ⟨g, ?_⟩
    change KPCuspSiegel.action F g.val (toArch F r) = toArch F p
    rw [he]
    exact congrArg (toArch F) (Prod.ext hg ht.symm)

def actualRadialPresentation (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) :
    CrossQuotient F S × ℝ ≃ₜ TotalQuotient F S where
  toFun p := Quotient.lift (fun x : Cross F => Quotient.mk (totalRelation F S) (x, p.2))
    (fun x y h => Quotient.sound ((totalRelation_product F hF S D _ _).mpr ⟨h, rfl⟩)) p.1
  invFun := Quotient.lift (fun p : Coordinates F => (Quotient.mk (crossRelation F S) p.1, p.2))
    (fun p r h => by
      obtain ⟨hc, ht⟩ := (totalRelation_product F hF S D p r).mp h
      exact Prod.ext (Quotient.sound hc) ht)
  left_inv := by
    rintro ⟨p, t⟩
    induction p using Quotient.inductionOn
    rfl
  right_inv := by
    intro p
    induction p using Quotient.inductionOn
    rfl
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_left
    exact continuous_quotient_mk'
  continuous_invFun := by
    apply continuous_quot_lift
    exact (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd

@[simp] theorem actualRadialPresentation_formula (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (p : Cross F) (t : ℝ) :
    actualRadialPresentation F hF S D (Quotient.mk _ p, t) = Quotient.mk _ (p, t) := rfl

theorem highRelation_product (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) (T : ℝ)
    (p r : {p : Coordinates F // T < p.2}) :
    highRelation F S T p r ↔ crossRelation F S p.val.1 r.val.1 ∧ p.val.2 = r.val.2 :=
  totalRelation_product F hF S D p.val r.val

def actualHighPresentation (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S) (T : ℝ) :
    CrossQuotient F S × Set.Ioi T ≃ₜ HighQuotient F S T where
  toFun p := Quotient.lift (fun x : Cross F => Quotient.mk (highRelation F S T)
      ⟨(x, p.2.val), p.2.property⟩)
    (fun x y h => Quotient.sound ((highRelation_product F hF S D T _ _).mpr ⟨h, rfl⟩)) p.1
  invFun := Quotient.lift (fun p : {p : Coordinates F // T < p.2} =>
    (Quotient.mk (crossRelation F S) p.val.1, (⟨p.val.2, p.property⟩ : Set.Ioi T)))
    (fun p r h => by
      obtain ⟨hc, ht⟩ := (highRelation_product F hF S D T p r).mp h
      exact Prod.ext (Quotient.sound hc) (Subtype.ext ht))
  left_inv := by
    rintro ⟨p, t⟩
    induction p using Quotient.inductionOn
    rfl
  right_inv := by
    intro p
    induction p using Quotient.inductionOn
    rfl
  continuous_toFun := by
    letI : LocallyCompactSpace (Set.Ioi T) := isOpen_Ioi.locallyCompactSpace
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_left
    apply continuous_quotient_mk'.comp
    exact (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := by
    apply continuous_quot_lift
    exact (continuous_quotient_mk'.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

@[simp] theorem actualHighPresentation_formula (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : ParabolicData F S)
    (T : ℝ) (p : Cross F) (t : Set.Ioi T) :
    actualHighPresentation F hF S D T (Quotient.mk _ p, t) =
      Quotient.mk _ ⟨(p, t.val), t.property⟩ := rfl
end DedekindZetaZeroFree.KPCuspCharts

end

end
