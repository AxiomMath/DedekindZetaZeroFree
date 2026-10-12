module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualBorelRetraction
open KPGlobalTorusFunctionData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def upper (x : Adeles F) : KPAdelicCoverRestrictedProduct.AdelicGL2 F :=
  Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
theorem upper_entries (x : Adeles F) (i j : Fin 2) :
    upper F x i j = (!![1, x; 0, 1]) i j := by
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.transvection]

theorem projected_root (x : Adeles F) :
    KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) (upper F x) := by
  change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
    (rootTuple F ζ hζ x)) = _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have he : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v
      ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
        (rootTuple F ζ hζ x)) i j) =
      KPAdelicCoverRestrictedProduct.adeleEval F v (upper F x i j) := by
    intro v
    have h := congrArg (fun A : KPLocalCover.LocalGL2 F v => A i j)
      (KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ (rootTuple F ζ hζ x) v)
    change KPAdelicCoverRestrictedProduct.adeleEval F v
      ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ (rootTuple F ζ hζ x)) i j) = _ at h
    rw [h]
    fin_cases i <;> fin_cases j <;>
      simp [rootTuple, KPStandardLocalRootLifts.N, KPLocalCover.projection_apply,
        KPLocalCover.sectionMap, KubotaRankTwo.n, upper_entries]
  apply Prod.ext
  · funext w; exact he (Sum.inl w)
  · apply Subtype.ext; funext q; exact he (Sum.inr q)

theorem root_mem_borel (x : Adeles F) : N F ζ hζ x ∈ borel F ζ hζ := by
  refine ⟨upper F x, (projected_root F ζ hζ x).symm, ?_⟩
  simp [upper_entries]

def torusInBorel : E F ζ hζ →* borel F ζ hζ :=
  Subgroup.inclusion (by
    intro g hg
    obtain ⟨A, hA, h10, _⟩ := hg
    exact ⟨A, hA, h10⟩)

def rootInBorel : Multiplicative (Adeles F) →* borel F ζ hζ :=
  (Nhom F ζ hζ).codRestrict _ (fun x => root_mem_borel F ζ hζ x.toAdd)

private theorem root_torus_zero (x : Adeles F) (hx : N F ζ hζ x ∈ E F ζ hζ) : x = 0 := by
  obtain ⟨A, hA, h10, h01⟩ := hx
  rw [projected_root] at hA
  obtain ⟨u, hu⟩ := QuotientGroup.eq.mp hA
  have he : upper F x = A * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) u = A⁻¹ * upper F x at hu
    rw [hu]; group
  have h := congrArg (fun B : KPAdelicCoverRestrictedProduct.AdelicGL2 F => B 0 1) he
  simpa [upper_entries, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, h01] using h

private theorem correction_trivial {V : Type*} [AddCommGroup V] [Module ℚ V]
    {G₀ H : Type*} [Group G₀] [Group H] (π : G₀ →* H) [Finite π.ker]
    (hc : π.ker ≤ Subgroup.center G₀)
    (f g : Multiplicative V →* G₀) (he : ∀ x, π (f x) = π (g x)) (x : V) :
    f (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd x) := by
  letI : CommGroup π.ker :=
    { (inferInstance : Group π.ker) with
      mul_comm := by
        intro a b
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hc a.property) b.val).symm }
  have hk (y : Multiplicative V) : f y * (g y)⁻¹ ∈ π.ker := by simp [he y]
  let d : Multiplicative V →* π.ker :=
    { toFun := fun y => ⟨f y * (g y)⁻¹, hk y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hcomm := Subgroup.mem_center_iff.mp (hc (hk b)) (g a)⁻¹
        simp only [map_mul, mul_inv_rev]
        calc
          f a * f b * ((g b)⁻¹ * (g a)⁻¹) = f a * (f b * (g b)⁻¹) * (g a)⁻¹ := by group
          _ = f a * (g a)⁻¹ * (f b * (g b)⁻¹) := by
            rw [mul_assoc, ← hcomm, ← mul_assoc] }
  exact mul_inv_eq_one.mp (congrArg Subtype.val (FiniteCentralBorel.finite_character_trivial d x))

theorem torus_conjugates_root (t : E F ζ hζ) (x : Adeles F) :
    t.val * N F ζ hζ x * t.val⁻¹ = N F ζ hζ ((p F ζ hζ t : Adeles F) * x) := by
  letI : Module ℚ (Adeles F) := Module.compHom (Adeles F) (algebraMap ℚ F)
  let π := KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
  have hfin : Finite π.ker := by
    rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
    exact Set.finite_range _ |>.to_subtype
  letI := hfin
  have hc : π.ker ≤ Subgroup.center (G F ζ hζ) := by
    rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
    exact KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
  let f := (MulAut.conj t.val).toMonoidHom.comp (Nhom F ζ hζ)
  let g := (Nhom F ζ hζ).comp
    (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft (p F ζ hζ t : Adeles F)))
  apply correction_trivial π hc f g
  intro y
  change π (t.val * N F ζ hζ y.toAdd * t.val⁻¹) =
    π (N F ζ hζ ((p F ζ hζ t : Adeles F) * y.toAdd))
  obtain ⟨A, hA, h10, h01⟩ := t.property
  have hr := ratio_formula F
    ⟨π t.val, t.property⟩ A hA h10 h01
  have he : A * upper F y.toAdd = upper F ((p F ζ hζ t : Adeles F) * y.toAdd) * A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        upper_entries, h10, h01]
    have hratio : (p F ζ hζ t : Adeles F) =
        ((diagonal_entries_units F A h10 h01).1.unit : Adeles F) *
        ((diagonal_entries_units F A h10 h01).2.unit⁻¹ : (Adeles F)ˣ) := hr
    rw [hratio]
    have h00 := (diagonal_entries_units F A h10 h01).1.unit_spec
    have h11 := (diagonal_entries_units F A h10 h01).2.unit_spec
    calc
      A 0 0 * y.toAdd = ((diagonal_entries_units F A h10 h01).1.unit : Adeles F) * y.toAdd :=
        congrArg (fun a : Adeles F => a * y.toAdd) h00.symm
      _ = ((diagonal_entries_units F A h10 h01).1.unit : Adeles F) *
          ((diagonal_entries_units F A h10 h01).2.unit⁻¹ : (Adeles F)ˣ) * y.toAdd *
          ((diagonal_entries_units F A h10 h01).2.unit : Adeles F) := by
        let u := (diagonal_entries_units F A h10 h01).1.unit
        let v := (diagonal_entries_units F A h10 h01).2.unit
        change (u : Adeles F) * y.toAdd = (u : Adeles F) * (v⁻¹ : (Adeles F)ˣ) * y.toAdd * (v : Adeles F)
        symm
        calc
          (u : Adeles F) * (v⁻¹ : (Adeles F)ˣ) * y.toAdd * (v : Adeles F) =
              (u : Adeles F) * y.toAdd * ((v⁻¹ : (Adeles F)ˣ) * (v : Adeles F)) := by ring
          _ = _ := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = _ := congrArg (fun a : Adeles F => _ * _ * y.toAdd * a) h11
  dsimp only [π]
  simp only [map_mul, map_inv, projected_root, ← hA]
  have hh := congrArg (QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)) he
  simp only [map_mul] at hh
  rw [hh, mul_assoc, mul_inv_cancel, mul_one]

private theorem factor_unique (t u : E F ζ hζ) (x y : Adeles F)
    (h : t.val * N F ζ hζ x = u.val * N F ζ hζ y) : t = u := by
  have hn : N F ζ hζ (-y) = (N F ζ hζ y)⁻¹ :=
    (Nhom F ζ hζ).map_inv (Multiplicative.ofAdd y)
  have he : N F ζ hζ (x - y) = t.val⁻¹ * u.val := by
    rw [sub_eq_add_neg, N_add, hn]
    calc
      _ = t.val⁻¹ * (t.val * N F ζ hζ x) * (N F ζ hζ y)⁻¹ := by group
      _ = _ := by rw [h]; group
  have hx : x - y = 0 := root_torus_zero F ζ hζ _
    (he ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ t.property) u.property)
  have hxy : x = y := sub_eq_zero.mp hx
  rw [hxy] at h
  exact Subtype.ext (mul_right_cancel h)

def factor (b : borel F ζ hζ) : E F ζ hζ × Adeles F :=
  ⟨(KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ b).choose,
    (KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ b).choose_spec.choose⟩
 theorem factor_spec (b : borel F ζ hζ) :
    b.val = (factor F ζ hζ b).1.val * N F ζ hζ (factor F ζ hζ b).2 :=
  (KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ b).choose_spec.choose_spec
theorem factor_torus (b : borel F ζ hζ) (t : E F ζ hζ) (x : Adeles F)
    (h : b.val = t.val * N F ζ hζ x) : (factor F ζ hζ b).1 = t :=
  factor_unique F ζ hζ _ _ _ _ ((factor_spec F ζ hζ b).symm.trans h)

def retraction : borel F ζ hζ →* E F ζ hζ where
  toFun b := (factor F ζ hζ b).1
  map_one' := factor_torus F ζ hζ 1 1 0 (by
    change (1 : G F ζ hζ) = 1 * N F ζ hζ 0
    have h0 : N F ζ hζ 0 = 1 := (Nhom F ζ hζ).map_one
    rw [h0, mul_one])
  map_mul' b c := by
    let t := (factor F ζ hζ b).1
    let u := (factor F ζ hζ c).1
    let x := (factor F ζ hζ b).2
    let y := (factor F ζ hζ c).2
    let z : Adeles F := (p F ζ hζ u⁻¹ : Adeles F) * x
    apply factor_torus F ζ hζ (b * c) (t * u) (z + y)
    have hc : u.val⁻¹ * N F ζ hζ x * u.val = N F ζ hζ z :=
      by simpa only [Subgroup.coe_inv, inv_inv] using torus_conjugates_root F ζ hζ u⁻¹ x
    have hcomm : N F ζ hζ x * u.val = u.val * N F ζ hζ z := by
      rw [← hc]; group
    change b.val * c.val = (t.val * u.val) * N F ζ hζ (z + y)
    rw [factor_spec F ζ hζ b, factor_spec F ζ hζ c, N_add]
    change (t.val * N F ζ hζ x) * (u.val * N F ζ hζ y) = _
    calc
      _ = t.val * (N F ζ hζ x * u.val) * N F ζ hζ y := by group
      _ = _ := by rw [hcomm]; group

@[simp] theorem retraction_torus (t : E F ζ hζ) :
    retraction F ζ hζ (torusInBorel F ζ hζ t) = t := by
  apply factor_torus F ζ hζ _ t 0
  change t.val = t.val * N F ζ hζ 0
  have h0 : N F ζ hζ 0 = 1 := (Nhom F ζ hζ).map_one
  rw [h0, mul_one]

@[simp] theorem retraction_root (x : Multiplicative (Adeles F)) :
    retraction F ζ hζ (rootInBorel F ζ hζ x) = 1 := by
  apply factor_torus F ζ hζ _ 1 x.toAdd
  change N F ζ hζ x.toAdd = 1 * N F ζ hζ x.toAdd
  rw [one_mul]

end DedekindZetaZeroFree.ActualBorelRetraction

end
