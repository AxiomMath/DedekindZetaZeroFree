module

public import DedekindZetaZeroFree.Adeles.Quotients.ProperDoubleQuotientTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCompactLevels
public import DedekindZetaZeroFree.Adeles.Lattices.RationalMatrices

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotient
open Topology
open scoped NumberField Classical

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev DoubleQuotient (Γ K : Subgroup G) := DoubleCoset.Quotient (Γ : Set G) (K : Set G)

instance (Γ K : Subgroup G) : TopologicalSpace (DoubleQuotient Γ K) :=
  inferInstanceAs (TopologicalSpace (_root_.Quotient _))

end Generic

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev actualCover := KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ
abbrev rationalSplit := KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
abbrev rationalSubgroup : Subgroup (actualCover F ζ hζ) := (rationalSplit F ζ hζ).range

def finiteTuples : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) where
  carrier := {g | ∀ w : NumberField.InfinitePlace F, g (Sum.inl w) = 1}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh w; simp [hg w, hh w]
  inv_mem' := by intro g hg w; simp [hg w]

def finiteSubgroup : Subgroup (actualCover F ζ hζ) :=
  (finiteTuples F ζ hζ).map
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

abbrev FiniteLevel := CompactOpenLevel (finiteSubgroup F ζ hζ)

def levelSubgroup (U : FiniteLevel F ζ hζ) : Subgroup (actualCover F ζ hζ) :=
  U.toOpenSubgroup.toSubgroup.map (finiteSubgroup F ζ hζ).subtype

abbrev centreMap := KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ

def rightSubgroup (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    Subgroup (actualCover F ζ hζ) :=
  if geometric then levelSubgroup F ζ hζ U ⊔ (centreMap F ζ hζ).range
  else levelSubgroup F ζ hζ U

abbrev actualLevelSpace (U : FiniteLevel F ζ hζ) (geometric : Bool) :=
  DoubleQuotient (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric)

theorem actual_cover_lc_t2_group :
    T2Space (actualCover F ζ hζ) ∧ LocallyCompactSpace (actualCover F ζ hζ) ∧
      IsTopologicalGroup (actualCover F ζ hζ) := by
  exact ⟨(KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1,
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1,
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1⟩

theorem actual_cover_secondCountable : SecondCountableTopology (actualCover F ζ hζ) := by
  exact ActualQuotientTopology.Cover.rawCover_secondCountable F ζ hζ

abbrev ArchGroup := NumberField.InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ

def glArchProjection : KPAdelicCoverRestrictedProduct.AdelicGL2 F →* ArchGroup F where
  toFun g w := Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map
      ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))) g)
  map_one' := by ext w; simp
  map_mul' := by intro g h; ext w; simp

 theorem scalars_le_arch_kernel : KPAdelicCoverRestrictedProduct.scalarSubgroup F ≤
    (glArchProjection F ζ hζ).ker := by
  rintro g ⟨u, rfl⟩
  ext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
  rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.ProjGenLinGroup.mk_scalar]

def archProjection : actualCover F ζ hζ →* ArchGroup F :=
  (QuotientGroup.lift (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (glArchProjection F ζ hζ) (scalars_le_arch_kernel F ζ hζ)).comp
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)

end DedekindZetaZeroFree.ActualQuotient

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualQuotient
open Topology
open scoped NumberField Classical

section Generic
variable {G : Type*} [Group G] [TopologicalSpace G]

abbrev doubleQuotientMap (Γ K : Subgroup G) : G → DoubleQuotient Γ K :=
  DoubleCoset.mk Γ K

def actionCorrespondence (Γ K : Subgroup G) : (Γ × K) × G → G × G :=
  fun p => ((p.1.1 : G) * p.2 * (p.1.2 : G)⁻¹, p.2)

def CompactTransporters (Γ K : Subgroup G) : Prop :=
  ∀ C : Set G, IsCompact C →
    {γ : G | γ ∈ Γ ∧ ∃ x ∈ C, ∃ y ∈ C, ∃ k ∈ K, γ = y * k * x⁻¹}.Finite

theorem compact_transporters [IsTopologicalGroup G] [T2Space G]
    (Γ K : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (dΓ : IsDiscrete (Γ : Set G)) (hK : IsCompact (K : Set G)) :
    CompactTransporters Γ K := by
  intro C hC
  open scoped Pointwise in
    have hcomp : IsCompact ((Γ : Set G) ∩ (C * (K : Set G) * C⁻¹)) :=
      ((hC.mul hK).mul hC.inv).inter_left hΓ
    have hfin := hcomp.finite (dΓ.mono Set.inter_subset_left)
    apply hfin.subset
    rintro γ ⟨hγ, x, hx, y, hy, k, hk, rfl⟩
    refine ⟨hγ, ?_⟩
    exact Set.mem_mul.mpr ⟨y * k, Set.mem_mul.mpr ⟨y, hy, k, hk, rfl⟩,
      x⁻¹, by simpa using hx, rfl⟩

theorem proper_actionCorrespondence [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ K : Subgroup G)
    (hΓ : IsClosed (Γ : Set G)) (dΓ : IsDiscrete (Γ : Set G))
    (hK : IsCompact (K : Set G)) : IsProperMap (actionCorrespondence Γ K) := by
  exact ActualQuotientTopology.Generic.proper_rawActionCorrespondence Γ K hΓ dΓ hK

theorem lcsc_polish (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] : PolishSpace Y := by
  exact ActualQuotientTopology.Generic.locallyCompact_secondCountable_polish Y

structure TopologyCertificate (Γ K : Subgroup G) : Prop where
  proper : IsProperMap (actionCorrespondence Γ K)
  locallyCompact : LocallyCompactSpace (DoubleQuotient Γ K)
  hausdorff : T2Space (DoubleQuotient Γ K)
  secondCountable : SecondCountableTopology (DoubleQuotient Γ K)
  polish : PolishSpace (DoubleQuotient Γ K)
  continuous : Continuous (doubleQuotientMap Γ K)
  openMap : IsOpenMap (doubleQuotientMap Γ K)
  quotientMap : IsQuotientMap (doubleQuotientMap Γ K)

theorem proper_doubleQuotient_certificate [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ K : Subgroup G)
    (hp : IsProperMap (actionCorrespondence Γ K)) : TopologyCertificate Γ K := by
  obtain ⟨hlc, ht2, hsc, hc, ho, hq⟩ :=
    ActualQuotientTopology.Generic.proper_rawDoubleQuotient_topology Γ K hp
  letI : LocallyCompactSpace (DoubleQuotient Γ K) := hlc
  letI : T2Space (DoubleQuotient Γ K) := ht2
  letI : SecondCountableTopology (DoubleQuotient Γ K) := hsc
  exact ⟨hp, hlc, ht2, hsc, lcsc_polish (DoubleQuotient Γ K), hc, ho, hq⟩
end Generic

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev actualLevelMap (U : FiniteLevel F ζ hζ) (geometric : Bool) :=
  doubleQuotientMap (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric)

theorem actual_rational_closed_discrete :
    IsClosed (rationalSubgroup F ζ hζ : Set (actualCover F ζ hζ)) ∧
      IsDiscrete (rationalSubgroup F ζ hζ : Set (actualCover F ζ hζ)) := by
  have h := ActualQuotientTopology.Arithmetic.rawRational_arithmetic_certificate F ζ hζ
  exact ⟨h.1, h.2.1⟩

theorem actual_rational_arch_injective :
    Function.Injective ((archProjection F ζ hζ).comp (rationalSubgroup F ζ hζ).subtype) := by
  exact (ActualQuotientTopology.Arithmetic.rawRational_arithmetic_certificate F ζ hζ).2.2

open scoped Pointwise in

theorem actual_right_compact (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    IsCompact (rightSubgroup F ζ hζ U geometric : Set (actualCover F ζ hζ)) := by
  letI : IsTopologicalGroup (actualCover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hU : IsCompact (levelSubgroup F ζ hζ U : Set (actualCover F ζ hζ)) := by
    change IsCompact ((finiteSubgroup F ζ hζ).subtype ''
      (U.toOpenSubgroup : Set (finiteSubgroup F ζ hζ)))
    exact U.isCompact.image (continuous_subtype_val :
      Continuous ((finiteSubgroup F ζ hζ).subtype))
  cases geometric with
  | false => simpa only [rightSubgroup, Bool.false_eq_true, ↓reduceIte] using hU
  | true =>
    let C := (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range
    letI : C.Normal := Subgroup.normal_of_le_center
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ)
    have hC : IsCompact (C : Set (actualCover F ζ hζ)) :=
      (Set.finite_range (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ)).isCompact
    have heq : ((levelSubgroup F ζ hζ U ⊔ C : Subgroup (actualCover F ζ hζ)) : Set _) =
        (levelSubgroup F ζ hζ U : Set (actualCover F ζ hζ)) *
          (C : Set (actualCover F ζ hζ)) := by
      ext x
      exact Subgroup.mem_sup_of_normal_right
    change IsCompact ((levelSubgroup F ζ hζ U ⊔ C : Subgroup (actualCover F ζ hζ)) :
      Set (actualCover F ζ hζ))
    rw [heq]
    exact hU.mul hC

theorem actual_compact_transporters (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    CompactTransporters (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric) := by
  letI := (actual_cover_lc_t2_group F ζ hζ).1
  letI := (actual_cover_lc_t2_group F ζ hζ).2.2
  exact compact_transporters _ _ (actual_rational_closed_discrete F ζ hζ).1
    (actual_rational_closed_discrete F ζ hζ).2 (actual_right_compact F ζ hζ U geometric)

theorem exists_actual_topology_certificate (U : FiniteLevel F ζ hζ) (geometric : Bool) :
    TopologyCertificate (rationalSubgroup F ζ hζ) (rightSubgroup F ζ hζ U geometric) := by
  letI := (actual_cover_lc_t2_group F ζ hζ).1
  letI := (actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (actual_cover_lc_t2_group F ζ hζ).2.2
  letI := actual_cover_secondCountable F ζ hζ
  apply proper_doubleQuotient_certificate
  exact proper_actionCorrespondence _ _ (actual_rational_closed_discrete F ζ hζ).1
    (actual_rational_closed_discrete F ζ hζ).2 (actual_right_compact F ζ hζ U geometric)

end DedekindZetaZeroFree.ActualQuotient

end
end
