module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

namespace DedekindZetaZeroFree.KPLocalJacquetImage

open scoped Valued
open ValuativeRel KPLocalStoneVonNeumann KPLocalPrincipalSeries
noncomputable section

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def root (A : LocalBorelData (K := K) (G := G) T) : Multiplicative K →* G :=
  A.B.subtype.comp A.upperRoot

abbrev Jacquet (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) := Representation.Coinvariants (ρ.comp (root A))

abbrev jacquetRelations (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) := Representation.Coinvariants.ker (ρ.comp (root A))

private theorem conjugate_root (A : LocalBorelData (K := K) (G := G) T)
    (h : H) (x : Multiplicative K) :
    ∃ y : Multiplicative K,
      (A.torus h : G) * root A x * (A.torus h : G)⁻¹ = root A y := by
  let b : A.B := A.torus h * A.upperRoot x * (A.torus h)⁻¹
  obtain ⟨y, hy⟩ := A.borel_decomposition b
  have hb : A.retract b = 1 := by
    simp [b, A.retract_torus, A.retract_upperRoot]
  rw [hb, map_one, one_mul] at hy
  exact ⟨y, congrArg (fun z : A.B => (z : G)) hy⟩

 theorem jacquetRelations_stable (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) (h : H) :
    jacquetRelations A ρ ≤ (jacquetRelations A ρ).comap (ρ (A.torus h : G)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, v⟩, rfl⟩
  obtain ⟨y, hy⟩ := conjugate_root A h x
  apply Representation.Coinvariants.mem_ker_of_eq y (ρ (A.torus h : G) v)
  change ρ (root A y) (ρ (A.torus h : G) v) - ρ (A.torus h : G) v =
    ρ (A.torus h : G) ((ρ.comp (root A)) x v - v)
  rw [← hy]
  simp [← Module.End.mul_apply, ← map_mul, mul_assoc]

def jacquetRepresentation (A : LocalBorelData (K := K) (G := G) T)
    (ρ : Representation ℂ G V) : Representation ℂ H (Jacquet A ρ) :=
  Representation.quotient (ρ.comp (A.B.subtype.comp A.torus))
    (jacquetRelations A ρ) (jacquetRelations_stable A ρ)

def jacquetLinearMap (A : LocalBorelData (K := K) (G := G) T)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) : Jacquet A ρ →ₗ[ℂ] Jacquet A σ :=
  Representation.Coinvariants.map _ _
    { toLinearMap := f.toLinearMap
      isIntertwining' x := f.isIntertwining' (root A x) }

def jacquetMap (A : LocalBorelData (K := K) (G := G) T)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) :
    (jacquetRepresentation A ρ).IntertwiningMap (jacquetRepresentation A σ) where
  toLinearMap := jacquetLinearMap A f
  isIntertwining' h := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change Representation.Coinvariants.mk (σ.comp (root A)) (f (ρ (A.torus h : G) v)) =
      Representation.Coinvariants.mk (σ.comp (root A)) (σ (A.torus h : G) (f v))
    rw [f.isIntertwining]

end
end DedekindZetaZeroFree.KPLocalJacquetImage
