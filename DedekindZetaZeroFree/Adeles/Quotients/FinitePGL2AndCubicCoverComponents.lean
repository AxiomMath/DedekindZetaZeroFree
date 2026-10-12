module

public import DedekindZetaZeroFree.Adeles.Lattices.PGL.SteinitzClassObstruction

@[expose] public section

open scoped Pointwise

namespace DedekindZetaZeroFree

namespace KPFiniteComponents

abbrev FiniteAdeles (F : Type*) [Field F] [NumberField F] :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

abbrev FinitePGL2 (F : Type*) [Field F] [NumberField F] :=
  Matrix.ProjGenLinGroup (Fin 2) (FiniteAdeles F)

noncomputable instance (F : Type*) [Field F] [NumberField F] :
    TopologicalSpace (FinitePGL2 F) := by
  unfold FinitePGL2 Matrix.ProjGenLinGroup
  infer_instance

end KPFiniteComponents

end DedekindZetaZeroFree

section

open scoped Pointwise

namespace DedekindZetaZeroFree
namespace KPFiniteComponents

abbrev RationalPGL2 (F : Type*) [Field F] := Matrix.ProjGenLinGroup (Fin 2) F

noncomputable def diagonal (F : Type*) [Field F] [NumberField F] :
    RationalPGL2 F →* FinitePGL2 F :=
  Matrix.ProjGenLinGroup.map (algebraMap F (FiniteAdeles F))

def integralLattice (F : Type*) [Field F] [NumberField F] :
    Set (Matrix (Fin 2) (Fin 1) (FiniteAdeles F)) :=
  {x | ∀ i j v, x i j v ∈ v.adicCompletionIntegers F}

noncomputable def integralCompact (F : Type*) [Field F] [NumberField F] :
    Subgroup (FinitePGL2 F) :=
  (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeles F))
    (integralLattice F)).map Matrix.ProjGenLinGroup.mk

def idealLattice (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Set (Matrix (Fin 2) (Fin 1) F) :=
  {x | (∃ a : NumberField.RingOfIntegers F, algebraMap _ F a = x 0 0) ∧ x 1 0 ∈ I}

noncomputable def projectiveIdealAut (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Subgroup (RationalPGL2 F) :=
  (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 2) F)
    (idealLattice F I)).map Matrix.ProjGenLinGroup.mk

noncomputable def arithmeticStabilizer (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (FinitePGL2 F)) (g : FinitePGL2 F) :
    Subgroup (RationalPGL2 F) :=
  (U.map (MulAut.conj g).toMonoidHom).comap (diagonal F)

end KPFiniteComponents

theorem kp_cusp_finite_adelic_components
    (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F))) :
    Finite (DoubleCoset.Quotient
      ((KPFiniteComponents.diagonal F).range : Set (KPFiniteComponents.FinitePGL2 F))
      (U : Set (KPFiniteComponents.FinitePGL2 F))) := by
  letI : IsTopologicalGroup (KPFiniteComponents.FinitePGL2 F) :=
    KPFiniteAdelicLatticeStabilizers.projective_topological_group F
  obtain ⟨hKcompact, hKopen⟩ :=
    (KPFiniteAdelicLatticeStabilizers.bounded_crt_lattice_and_projective_compact F).1
  exact KPFiniteAdelicLatticeStabilizers.finite_doubleCoset_at_open_level
    (KPFiniteComponents.diagonal F).range (KPFiniteComponents.integralCompact F) U
    hKcompact hKopen hUopen (KPFiniteAdelicLatticeStabilizers.projective_class_finiteness F)

theorem kp_cusp_finite_adelic_arithmetic_stabilizers
    (F : Type*) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUcompact : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUopen : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
      (a : KPFiniteComponents.RationalPGL2 F), I ≠ 0 ∧
      (KPFiniteComponents.arithmeticStabilizer F U g).Commensurable
        ((KPFiniteComponents.projectiveIdealAut F I).map (MulAut.conj a).toMonoidHom) ∧
      (KPFiniteComponents.arithmeticStabilizer F
        (U ⊓ KPFiniteComponents.integralCompact F) g).Commensurable
        ((KPFiniteComponents.projectiveIdealAut F I).map (MulAut.conj a).toMonoidHom) := by
  obtain ⟨I, a, hI, hstandard⟩ :=
    KPFiniteAdelicLatticeStabilizers.standard_stabilizer_class_obstruction F g
  obtain ⟨hlevel, hintersection⟩ :=
    KPFiniteAdelicLatticeStabilizers.level_stabilizers_commensurable_standard F U hUcompact hUopen g
  exact ⟨I, a, hI, hlevel.trans hstandard, hintersection.trans hstandard⟩

namespace KPFiniteComponentCover
variable {C G R : Type*} [Group C] [Group G] [Group R]
variable (π : C →* G) (s : R →* C) (d : R →* G) (hs : π.comp s = d)
variable (U : Subgroup C)
private def q : DoubleCoset.Quotient (s.range : Set C) (U : Set C) →
    DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G) :=
  Quotient.lift (fun x : C => DoubleCoset.mk d.range (U.map π) (π x)) (by
    intro a b h
    change DoubleCoset.setoid (s.range : Set C) (U : Set C) a b at h
    obtain ⟨t, ⟨r, rfl⟩, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp h
    apply (DoubleCoset.eq).2
    refine ⟨d r, ⟨r, rfl⟩, π u, ⟨u, hu, rfl⟩, ?_⟩
    simp [← hs, map_mul])

private theorem q_surjective (hπ : Function.Surjective π) : Function.Surjective (q π s d hs U) := by
  intro b
  induction b using Quotient.inductionOn with
  | h g =>
    obtain ⟨c, rfl⟩ := hπ g
    exact ⟨DoubleCoset.mk s.range U c, rfl⟩

private theorem fiber_surjective (hcentral : π.ker ≤ Subgroup.center C) (c : C) :
    Function.Surjective (fun z : π.ker =>
      (⟨DoubleCoset.mk s.range U (z.val * c), show q π s d hs U
        (DoubleCoset.mk s.range U (z.val * c)) = q π s d hs U
          (DoubleCoset.mk s.range U c) from by
        change DoubleCoset.mk d.range (U.map π) (π (z.val * c)) =
          DoubleCoset.mk d.range (U.map π) (π c)
        simp only [map_mul, (MonoidHom.mem_ker.mp z.property), one_mul]⟩ :
      {a // q π s d hs U a = q π s d hs U (DoubleCoset.mk s.range U c)})) := by
  rintro ⟨a, ha⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  change DoubleCoset.mk d.range (U.map π) (π x) =
    DoubleCoset.mk d.range (U.map π) (π c) at ha
  obtain ⟨t, ⟨r, rfl⟩, v, ⟨u, hu, rfl⟩, hx⟩ := DoubleCoset.eq.mp ha.symm
  have hsr : π (s r) = d r := DFunLike.congr_fun hs r
  let z : π.ker := ⟨x * (s r * c * u)⁻¹, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hsr, hx, mul_inv_cancel]⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change DoubleCoset.mk s.range U (z.val * c) = DoubleCoset.mk s.range U x
  apply DoubleCoset.eq.mpr
  refine ⟨s r, ⟨r, rfl⟩, u, hu, ?_⟩
  have hz : s r * z.val = z.val * s r := Subgroup.mem_center_iff.mp (hcentral z.property) (s r)
  rw [← mul_assoc (s r) z.val c, hz]
  dsimp [z]
  group

private theorem fiber_finite (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center C) [Finite π.ker]
    (b : DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G)) :
    Finite {a // q π s d hs U a = b} := by
  obtain ⟨a, rfl⟩ := q_surjective π s d hs U hπ b
  obtain ⟨c, rfl⟩ := Quotient.exists_rep a
  exact Finite.of_surjective _ (fiber_surjective π s d hs U hcentral c)

private theorem fiber_card (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center C) [Finite π.ker]
    (b : DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G)) :
    Nat.card {a // q π s d hs U a = b} ≤ Nat.card π.ker := by
  obtain ⟨a, rfl⟩ := q_surjective π s d hs U hπ b
  obtain ⟨c, rfl⟩ := Quotient.exists_rep a
  exact Nat.card_le_card_of_surjective _ (fiber_surjective π s d hs U hcentral c)

include hs in
private theorem total_finite (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center C) [Finite π.ker]
    [Finite (DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G))] :
    Finite (DoubleCoset.Quotient (s.range : Set C) (U : Set C)) := by
  letI (b : DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G)) :=
    fiber_finite π s d hs U hπ hcentral b
  exact Finite.of_injective
    (fun a => (⟨q π s d hs U a, ⟨a, rfl⟩⟩ :
      Sigma fun b => {a // q π s d hs U a = b})) (by
        intro a b h
        exact congrArg (fun x => x.2.val) h)
include hs in

theorem finite_doubleCoset_of_finite_central_kernel
    (hπ : Function.Surjective π) (hcentral : π.ker ≤ Subgroup.center C)
    [Finite π.ker]
    (hbase : Finite (DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G))) :
    Finite (DoubleCoset.Quotient (s.range : Set C) (U : Set C)) ∧
    ∃ q : DoubleCoset.Quotient (s.range : Set C) (U : Set C) →
        DoubleCoset.Quotient (d.range : Set G) (U.map π : Set G),
      (∀ c, q (DoubleCoset.mk s.range U c) =
        DoubleCoset.mk d.range (U.map π) (π c)) ∧
      Function.Surjective q ∧
      (∀ b, Nat.card {a // q a = b} ≤ Nat.card π.ker) := by
  letI := hbase
  refine ⟨total_finite π s d hs U hπ hcentral, q π s d hs U,
    fun _ => rfl, q_surjective π s d hs U hπ, ?_⟩
  exact fiber_card π s d hs U hπ hcentral
end KPFiniteComponentCover

theorem kp_cusp_cubic_cover_finite_components
    (F : Type*) [Field F] [NumberField F]
    (C : Type*) [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    (π : C →* KPFiniteComponents.FinitePGL2 F)
    (hπcontinuous : Continuous π) (hπopen : IsOpenMap π)
    (hπsurjective : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center C)
    (hkernelFinite : Finite π.ker) (hkernelCard : Nat.card π.ker ≤ 3)
    (s : KPFiniteComponents.RationalPGL2 F →* C)
    (hs : π.comp s = KPFiniteComponents.diagonal F)
    (U : Subgroup C) (hUcompact : IsCompact (U : Set C))
    (hUopen : IsOpen (U : Set C)) :
    Finite (DoubleCoset.Quotient
      ((KPFiniteComponents.diagonal F).range : Set (KPFiniteComponents.FinitePGL2 F))
      (U.map π : Set (KPFiniteComponents.FinitePGL2 F))) ∧
    Finite (DoubleCoset.Quotient (s.range : Set C) (U : Set C)) ∧
    ∃ q : DoubleCoset.Quotient (s.range : Set C) (U : Set C) →
        DoubleCoset.Quotient
      ((KPFiniteComponents.diagonal F).range : Set (KPFiniteComponents.FinitePGL2 F))
      (U.map π : Set (KPFiniteComponents.FinitePGL2 F)),
      (∀ c : C, q (DoubleCoset.mk s.range U c) =
        DoubleCoset.mk (KPFiniteComponents.diagonal F).range (U.map π) (π c)) ∧
      Function.Surjective q ∧
      (∀ b, Nat.card {a // q a = b} ≤ 3) := by
  classical
  letI : Finite π.ker := hkernelFinite
  have hbase := kp_cusp_finite_adelic_components F (U.map π)
    (by simpa only [Subgroup.coe_map] using hUcompact.image hπcontinuous)
    (by simpa only [Subgroup.coe_map] using hπopen _ hUopen)
  letI := hbase
  refine ⟨hbase, KPFiniteComponentCover.total_finite π s
    (KPFiniteComponents.diagonal F) hs U hπsurjective hcentral, ?_⟩
  refine ⟨KPFiniteComponentCover.q π s (KPFiniteComponents.diagonal F) hs U,
    fun _ => rfl, KPFiniteComponentCover.q_surjective π s
      (KPFiniteComponents.diagonal F) hs U hπsurjective, ?_⟩
  intro b
  exact (KPFiniteComponentCover.fiber_card π s (KPFiniteComponents.diagonal F)
    hs U hπsurjective hcentral b).trans hkernelCard

end DedekindZetaZeroFree

end
