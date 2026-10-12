module

public import DedekindZetaZeroFree.Adeles.Lattices.SupportedPrincipalIntersection
public import DedekindZetaZeroFree.Arithmetic.Units.SUnitPowerQuotientDimensions

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ArithmeticContext
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Pointwise
private theorem compact_reps_open {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H P : Subgroup G) (ho : IsOpen (H : Set G))
    (K : Set G) (hc : IsCompact K) (hrep : ∀ g : G, ∃ k ∈ K, g / k ∈ P) :
    ∃ C : Set H, IsCompact C ∧ ∀ h : H, ∃ c ∈ C, h.val / c.val ∈ P := by
  classical
  let J := H ⊔ P
  have hJo : IsOpen (J : Set G) := Subgroup.isOpen_mono (show H ≤ J from le_sup_left) ho
  let K0 := K ∩ (J : Set G)
  have hK0 : IsCompact K0 := hc.inter_right (J.isClosed_of_isOpen hJo)
  let V : P → Set G := fun p => (fun x : G => p.val * x) '' (H : Set G)
  have hVo : ∀ p, IsOpen (V p) := fun p => (Homeomorph.mulLeft p.val).isOpenMap _ ho
  have hcover : K0 ⊆ ⋃ p, V p := by
    intro k hk
    obtain ⟨h, hh, p, hp, he⟩ := Subgroup.mem_sup.mp hk.2
    exact Set.mem_iUnion.mpr ⟨⟨p,hp⟩, h, hh, by simpa [mul_comm] using he⟩
  obtain ⟨t, ht⟩ := hK0.elim_finite_subcover V hVo hcover
  let D : P → Set G := fun p => (fun x : G => p.val⁻¹ * x) '' (K0 ∩ V p)
  have hDc : ∀ p, IsCompact (D p) := by
    intro p
    apply IsCompact.image _ (continuous_const_mul _)
    apply hK0.inter_right
    exact (Homeomorph.mulLeft p.val).isClosedMap _ (H.isClosed_of_isOpen ho)
  let B := ⋃ p ∈ t, D p
  have hBc : IsCompact B := t.isCompact_biUnion (fun p _ => hDc p)
  have hBH : B ⊆ (H : Set G) := by
    intro b hb
    rcases Set.mem_iUnion.mp hb with ⟨p, hb⟩
    rcases Set.mem_iUnion.mp hb with ⟨_, hb⟩
    rcases hb with ⟨k, ⟨_, hk⟩, rfl⟩
    rcases hk with ⟨h, hh, rfl⟩
    simpa using hh
  let C : Set H := Subtype.val ⁻¹' B
  have hCc : IsCompact C := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa [C, Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hBH] using hBc
  refine ⟨C, hCc, ?_⟩
  intro h
  obtain ⟨k, hk, hpk⟩ := hrep h.val
  have hkJ : k ∈ J := by
    have hx := J.div_mem ((show H ≤ J from le_sup_left) h.prop)
      ((show P ≤ J from le_sup_right) hpk)
    simpa using hx
  rcases Set.mem_iUnion.mp (ht ⟨hk,hkJ⟩) with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨hpt, hkp⟩
  let b := p.val⁻¹ * k
  have hbB : b ∈ B := Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpt, k, ⟨⟨hk,hkJ⟩, hkp⟩, rfl⟩⟩
  refine ⟨⟨b, hBH hbB⟩, hbB, ?_⟩
  have := P.mul_mem hpk p.prop
  simpa [b, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

variable {F : Type} [Field F] [NumberField F]

theorem normOne_sixth_unit_quotient_compact (A : SArithmeticData F) :
    CompactSpace (A.G1 ⧸ A.Gamma1) := by
  classical
  let N := IdeleGroup.normOneSubgroup (K := F)
  let P := (IdeleGroup.principalSubgroup F).subgroupOf N
  let K : Set N := Subtype.val ⁻¹' IdeleGroup.compactNormOneClassCover
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset]
    · exact IdeleGroup.isCompact_compactNormOneClassCover
    · intro k hk
      exact ⟨⟨k, IdeleGroup.compactNormOneClassCover_subset_normOne hk⟩, rfl⟩
  have hrep : ∀ g : N, ∃ k ∈ K, g / k ∈ P := by
    intro g
    have hg : QuotientGroup.mk' (IdeleGroup.principalSubgroup F) g.val ∈
        IdeleClassGroup.normOneSubgroup (K := F) :=
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff g.val).2 g.prop
    change QuotientGroup.mk' (IdeleGroup.principalSubgroup F) g.val ∈
      (IdeleClassGroup.normOneSubgroup (K := F) : Set (IdeleClassGroup F)) at hg
    rw [← IdeleClassGroup.image_compactNormOneClassCover] at hg
    obtain ⟨k, hk, he⟩ := hg
    refine ⟨⟨k, IdeleGroup.compactNormOneClassCover_subset_normOne hk⟩, hk, ?_⟩
    change g.val / k ∈ IdeleGroup.principalSubgroup F
    exact QuotientGroup.eq_iff_div_mem.mp he.symm
  obtain ⟨C, hC, hCrep⟩ := compact_reps_open A.H P A.isOpen_H K hK hrep
  obtain ⟨e, he⟩ := A.exists_supportedChart
  let f : A.H →* A.G1 := (MonoidHom.fst A.G1 A.C).comp e.toMonoidHom
  have hf : Continuous f := continuous_fst.comp e.continuous
  let D := f '' C
  have hD : IsCompact D := hC.image hf
  have hDrep : ∀ g : A.G1, ∃ d ∈ D, g / d ∈ A.L := by
    intro g
    let h := e.symm (g, 1)
    obtain ⟨c, hc, hpc⟩ := hCrep h
    have hpc' : h / c ∈ A.principalIntersection := hpc
    rw [A.principalIntersection_eq_range] at hpc'
    obtain ⟨u, hu⟩ := hpc'
    have hu' : f (h / c) = A.diagonalS u := by
      rw [← hu]
      exact congrArg Prod.fst (A.supportedChart_principal e he u)
    refine ⟨f c, ⟨c, hc, rfl⟩, u, ?_⟩
    have hf_h : f h = g := by
      change (e (e.symm (g, 1))).1 = g
      rw [e.apply_symm_apply]
    rw [map_div, hf_h] at hu'
    exact hu'.symm
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  letI : Finite A.UnitQuotient := Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv
  let r : A.UnitQuotient → A.U := Quotient.out
  let B : Set A.G1 := ⋃ q : A.UnitQuotient,
    (fun d : A.G1 => d * A.diagonalS (r q)) '' D
  have hB : IsCompact B := isCompact_iUnion fun q =>
    hD.image (continuous_mul_const _)
  have hsurj : QuotientGroup.mk' A.Gamma1 '' B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A.Gamma1 x
    obtain ⟨d, hd, u, hu⟩ := hDrep g
    let q : A.UnitQuotient := QuotientGroup.mk' A.unitSixthPowers u
    have hq : u / r q ∈ A.unitSixthPowers := by
      apply QuotientGroup.eq_iff_div_mem.mp
      exact (Quotient.out_eq q).symm
    have hgam : A.diagonalS (u / r q) ∈ A.Gamma1 := by
      rw [A.Gamma1_eq_sixthPower_image]
      exact ⟨u / r q, hq, rfl⟩
    refine ⟨d * A.diagonalS (r q), Set.mem_iUnion.mpr ⟨q, d, hd, rfl⟩, ?_⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hgu : g = d * A.diagonalS u := by
      have := congrArg (fun z : A.G1 => d * z) hu
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this.symm
    rw [hgu]
    simpa [map_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      A.Gamma1.inv_mem hgam
  apply isCompact_univ_iff.mp
  rw [← hsurj]
  exact hB.image QuotientGroup.continuous_mk

end
end DedekindZetaZeroFree.ArithmeticContext
