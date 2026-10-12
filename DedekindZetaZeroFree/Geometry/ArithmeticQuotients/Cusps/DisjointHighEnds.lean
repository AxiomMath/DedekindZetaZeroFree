module

public import DedekindZetaZeroFree.Adeles.Lattices.Cusps.ParabolicExtension
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.ArithmeticHoroballIntersections

@[expose] public section

section

noncomputable section
open scoped Classical Matrix

attribute [local instance] Fintype.ofFinite

namespace DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

private theorem meanHeight_upper_frame
    (F : Type) [Field F] [NumberField F]
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) z) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
        (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F := by
  have h00 : A 0 0 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  have h11 : A 1 1 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  rw [KPCuspSiegel.action_mk]
  have hs : ∀ i : Fin (KPCuspLogShape.dimension F),
      (KPCuspSiegel.glAction F A z i).2 = (z i).2 +
        Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖ := by
    intro i
    let ρ := (KPCusp.complexPlace F i).embedding
    apply KPCuspLogShape.upper_action_snd
    · change ρ (A 1 0) = 0
      simp [hA]
    · exact (map_ne_zero ρ).mpr (div_ne_zero h00 h11)
    · change ρ (A 0 0) = ρ (A 0 0 / A 1 1) * ρ (A 1 1)
      rw [← map_mul, div_mul_cancel₀ _ h11]
  simp only [KPCuspLogShape.meanHeight, hs, Finset.sum_add_distrib, add_div]

private theorem highCusp_frame_equivariant
    (F : Type) [Field F] [NumberField F]
    (γ σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    KPCuspSiegel.action F γ '' KPCuspSiegel.highCusp F σ T =
      KPCuspSiegel.highCusp F (γ * σ) T := by
  unfold KPCuspSiegel.highCusp
  rw [Set.image_image]
  congr 1
  funext z
  exact (mul_smul γ σ z).symm

private theorem highCusp_upper_frame
    (F : Type) [Field F] [NumberField F]
    (σ : KPCuspArithmetic.PGL2 F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0) (T : ℝ) :
    KPCuspSiegel.highCusp F (σ * Matrix.ProjGenLinGroup.mk A) T =
      KPCuspSiegel.highCusp F σ
        (T + (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F) := by
  let c : ℝ := (∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F
  let u := Matrix.ProjGenLinGroup.mk A
  have hh (z : KPArch.Space (KPCuspLogShape.dimension F)) :
      KPCuspLogShape.meanHeight _ (u • z) = KPCuspLogShape.meanHeight _ z + c :=
    meanHeight_upper_frame F A hA z
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u • w, ?_, ?_⟩
    · change T + c < KPCuspLogShape.meanHeight _ (u • w)
      rw [hh]
      simpa only [add_comm] using add_lt_add_right hw c
    · exact (mul_smul σ u w).symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u⁻¹ • w, ?_, ?_⟩
    · have he := hh (u⁻¹ • w)
      rw [smul_inv_smul] at he
      change T < KPCuspLogShape.meanHeight _ (u⁻¹ • w)
      change T + c < KPCuspLogShape.meanHeight _ w at hw
      linarith
    · change (σ * u) • (u⁻¹ • w) = σ • w
      rw [mul_smul, smul_inv_smul]

private theorem highCusp_antitone
    (F : Type) [Field F] [NumberField F]
    (σ : KPCuspArithmetic.PGL2 F) {T S : ℝ} (h : T ≤ S) :
    KPCuspSiegel.highCusp F σ S ⊆ KPCuspSiegel.highCusp F σ T := by
  apply Set.image_mono
  intro z hz
  exact lt_of_le_of_lt h hz

private theorem projected_highCusp_frame_equivariant
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (γ : Γ) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (γ.val * σ) T =
      KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T := by
  rw [← highCusp_frame_equivariant F γ.val σ T, Set.image_image]
  congr 1
  funext z
  exact KPCuspSiegel.projection_action F Γ γ z

private theorem projected_highCusp_equivalent_frame_shift
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (γ : Γ) (σ τ : KPCuspArithmetic.PGL2 F)
    (h : γ • (σ • KPCuspArithmetic.infinity F) = τ • KPCuspArithmetic.infinity F) :
    ∃ c : ℝ, ∀ T : ℝ,
      KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F τ T =
        KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ (T + c) := by
  let u := σ⁻¹ * γ.val⁻¹ * τ
  have hu : u • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
    dsimp [u]
    rw [mul_smul, mul_smul, ← h]
    change σ⁻¹ • (γ.val⁻¹ • (γ.val • (σ • KPCuspArithmetic.infinity F))) =
      KPCuspArithmetic.infinity F
    rw [inv_smul_smul, inv_smul_smul]
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective u
  have hupper : A 1 0 = 0 := by
    rw [← hA] at hu
    unfold KPCuspArithmetic.infinity at hu
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hu
    obtain ⟨a, ha⟩ := hu
    have hh := congrFun ha 1
    have hz : (a • ![1, 0]) 1 = (0 : F) := by simp
    rw [hz] at hh
    change 0 = ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) 1 at hh
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh.symm
  refine ⟨(∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F, ?_⟩
  intro T
  have ht : τ = γ.val * (σ * Matrix.ProjGenLinGroup.mk A) := by
    rw [hA]
    dsimp [u]
    group
  rw [ht, projected_highCusp_frame_equivariant, highCusp_upper_frame F σ A hupper]

theorem finite_frame_high_end_absorption
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    {ι κ : Type*} [Finite ι]
    (τ : ι → KPCuspArithmetic.PGL2 F)
    (σ : κ → KPCuspArithmetic.PGL2 F)
    (hcover : ∀ b : ι, ∃ (a : κ) (γ : Γ),
      γ • (σ a • KPCuspArithmetic.infinity F) =
        τ b • KPCuspArithmetic.infinity F) :
    ∀ T : ℝ, ∃ S : ℝ,
      (⋃ b : ι, KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (τ b) S) ⊆
        (⋃ a : κ, KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T) := by
  classical
  choose a γ hγ using hcover
  choose c hc using fun b =>
    projected_highCusp_equivalent_frame_shift F Γ (γ b) (σ (a b)) (τ b) (hγ b)
  intro T
  refine ⟨T + ∑ b : ι, |c b|, ?_⟩
  intro x hx
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hx
  rw [hc b (T + ∑ b : ι, |c b|)] at hxb
  obtain ⟨z, hz, rfl⟩ := hxb
  refine Set.mem_iUnion.mpr ⟨a b, z, ?_, rfl⟩
  refine highCusp_antitone F (σ (a b)) ?_ hz
  have hle : |c b| ≤ ∑ b : ι, |c b| :=
    Finset.single_le_sum (fun b _ => abs_nonneg (c b)) (Finset.mem_univ b)
  have hneg : -(c b) ≤ |c b| := neg_le_abs (c b)
  linarith

end DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

end

end

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

 def subsetOrbitMap {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (S Γ : Subgroup G) (h : S ≤ Γ) (U : Set X) :
    Quotient (Setoid.comap (Subtype.val : U → X) (MulAction.orbitRel S X)) →
      Quotient (MulAction.orbitRel Γ X) :=
  Quotient.lift (fun x => Quotient.mk _ x.val) (by
    intro x y hxy
    apply Quotient.sound
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨⟨s.val, h s.property⟩, hs⟩))

private theorem isOpenEmbedding_subsetOrbitMap {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    (S Γ : Subgroup G) (h : S ≤ Γ) (U : Set X) (hU : IsOpen U)
    (hintersection : ∀ (γ : Γ) (x : X), x ∈ U → γ • x ∈ U → (γ : G) ∈ S) :
    Topology.IsOpenEmbedding (subsetOrbitMap S Γ h U) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro a b hab
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective b
    apply Quotient.sound
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hab))
    have hγS : (γ : G) ∈ S := hintersection γ y.val y.property (by rw [hγ]; exact x.property)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨⟨γ.val, hγS⟩, hγ⟩)
  · intro A hA
    let p : U → Quotient (Setoid.comap (Subtype.val : U → X) (MulAction.orbitRel S X)) :=
      Quotient.mk _
    have hp : IsOpen (p ⁻¹' A) := hA.preimage continuous_quotient_mk'
    have hv : IsOpen (Subtype.val '' (p ⁻¹' A)) := hU.isOpenMap_subtype_val _ hp
    have heq : subsetOrbitMap S Γ h U '' A =
        Quotient.mk (MulAction.orbitRel Γ X) '' (Subtype.val '' (p ⁻¹' A)) := by
      ext q
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
        exact ⟨x.val, ⟨x, ha, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ y, hy, rfl⟩
    rw [heq]
    letI : ContinuousConstSMul Γ X := ⟨fun γ => continuous_const_smul (γ : G)⟩
    exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ hv

theorem disjoint_embedded_high_ends_of_intersection
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    {ι : Type*}
    (q : ι → KPCuspArithmetic.Cusp F)
    (σ : ι → KPCuspArithmetic.PGL2 F) (T : ℝ)
    (hintersection : ∀ (a b : ι) (γ : Γ)
      (z : KPArch.Space (KPCuspLogShape.dimension F)),
      z ∈ KPCuspSiegel.highCusp F (σ a) T →
      KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F) z ∈
        KPCuspSiegel.highCusp F (σ b) T →
      a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ KPCuspSiegel.parabolic F Γ (q a)) :
    (Pairwise fun a b : ι =>
      Disjoint (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)
        (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ b) T)) ∧
    (∀ a : ι,
      ∃ j : KPCuspSiegel.CuspQuotient F Γ (q a) (KPCuspSiegel.highCusp F (σ a) T) →
        KPCuspSiegel.OrbitQuotient F Γ,
        Topology.IsEmbedding j ∧
        ∀ z : KPCuspSiegel.highCusp F (σ a) T,
          j (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z) := by
  haveI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F)
      (KPArch.Space (KPCuspLogShape.dimension F)) :=
    ⟨fun γ => KPCuspSiegel.continuous_action F γ⟩
  constructor
  · intro a b hab
    apply Set.disjoint_left.mpr
    rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
    have hxy : Quotient.mk (MulAction.orbitRel Γ
        (KPArch.Space (KPCuspLogShape.dimension F))) x = Quotient.mk _ y :=
      hxp.trans hyp.symm
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hxy))
    have hγhigh : KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F) y ∈
        KPCuspSiegel.highCusp F (σ a) T := by
      change γ • y ∈ _
      rw [hγ]
      exact hx
    exact hab (hintersection b a γ y hy hγhigh).1.symm
  · intro a
    refine ⟨subsetOrbitMap (KPCuspSiegel.parabolic F Γ (q a)) Γ inf_le_left
      (KPCuspSiegel.highCusp F (σ a) T), ?_, fun _ => rfl⟩
    exact (isOpenEmbedding_subsetOrbitMap _ _ inf_le_left _
      (KPCuspSiegel.isOpen_highCusp F (σ a) T) (fun γ z hz hγz =>
        (hintersection a a γ z hz hγz).2)).isEmbedding

end DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

end

end

section

noncomputable section
open scoped Classical NumberField Matrix

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

theorem component_reduction_of_integral_lattice
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M)) :
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F) (T₀ : ℝ),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) ∧
      ∀ T : ℝ, T₀ ≤ T →
        (Pairwise fun a b : Fin n =>
          Disjoint (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)
            (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ b) T)) ∧
        IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
          (⋃ a : Fin n, KPCuspSiegel.projection F Γ ''
            KPCuspSiegel.highCusp F (σ a) T)) ∧
        (∀ a : Fin n,
          ∃ j : KPCuspSiegel.CuspQuotient F Γ (q a) (KPCuspSiegel.highCusp F (σ a) T) →
            KPCuspSiegel.OrbitQuotient F Γ,
            Topology.IsEmbedding j ∧
            ∀ z : KPCuspSiegel.highCusp F (σ a) T,
              j (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z) := by
  obtain ⟨n, q, σ, t₀, P, B, hn, hσ, hcover, hdistinct, hPB,
    hboxes, hhigh, hcompact, T₁, hT₁, hends⟩ :=
    kp_cusp_siegel_cover_and_truncation F hF M hM Γ hΓ hcomm
  refine ⟨n, q, σ, T₁, hn, hσ, hcover, hdistinct, ?_⟩
  intro T hT
  obtain ⟨hdisjoint, hintersection, hmaps, hembed⟩ := hends T hT
  exact ⟨hdisjoint, (hcompact T (lt_of_lt_of_le hT₁ hT)).2, hembed⟩

theorem finite_adelic_stabilizer_commensurable_lattice
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    ∃ M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F),
      KPCuspArithmetic.IsRankTwoLattice F M ∧
      (KPFiniteComponents.arithmeticStabilizer F U g).Commensurable
        (KPCuspArithmetic.projectiveAutomorphisms F M) := by
  obtain ⟨I, a, hI, hcomm, _⟩ :=
    kp_cusp_finite_adelic_arithmetic_stabilizers F U hUc hUo g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  let M := KPCuspFiniteArithmetic.idealArithmeticModule F I
  refine ⟨M.map (KPCuspArithmetic.rationalMatrixLinearEquiv F A).toLinearMap,
    KPCuspArithmetic.isRankTwoLattice_map F M
      (KPCuspFiniteArithmetic.idealArithmeticModule_full F I hI) A, ?_⟩
  change (KPFiniteComponents.arithmeticStabilizer F U g).Commensurable
    ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
      (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom) at hcomm
  rw [KPCuspFiniteArithmetic.idealProjectiveAut_eq_arithmeticAutomorphisms,
    KPCuspArithmetic.projectiveAutomorphisms_conjugate] at hcomm
  exact hcomm

theorem finite_adelic_cusp_orbits
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    Finite (Quotient (MulAction.orbitRel
      (KPFiniteComponents.arithmeticStabilizer F U g) (KPCuspArithmetic.Cusp F))) := by
  let Γ := KPFiniteComponents.arithmeticStabilizer F U g
  obtain ⟨M, hM, hcomm⟩ := finite_adelic_stabilizer_commensurable_lattice F U hUc hUo g
  let Δ := Γ ⊓ KPCuspArithmetic.projectiveAutomorphisms F M
  have hΔ : ∀ k ∈ Δ, KPCuspArithmetic.PreservesUpToHomothety F M k := by
    intro k hk
    exact (KPCuspArithmetic.preservesUpToHomothety_iff_mem_projectiveAutomorphisms
      F M k).mpr hk.2
  have hΔcomm : Δ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M) :=
    hcomm.inf_left (.refl _)
  obtain ⟨n, q, σ, T₀, hn, hσ, hcover, hdistinct, hends⟩ :=
    component_reduction_of_integral_lattice F hF M hM Δ hΔ hΔcomm
  apply Finite.of_surjective (fun a : Fin n =>
    Quotient.mk (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)) (q a))
  intro c
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective c
  obtain ⟨a, δ, hδ⟩ := hcover r
  refine ⟨a, Quotient.sound ?_⟩
  apply (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)).symm
  exact MulAction.orbitRel_apply.mpr
    (MulAction.mem_orbit_iff.mpr ⟨⟨δ.val, δ.property.1⟩, hδ⟩)

theorem highCusp_frame_equivariant
    (F : Type) [Field F] [NumberField F]
    (γ σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    KPCuspSiegel.action F γ '' KPCuspSiegel.highCusp F σ T =
      KPCuspSiegel.highCusp F (γ * σ) T := by
  unfold KPCuspSiegel.highCusp
  rw [Set.image_image]
  congr 1
  funext z
  exact (mul_smul γ σ z).symm

theorem projected_highCusp_frame_equivariant
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (γ : Γ) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (γ.val * σ) T =
      KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T := by
  rw [← highCusp_frame_equivariant F γ.val σ T, Set.image_image]
  congr 1
  funext z
  exact KPCuspSiegel.projection_action F Γ γ z

theorem meanHeight_upper_frame
    (F : Type) [Field F] [NumberField F]
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) z) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
        (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F := by
  have h00 : A 0 0 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  have h11 : A 1 1 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  rw [KPCuspSiegel.action_mk]
  have hs : ∀ i : Fin (KPCuspLogShape.dimension F),
      (KPCuspSiegel.glAction F A z i).2 = (z i).2 +
        Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖ := by
    intro i
    let ρ := (KPCusp.complexPlace F i).embedding
    apply KPCuspLogShape.upper_action_snd
    · change ρ (A 1 0) = 0
      simp [hA]
    · exact (map_ne_zero ρ).mpr (div_ne_zero h00 h11)
    · change ρ (A 0 0) = ρ (A 0 0 / A 1 1) * ρ (A 1 1)
      rw [← map_mul, div_mul_cancel₀ _ h11]
  simp only [KPCuspLogShape.meanHeight, hs, Finset.sum_add_distrib, add_div]

theorem highCusp_upper_frame
    (F : Type) [Field F] [NumberField F]
    (σ : KPCuspArithmetic.PGL2 F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0) (T : ℝ) :
    KPCuspSiegel.highCusp F (σ * Matrix.ProjGenLinGroup.mk A) T =
      KPCuspSiegel.highCusp F σ
        (T + (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F) := by
  let c : ℝ := (∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F
  let u := Matrix.ProjGenLinGroup.mk A
  have hh (z : KPArch.Space (KPCuspLogShape.dimension F)) :
      KPCuspLogShape.meanHeight _ (u • z) = KPCuspLogShape.meanHeight _ z + c :=
    meanHeight_upper_frame F A hA z
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u • w, ?_, ?_⟩
    · change T + c < KPCuspLogShape.meanHeight _ (u • w)
      rw [hh]
      simpa only [add_comm] using add_lt_add_right hw c
    · exact (mul_smul σ u w).symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u⁻¹ • w, ?_, ?_⟩
    · have he := hh (u⁻¹ • w)
      rw [smul_inv_smul] at he
      change T < KPCuspLogShape.meanHeight _ (u⁻¹ • w)
      change T + c < KPCuspLogShape.meanHeight _ w at hw
      linarith
    · change (σ * u) • (u⁻¹ • w) = σ • w
      rw [mul_smul, smul_inv_smul]

theorem highCusp_same_cusp_shift
    (F : Type) [Field F] [NumberField F]
    (σ τ : KPCuspArithmetic.PGL2 F)
    (h : σ • KPCuspArithmetic.infinity F = τ • KPCuspArithmetic.infinity F) :
    ∃ c : ℝ, ∀ T : ℝ,
      KPCuspSiegel.highCusp F τ T = KPCuspSiegel.highCusp F σ (T + c) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (σ⁻¹ * τ)
  have hf : Matrix.ProjGenLinGroup.mk A • KPCuspArithmetic.infinity F =
      KPCuspArithmetic.infinity F := by
    rw [hA, mul_smul, ← h, inv_smul_smul]
  have hc : A 1 0 = 0 := by
    unfold KPCuspArithmetic.infinity at hf
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hf
    obtain ⟨a, ha⟩ := hf
    have hh := congrFun ha 1
    have he : (a • ![1, 0]) 1 = (0 : F) := by simp
    rw [he] at hh
    change 0 = (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) ![1, 0]) 1 at hh
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh.symm
  refine ⟨(∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F, fun T => ?_⟩
  have he : τ = σ * Matrix.ProjGenLinGroup.mk A := by rw [hA, mul_inv_cancel_left]
  rw [he]
  exact highCusp_upper_frame F σ A hc T

theorem highCusp_antitone
    (F : Type) [Field F] [NumberField F]
    (σ : KPCuspArithmetic.PGL2 F) {T S : ℝ} (h : T ≤ S) :
    KPCuspSiegel.highCusp F σ S ⊆ KPCuspSiegel.highCusp F σ T := by
  apply Set.image_mono
  intro z hz
  exact lt_of_le_of_lt h hz

theorem finite_same_cusp_common_height
    (F : Type) [Field F] [NumberField F]
    {ι : Type} [Fintype ι]
    (σ τ : ι → KPCuspArithmetic.PGL2 F)
    (h : ∀ a, σ a • KPCuspArithmetic.infinity F = τ a • KPCuspArithmetic.infinity F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ι) (T : ℝ),
      KPCuspSiegel.highCusp F (τ a) (T + C) ⊆ KPCuspSiegel.highCusp F (σ a) T ∧
      KPCuspSiegel.highCusp F (σ a) (T + C) ⊆ KPCuspSiegel.highCusp F (τ a) T := by
  choose c hc using fun a => highCusp_same_cusp_shift F (σ a) (τ a) (h a)
  let C : ℝ := ∑ a, |c a|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => abs_nonneg (c a))
  have hCa (a : ι) : |c a| ≤ C :=
    Finset.single_le_sum (fun b _ => abs_nonneg (c b)) (Finset.mem_univ a)
  refine ⟨C, hC, fun a T => ?_⟩
  constructor
  · rw [hc a]
    apply highCusp_antitone
    have hlo := neg_abs_le (c a)
    have hle := hCa a
    linarith
  · rw [hc a]
    apply highCusp_antitone
    have hhi := le_abs_self (c a)
    have hle := hCa a
    linarith

theorem finite_adelic_cusp_cover_with_compact_complement
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    let Γ := KPFiniteComponents.arithmeticStabilizer F U g
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      ∀ T : ℝ, IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
        (⋃ a : Fin n, KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)) := by
  let Γ := KPFiniteComponents.arithmeticStabilizer F U g
  obtain ⟨M, hM, hcomm⟩ := finite_adelic_stabilizer_commensurable_lattice F U hUc hUo g
  let Δ := Γ ⊓ KPCuspArithmetic.projectiveAutomorphisms F M
  have hΔ : ∀ k ∈ Δ, KPCuspArithmetic.PreservesUpToHomothety F M k := by
    intro k hk
    exact (KPCuspArithmetic.preservesUpToHomothety_iff_mem_projectiveAutomorphisms
      F M k).mpr hk.2
  have hΔcomm : Δ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M) :=
    hcomm.inf_left (.refl _)
  obtain ⟨n, q, σ, t₀, P, B, hn, hσ, hcover, hdistinct, hPB,
    hboxes, hhigh, hcompact, hends⟩ :=
    kp_cusp_siegel_cover_and_truncation F hF M hM Δ hΔ hΔcomm
  refine ⟨n, q, σ, hn, hσ, ?_, ?_⟩
  · intro r
    obtain ⟨a, δ, hδ⟩ := hcover r
    exact ⟨a, ⟨δ.val, δ.property.1⟩, hδ⟩
  · intro T
    apply KPCuspSiegel.isCompact_complement_of_cover F
      (KPCuspLogShape.dimension_pos F hF) Γ σ P B
      (fun a => (hPB a).1) (fun a => (hPB a).2.2.1) t₀ T
    intro z
    obtain ⟨δ, a, w, hw, hz⟩ := hboxes z
    exact ⟨⟨δ.val, δ.property.1⟩, a, w, hw, hz⟩

theorem finite_adelic_inequivalent_cusp_representatives
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    let Γ := KPFiniteComponents.arithmeticStabilizer F U g
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) := by
  let Γ := KPFiniteComponents.arithmeticStabilizer F U g
  let Q := Quotient (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F))
  letI : Finite Q := finite_adelic_cusp_orbits F hF U hUc hUo g
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Nonempty Q := ⟨Quotient.mk _ (KPCuspArithmetic.infinity F)⟩
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  obtain ⟨n₀, q₀, σ₀, hn₀, hσ₀, hcover₀, _⟩ :=
    finite_adelic_cusp_cover_with_compact_complement F hF U hUc hUo g
  choose a γ hγ using fun c : Q => hcover₀ c.out
  let q : Fin (Fintype.card Q) → KPCuspArithmetic.Cusp F := fun i => (e.symm i).out
  let σ : Fin (Fintype.card Q) → KPCuspArithmetic.PGL2 F :=
    fun i => (γ (e.symm i)).val * σ₀ (a (e.symm i))
  refine ⟨Fintype.card Q, q, σ, Fintype.card_pos, ?_, ?_, ?_⟩
  · intro i
    change ((γ (e.symm i)).val * σ₀ (a (e.symm i))) • _ = _
    rw [mul_smul, hσ₀]
    exact hγ (e.symm i)
  · intro r
    let c : Q := Quotient.mk _ r
    have hr : Quotient.mk (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F))
        (q (e c)) = Quotient.mk _ r := by
      change Quotient.mk _ (e.symm (e c)).out = c
      rw [e.symm_apply_apply, Quotient.out_eq]
    obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hr.symm))
    exact ⟨e c, δ, hδ⟩
  · intro i j hij δ hδ
    have he : e.symm i = e.symm j := by
      rw [← Quotient.out_eq (e.symm i), ← Quotient.out_eq (e.symm j)]
      apply Quotient.sound
      apply (MulAction.orbitRel Γ (KPCuspArithmetic.Cusp F)).symm
      exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨δ, hδ⟩)
    exact hij (e.symm.injective he)

theorem compact_complement_of_cusp_representatives
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) {n m : ℕ}
    (σ : Fin n → KPCuspArithmetic.PGL2 F)
    (q : Fin m → KPCuspArithmetic.Cusp F)
    (τ : Fin m → KPCuspArithmetic.PGL2 F)
    (hτ : ∀ b, τ b • KPCuspArithmetic.infinity F = q b)
    (hcover : ∀ r : KPCuspArithmetic.Cusp F,
      ∃ (b : Fin m) (γ : Γ), γ • q b = r)
    (hc : ∀ T : ℝ, IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
      (⋃ a : Fin n, KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)))
    (T : ℝ) :
    IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
      (⋃ b : Fin m, KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (τ b) T)) := by
  choose b γ hγ using fun a : Fin n => hcover (σ a • KPCuspArithmetic.infinity F)
  have he (a : Fin n) : ((γ a).val * τ (b a)) • KPCuspArithmetic.infinity F =
      σ a • KPCuspArithmetic.infinity F := by rw [mul_smul, hτ]; exact hγ a
  obtain ⟨C, hC, hbuffer⟩ := finite_same_cusp_common_height F
    (fun a => (γ a).val * τ (b a)) σ he
  apply (hc (T + C)).of_isClosed_subset
  · simpa only [← Set.compl_eq_univ_sdiff] using
      (KPCuspSiegel.isOpen_projected_highCusps F Γ τ T).isClosed_compl
  · intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    intro hold
    obtain ⟨a, w, hw, hwz⟩ := Set.mem_iUnion.mp hold
    apply hz.2
    apply Set.mem_iUnion.mpr
    refine ⟨b a, ?_⟩
    have hm : z ∈ KPCuspSiegel.projection F Γ ''
        KPCuspSiegel.highCusp F ((γ a).val * τ (b a)) T :=
      ⟨w, (hbuffer a T).1 hw, hwz⟩
    rwa [projected_highCusp_frame_equivariant F Γ (γ a) (τ (b a)) T] at hm

theorem finite_adelic_component_reduction
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteComponents.FinitePGL2 F))
    (hUc : IsCompact (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (hUo : IsOpen (U : Set (KPFiniteComponents.FinitePGL2 F)))
    (g : KPFiniteComponents.FinitePGL2 F) :
    let Γ := KPFiniteComponents.arithmeticStabilizer F U g
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F) (T₀ : ℝ),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) ∧
      ∀ T : ℝ, T₀ ≤ T →
        (Pairwise fun a b : Fin n =>
          Disjoint (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)
            (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ b) T)) ∧
        IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
          (⋃ a : Fin n, KPCuspSiegel.projection F Γ ''
            KPCuspSiegel.highCusp F (σ a) T)) ∧
        (∀ a : Fin n,
          ∃ j : KPCuspSiegel.CuspQuotient F Γ (q a) (KPCuspSiegel.highCusp F (σ a) T) →
            KPCuspSiegel.OrbitQuotient F Γ,
            Topology.IsEmbedding j ∧
            ∀ z : KPCuspSiegel.highCusp F (σ a) T,
              j (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z) := by
  let Γ := KPFiniteComponents.arithmeticStabilizer F U g
  obtain ⟨n, q, σ, hn, hσ, hcover, hdistinct⟩ :=
    finite_adelic_inequivalent_cusp_representatives F hF U hUc hUo g
  obtain ⟨M, hM, hcomm⟩ :=
    finite_adelic_stabilizer_commensurable_lattice F U hUc hUo g
  obtain ⟨T₀, hintersection⟩ :=
    KPFiniteCuspAtlasReduction.commensurable_uniform_high_cusp_intersection
      F hF M hM Γ hcomm q σ hσ hdistinct
  obtain ⟨m, r, τ, _, hτ, _, hcompact⟩ :=
    finite_adelic_cusp_cover_with_compact_complement F hF U hUc hUo g
  have habsorb :=
    KPFiniteCuspAtlasReduction.finite_frame_high_end_absorption F Γ τ σ
      (fun b => by
        obtain ⟨a, γ, hγ⟩ := hcover (r b)
        exact ⟨a, γ, by rw [hσ, hτ]; exact hγ⟩)
  refine ⟨n, q, σ, T₀, hn, hσ, hcover, hdistinct, ?_⟩
  intro T hT
  obtain ⟨hdisjoint, hembed⟩ :=
    KPFiniteCuspAtlasReduction.disjoint_embedded_high_ends_of_intersection
      F Γ q σ T (hintersection T hT)
  refine ⟨hdisjoint, ?_, hembed⟩
  obtain ⟨S, hS⟩ := habsorb T
  apply (hcompact S).of_isClosed_subset
  · simpa only [← Set.compl_eq_univ_sdiff] using
      (KPCuspSiegel.isOpen_projected_highCusps F Γ σ T).isClosed_compl
  · intro z hz
    exact ⟨hz.1, fun hp => hz.2 (hS hp)⟩

namespace ReductionTransfer
open scoped Classical
variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

def orbitCoarsening (Δ Γ : Subgroup G) (h : Δ ≤ Γ) :
    Quotient (MulAction.orbitRel Δ X) → Quotient (MulAction.orbitRel Γ X) :=
  Quotient.lift (Quotient.mk _) (by
    intro x y hxy
    apply Quotient.sound
    obtain ⟨δ, hδ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨⟨δ.val, h δ.property⟩, hδ⟩))

@[simp] theorem orbitCoarsening_mk (Δ Γ : Subgroup G) (h : Δ ≤ Γ) (x : X) :
    orbitCoarsening (X := X) Δ Γ h (Quotient.mk _ x) = Quotient.mk _ x := rfl

def subsetOrbitMap (S Γ : Subgroup G) (h : S ≤ Γ) (U : Set X) :
    Quotient (Setoid.comap (Subtype.val : U → X) (MulAction.orbitRel S X)) →
      Quotient (MulAction.orbitRel Γ X) :=
  Quotient.lift (fun x => Quotient.mk _ x.val) (by
    intro x y hxy
    apply Quotient.sound
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨⟨s.val, h s.property⟩, hs⟩))

@[simp] theorem subsetOrbitMap_mk (S Γ : Subgroup G) (h : S ≤ Γ) (U : Set X) (x : U) :
    subsetOrbitMap S Γ h U (Quotient.mk _ x) = Quotient.mk _ x.val := rfl

end ReductionTransfer

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end

end
