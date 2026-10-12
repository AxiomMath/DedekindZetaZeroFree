module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

theorem triple_mem_kernelLattice {F : Type} [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : KPCuspCharts.ParabolicData F S)
    (ρ : S →* rootsOfUnity 3 F) (x : D.L) :
    (3 : ℕ) • (x : F) ∈ KPCuspGenuineMonodromy.kernelLattice S D ρ := by
  refine ⟨D.L.nsmul_mem x.property 3, ?_⟩
  intro hx
  have he : (⟨3 • (x : F), hx⟩ : D.L) = 3 • x := Subtype.ext rfl
  rw [he]
  have hm : Multiplicative.ofAdd (3 • x) = (Multiplicative.ofAdd x) ^ 3 := rfl
  rw [hm, map_pow, map_pow]
  apply Subtype.ext
  exact (ρ (D.inclusion (Multiplicative.ofAdd x))).property

theorem small_conjugated_finite_root_level
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ∃ K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F, x ∈ K → c⁻¹ *
        KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.finiteRoot F ζ hζ x * c ∈ U.toOpenSubgroup := by
  let n := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.finiteRoot F ζ hζ
  have hn : Continuous n :=
    KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.finiteRoot_continuous F ζ hζ
  have hp : Continuous (fun x => c⁻¹ * n x * c) := (continuous_const.mul hn).mul continuous_const
  have hzero : c⁻¹ * n 0 * c = 1 := by
    simp [n, KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.finiteRoot_zero]
  have hmem : (fun x => c⁻¹ * n x * c) ⁻¹' (U.toOpenSubgroup : Set _) ∈ 𝓝 0 := by
    apply hp.continuousAt.preimage_mem_nhds
    rw [hzero]
    exact U.toOpenSubgroup.isOpen.mem_nhds (U.toOpenSubgroup.one_mem)
  obtain ⟨K, hc, ho, hK⟩ := AdelicSeparation.finiteAdeles_compactOpen_basis_zero F _ hmem
  exact ⟨K, hc, ho, fun x hx => hK hx⟩

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
