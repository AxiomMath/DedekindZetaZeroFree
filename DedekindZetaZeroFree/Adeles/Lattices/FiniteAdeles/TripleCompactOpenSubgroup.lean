module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RootGroups.ConjugatedFiniteLevel

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F]

theorem triple_finite_level (K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
 (hc : IsCompact (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
 (ho : IsOpen (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :
 let K3 := K.map (nsmulAddMonoidHom 3)
 IsCompact (K3 : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧
 IsOpen (K3 : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧ K3 ≤ K ∧
 ∀ r:F, algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r ∈ K3 →
 ∃ r0:F, algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r0 ∈ K ∧ 3 • r0 = r := by
 dsimp only
 let A := IsDedekindDomain.FiniteAdeleRing (𝓞 F) F
 have he : (nsmulAddMonoidHom 3 : A →+ A) = DistribSMul.toAddMonoidHom A (3:A) := by
   ext x
   simp [smul_eq_mul]
 have h3 : IsUnit (3:A) := by
   have h : IsUnit (3:F) := isUnit_iff_ne_zero.mpr (by norm_num)
   convert h.map (algebraMap F A) using 1
   exact (map_ofNat (algebraMap F A) 3).symm
 have hh : IsHomeomorph (fun x : A => (3:A) • x) := h3.isHomeomorph_smul
 refine ⟨?_, ?_, ?_, ?_⟩
 · exact hc.image (continuous_id.nsmul 3)
 · change IsOpen ((nsmulAddMonoidHom 3) '' (K : Set A))
   rw [he]
   exact hh.isOpenMap _ ho
 · rintro x ⟨y,hy,rfl⟩
   exact K.nsmul_mem hy 3
 · intro r hr
   obtain ⟨x,hx,hxr⟩ := hr
   refine ⟨(3:F)⁻¹ * r, ?_, ?_⟩
   · have hinv : algebraMap F A (3:F)⁻¹ * (3:A) = 1 := by
       rw [← map_ofNat (algebraMap F A) 3, ← map_mul]
       norm_num
     rw [map_mul, ← hxr]
     convert hx using 1
     simp only [nsmulAddMonoidHom_apply, nsmul_eq_mul]
     rw [← mul_assoc]
     have hn : (↑(3:ℕ) : A) = 3 := by norm_num
     rw [hn]
     change algebraMap F A (3:F)⁻¹ * (3:A) * x ∈ K ↔ x ∈ K
     rw [hinv, one_mul]
   · simp only [nsmul_eq_mul]
     norm_num only [Nat.cast_ofNat]
     field_simp
end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
