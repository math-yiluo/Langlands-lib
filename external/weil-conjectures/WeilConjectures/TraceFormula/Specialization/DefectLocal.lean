/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreBaseChange
public import WeilConjectures.TraceFormula.Specialization.DefectExchanges

/-!

# The vanishing of the defect of the specialization is local

Let `X` be a separated `k`-scheme of finite type, `Z = V(I) ⊆ X` a closed subscheme and
`g_a : V_a ⟶ X` finitely many open immersions covering `X`. This file shows that the defect
`C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` vanishes as soon as every
`C_{V_a, g_a^* Z}(g_a^* L)` does
(`ProEtale.CondensedRing.isZero_specializationDefect_of_cover`): this is the reduction "the
assertion is local" in the proof of blueprint `theorem-verdier-s-theorem-specialization-zero--1`.

By the smooth exchange for the defect
(`ProEtale.CondensedRing.nonempty_specializationDefect_upperStar_iso`) the pullbacks of `C_{X,Z}(L)`
along the maps `N_⊥ (Z ∩ V_a) ⟶ N_⊥ Z` of special fibres of the constant families vanish, and we
conclude by the detection of zero objects along finite quasi-compact jointly surjective families.
For this we show the geometric facts:

* along an open immersion `h : X' ⟶ X`, the deformation space of `h^* I` is the base change
  `X' ×_X D_I X` (`Scheme.IdealSheafData.isPullback_deformationSpaceMap_of_isOpenImmersion`), and
  so are the total spaces and the special fibres over the trait
  (`ProEtale.CondensedRing.isPullback_deformationSpecialFibreMap_toBase`); in particular the map of
  special fibres is an open immersion
  (`ProEtale.CondensedRing.isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion`);
* the restriction `Z ∩ V_a ⟶ Z` of `g_a` to the centre is the base change of `g_a`
  (`ProEtale.CondensedRing.isPullback_centreMap`, in `DefectCentreMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Locality of the vanishing of the defect -/

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The vanishing of the defect is local** (the reduction "the assertion is local" in the proof
of blueprint `theorem-verdier-s-theorem-specialization-zero--1`): for finitely many open immersions
`g_a : V_a ⟶ X` covering `X`, if every defect `C_{V_a, g_a^* Z}(g_a^* L)` vanishes, then so does
`C_{X,Z}(L)`. -/
theorem isZero_specializationDefect_of_cover {ι : Type*} [Finite ι] {V : ι → Over (Spec (.of k))}
    [∀ a, LocallyOfFiniteType (V a).hom] [∀ a, QuasiCompact (V a).hom]
    [∀ a, IsSeparated (V a).hom] (g : ∀ a, V a ⟶ X) [∀ a, IsOpenImmersion (g a).left]
    (hg : ⋃ a, Set.range (g a).left.base = Set.univ)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : ∀ a, IsZero (specializationDefect (V a) (I.comap (g a).left) k'
      (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g a)).obj L).obj)) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun a ↦ (centreSpecialFibreMap (g a) I k').left)
    (exists_mem_range_centreSpecialFibreMap I k' g hg)
  have (a : ι) : IsIso ((L(((centreSpecialFibreMap (g a) I k').left)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧)).map
      (0 : specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ⟶ 0)) := by
    obtain ⟨e⟩ := nonempty_specializationDefect_upperStar_iso (g a) I k' L
    exact ((h a).of_iso e.symm).isIso (Functor.map_isZero _ (isZero_zero _)) _
  exact ((isIsoZero_iff_source_target_isZero _ _).1 (hP.isIso
    (0 : specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ⟶ 0))).1

variable (X) in
/-- **Reduction to complexes vanishing on the centre** (blueprint
`lemma-base-change-cone-x-z`, last assertion): if `C_{X,Z}(L₀) = 0` for every bounded
constructible `L₀` with `Li^* L₀ = 0`, then `C_{X,Z}(L) = 0` for every `L`. Indeed
`C_{X,Z}(L) ≅ C_{X,Z}(j_! j^* L)` for the complement `j : X ∖ Z ⟶ X`, and `Li^* j_! = 0`. -/
theorem isZero_specializationDefect_of_forall_isZero_upperStar
    (h : ∀ L₀ : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (centreι X I)).obj L₀) →
      IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L₀.obj))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  have hj := isCompl_range_overRestrictι_centreι I
  obtain ⟨e⟩ := nonempty_specializationDefect_lowerShriek_upperStar_iso X I k'
    (overRestrictι X I.support.compl) hj L
  exact (h _ (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ _
    (centreι X I) hj.disjoint _)).of_iso e.symm

end AlgebraicGeometry.ProEtale.CondensedRing
