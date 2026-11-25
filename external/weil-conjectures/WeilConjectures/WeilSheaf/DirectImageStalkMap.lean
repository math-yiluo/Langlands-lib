/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.UpperStarLowerStar
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.WeightGap

/-!
# Stalks of direct images along an open immersion

This file collects the stalkwise tools used to study the ordinary direct image `j_*` along an
open immersion `j : U ↪ X` and its first higher direct image.

* A morphism of Weil sheaves on a scheme locally of finite type over `k₀` vanishes as soon as it
  vanishes on the geometric stalks at all closed points
  (`AlgebraicGeometry.WeilSheaf.eq_zero_of_forall_stalkAtMap`).
* At a closed point of the open `U`, a morphism of Weil sheaves on `X` whose restriction to `U`
  is an epimorphism is surjective on the geometric stalk
  (`AlgebraicGeometry.WeilSheaf.surjective_stalkAtMap_of_mem_range`): the geometric point lifts to
  `Ū`, and the stalk of `j^* M` there is the stalk of `M`.
* The identification `𝓗⁰(Rφ_* F) ≅ φ_* F` is natural in `F`
  (`AlgebraicGeometry.WeilSheaf.homologySheafZeroDerivedLowerStarIso_hom_naturality`).
* A morphism into a Weil sheaf whose stalk is dual, up to a Tate twist, to a stalk with weights at
  most `-w`, from a sheaf whose stalk has weights at most `w`, vanishes on that stalk
  (`AlgebraicGeometry.WeilSheaf.stalkAtMap_eq_zero_of_dual`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Naturality

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The identification `𝓗⁰(Rφ_* F) ≅ φ_* F` of
`AlgebraicGeometry.WeilSheaf.homologySheafZeroDerivedLowerStarIso` is natural in `F`. -/
@[reassoc]
lemma homologySheafZeroDerivedLowerStarIso_hom_naturality {F G : WeilSheaf k₀ l Y}
    (f : F ⟶ G) :
    (WeilComplex.homologySheaf 0).map ((WeilComplex.derivedLowerStar φ).map (toComplex.map f)) ≫
        (homologySheafZeroDerivedLowerStarIso φ G).hom =
      (homologySheafZeroDerivedLowerStarIso φ F).hom ≫ (lowerStar φ).map f := by
  apply ObjectProperty.hom_ext
  have h₁ := Functor.homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality
    (ProEtaleWeilSheaf.lowerStar k₀ l φ) f.hom 0
  have h₂ := (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedZeroIsoSelf.hom.naturality f.hom
  change (DerivedCategory.homologyFunctor _ ((0 : ℕ) : ℤ)).map
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.map
        ((DerivedCategory.singleFunctor _ 0).map f.hom)) ≫
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).homologyRightDerivedFunctorObjSingleFunctorIso
        G.obj 0 ≪≫ (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedZeroIsoSelf.app G.obj).hom =
    ((ProEtaleWeilSheaf.lowerStar k₀ l φ).homologyRightDerivedFunctorObjSingleFunctorIso
        F.obj 0 ≪≫ (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedZeroIsoSelf.app F.obj).hom ≫
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).map f.hom
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Iso.app_hom, reassoc_of% h₁, h₂,
    Category.assoc]

end Naturality

/-- A morphism of Weil sheaves on a scheme locally of finite type over `k₀` vanishes if it
vanishes on the geometric stalks at all closed points: otherwise its image is a nonzero Weil
sheaf, which has a nonzero geometric stalk at some closed point
(`AlgebraicGeometry.WeilSheaf.exists_nontrivial_stalk_of_not_isZero`). -/
theorem eq_zero_of_forall_stalkAtMap [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {M N : WeilSheaf k₀ l X} (u : M ⟶ N)
    (h : ∀ (x : X.finitePoints) (c : (M.stalk x).carrier), stalkAtMap _ _ _ u c = 0) :
    u = 0 := by
  by_contra hu
  have hI : ¬ IsZero (image u) := fun hI ↦ hu (by
    rw [← image.fac u, hI.eq_of_src (image.ι u) 0, comp_zero])
  obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero (image u) hI
  obtain ⟨y, hy⟩ := exists_ne (0 : ((image u).stalk x).carrier)
  obtain ⟨c, rfl⟩ := surjective_stalkAtMap _ _ _ (factorThruImage u) y
  apply hy
  apply injective_stalkAtMap _ _ _ (image.ι u)
  rw [← stalkAtMap_comp, image.fac, map_zero]
  exact h x c

/-- Let `x` be a closed point of `X` and `A ⟶ R` a morphism of Weil sheaves on `X`. If the stalk
of `A` at `x` has weights at most `w`, and the stalk of `R` at `x` is dual, up to the twist by
the residue cardinality `q_x`, to a Frobenius module `D_x̄` of weights at most `-w` (so that it
has weights at least `w + 2`), then the map vanishes on the stalks at `x`
(`FrobeniusModule.eq_zero_of_hasWeightsAtMost_of_dual`). -/
theorem stalkAtMap_eq_zero_of_dual {A R D : WeilSheaf k₀ l X} (u : A ⟶ R) (x : X.finitePoints)
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (hq : 1 < (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1)
    (hA : (A.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w)
    (hD : (D.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) (-w))
    (hE : ∃ E : (D.stalk x).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (R.stalk x).carrier,
      ∀ a b, E ((D.stalk x).frobenius a) ((R.stalk x).frobenius b) =
        (((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : PadicAlgCl l)) * E a b) :
    (stalkAtMap _ _ _ u : (A.stalk x).carrier →ₗ[PadicAlgCl l] (R.stalk x).carrier) = 0 := by
  obtain ⟨E, hE⟩ := hE
  exact FrobeniusModule.eq_zero_of_hasWeightsAtMost_of_dual _ (stalkAtMap_frobenius _ _ _ u) hq
    hA E hE hD

section OpenImmersion

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X)
  [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The stalk at a geometric point `t ≫ j̄` of `X̄` coming from `Ū` is the stalk of the
restriction to `U`: if `j^* g` is an epimorphism, `g` is an epimorphism on the stalks at
`t ≫ j̄`, the pullback along `t ≫ j̄` being the pullback along `j̄` followed by that along `t`. -/
theorem epi_stalkMap_comp_geometricFiberMap
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    {M N : WeilSheaf k₀ l X} (g : M ⟶ N) [Epi ((upperStar j).map g)]
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Epi (stalkMap (t ≫ Scheme.Hom.geometricFiberMap j (comp_over j _)) g) := by
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  set G := (sheafFunctor k₀ l X).map g
  have h₁ : (t ≫ jb)^*[WeilCoefficients.{u} l].map G =
      (ProEtale.upperStarComp _ t jb).hom.app _ ≫ (t)^*[_].map ((jb)^*[_].map G) ≫
        (ProEtale.upperStarComp _ t jb).inv.app _ := by
    have n := (ProEtale.upperStarComp (WeilCoefficients.{u} l) t jb).hom.naturality G
    rw [Functor.comp_map] at n
    rw [← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have h₂ : Epi (stalkMap t ((upperStar j).map g)) := inferInstance
  change Epi ((Sheaf.Γ _ _).map ((t ≫ jb)^*[WeilCoefficients.{u} l].map G))
  rw [h₁, Functor.map_comp, Functor.map_comp]
  have h₃ : Epi ((Sheaf.Γ _ (WeilCoefficients.{u} l)).map ((t)^*[_].map ((jb)^*[_].map G))) := h₂
  infer_instance

/-- At a closed point `x` of `X` lying in the open `U`, a morphism `g` of Weil sheaves on `X`
whose restriction `j^* g` to `U` is an epimorphism is surjective on the geometric stalks at `x`:
the geometric point over `x` factors through the open `Ū ⊆ X̄`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricFiberMap`), and the stalks there are those of
the restrictions (`AlgebraicGeometry.WeilSheaf.epi_stalkMap_comp_geometricFiberMap`). -/
theorem surjective_stalkAtMap_of_mem_range [IsOpenImmersion j]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    {M N : WeilSheaf k₀ l X} (g : M ⟶ N) [Epi ((upperStar j).map g)] (x : X.finitePoints)
    (hx : x.1 ∈ Set.range j.base) :
    Function.Surjective
      (stalkAtMap _ _ _ g : (M.stalk x).carrier →ₗ[PadicAlgCl l] (N.stalk x).carrier) := by
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  set jb := Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have hP := Scheme.Hom.isPullback_geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
  have hrange : Set.range s.base ⊆ Set.range jb.base := by
    rintro _ ⟨p, rfl⟩
    have : Subsingleton (Spec (CommRingCat.of (AlgebraicClosure k₀))) :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of (AlgebraicClosure k₀))))
    obtain rfl := Subsingleton.elim p (IsLocalRing.closedPoint (AlgebraicClosure k₀))
    obtain ⟨y, hy⟩ := hx
    have hp : (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.base
        (s.base (IsLocalRing.closedPoint (AlgebraicClosure k₀))) = j.base y := by
      rw [hy, ← Scheme.Hom.comp_apply]
      exact Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ y hp
    refine ⟨hP.isoPullback.inv.base z, ?_⟩
    have hc : hP.isoPullback.inv ≫ jb = pullback.fst _ _ := by
      exact (Iso.inv_comp_eq _).2 hP.isoPullback_hom_fst.symm
    rw [← hz, ← Scheme.Hom.comp_apply, hc]
  have ht : IsOpenImmersion.lift jb s hrange ≫ jb = s := IsOpenImmersion.lift_fac _ _ _
  have h := epi_stalkMap_comp_geometricFiberMap j g (IsOpenImmersion.lift jb s hrange)
  rw [ht] at h
  intro y
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (stalkMap s g)).1 h y
  exact ⟨c, (stalkAtMap_apply _ _ _ g c).trans hc⟩

variable [IsOpenImmersion j] [QuasiCompact j] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The restriction to the open `U` of the direct image `j_* g` of an epimorphism `g` of Weil
sheaves on `U` is an epimorphism: `j^* j_* ≅ 𝟭`
(`AlgebraicGeometry.WeilSheaf.lowerStarCompUpperStarIso`). -/
theorem epi_upperStar_map_lowerStar_map {F G : WeilSheaf k₀ l U} (g : F ⟶ G) [Epi g] :
    Epi ((upperStar j).map ((lowerStar j).map g)) := by
  have hc := (lowerStarCompUpperStarIso (k₀ := k₀) (l := l) j).hom.naturality g
  have h₁ : Epi ((lowerStar j ⋙ upperStar j).map g ≫
      (lowerStarCompUpperStarIso (k₀ := k₀) (l := l) j).hom.app G) := by
    rw [hc]
    exact epi_comp _ _
  exact (epi_comp_iff_of_isIso _ _).1 h₁

/-- The higher direct image `Rⁱj_* F` along an open immersion is the cohomology sheaf
`𝓗ⁱ(Rj_* F)` of the derived direct image of `F` placed in degree zero. Stated as an equation to
be used by rewriting: checking it by unification unfolds the cohomology sheaf functor. -/
lemma higherDirectImage_obj_eq [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (i : ℕ) :
    (higherDirectImage j i).obj F = (WeilComplex.homologySheaf (i : ℤ)).obj
      ((WeilComplex.derivedLowerStar j).obj (toComplex.obj F)) := by
  unfold higherDirectImage higherLowerStar
  rw [Functor.comp_obj, Functor.comp_obj]

end OpenImmersion

end AlgebraicGeometry.WeilSheaf
