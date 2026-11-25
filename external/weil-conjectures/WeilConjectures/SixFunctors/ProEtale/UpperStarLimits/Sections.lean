/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.Hull
public import WeilConjectures.SixFunctors.ProEtale.CoproductSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Sections of pullbacks over objects with weakly étale hulls

Let `g : Z ⟶ Y` be a morphism of schemes and `V` an object of the small pro-étale site of `Z`
such that `V ⟶ Z ⟶ Y` has a weakly étale hull `V ⟶ W₀ ⟶ Y`
(`AlgebraicGeometry.Scheme.ProEt.IsHull`). Then `V ⟶ W₀ ×_Y Z` is a terminal object of the
indexing category of the left Kan extension along base change at `V`, so the presheaf pullback
`P = Lan F` of a sheaf `F` on `Y_proét` takes the value `F(W₀)` at `V`
(`AlgebraicGeometry.ProEtale.isIso_hullLanMap`).

If moreover `V` is affine with split affine covers (e.g. the spectrum of a w-contractible ring),
every covering of `V` is refined by a finite decomposition of `V` into disjoint open and closed
pieces, which again have hulls, the hull of `V` being the disjoint union of the hulls of the
pieces. So `P` satisfies the sheaf condition for these coverings, and sheafification does not
change its value at `V`. Hence the sections of `g^* F` over `V` are `F(W₀)`, naturally in `F`
(`AlgebraicGeometry.ProEtale.hullSectionsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

/-- If `a : c ⟶ G.obj d` is initial among the morphisms from `c` to objects in the image of `G`,
the pointwise left Kan extension of `F` along `G.op` takes the value `F(d)` at `c`. -/
lemma isIso_leftKanExtensionUnit_app_comp_map {C D H : Type*} [Category* C] [Category* D]
    [Category* H] (G : D ⥤ C) (F : Dᵒᵖ ⥤ H) [G.op.HasPointwiseLeftKanExtension F] {c : C} {d : D}
    (a : c ⟶ G.obj d) (ha : ∀ (d' : D) (b : c ⟶ G.obj d'), ∃! t : d ⟶ d', a ≫ G.map t = b) :
    IsIso ((G.op.leftKanExtensionUnit F).app (op d) ≫ (G.op.leftKanExtension F).map a.op) := by
  let j₀ : CostructuredArrow G.op (op c) := CostructuredArrow.mk (Y := op d) a.op
  have hj₀ : IsTerminal j₀ := by
    refine IsTerminal.ofUniqueHom
      (fun j ↦ CostructuredArrow.homMk (ha j.left.unop j.hom.unop).exists.choose.op ?_) ?_
    · apply Quiver.Hom.unop_inj
      exact (ha j.left.unop j.hom.unop).exists.choose_spec
    · intro j m
      refine CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj ?_)
      refine (ha j.left.unop j.hom.unop).unique ?_ (ha j.left.unop j.hom.unop).exists.choose_spec
      exact congrArg Quiver.Hom.unop (CostructuredArrow.w m)
  exact (G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F (op c)).isIso_ι_app_of_isTerminal
    j₀ hj₀

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R : Type (u + 1)} [Ring R]

/-- A limit fan of modules is a product on underlying types. -/
lemma bijective_moduleCat_of_isLimit_fan {ι : Type u} {A : ModuleCat.{u + 1} R}
    {B : ι → ModuleCat.{u + 1} R} (f : ∀ i, A ⟶ B i) (h : IsLimit (Fan.mk A f)) :
    Function.Bijective (fun x i ↦ f i x) := by
  have h' := Fan.isLimitMapConeEquiv (forget _) _ _ (isLimitOfPreserves (forget _) h)
  constructor
  · intro x y hxy
    have hh : (↾fun _ : PUnit.{u + 2} ↦ x) = (↾fun _ ↦ y) := by
      refine Fan.IsLimit.hom_ext h' _ _ fun i ↦ ?_
      ext t
      exact congrFun hxy i
    exact ConcreteCategory.congr_hom hh PUnit.unit
  · intro x
    refine ⟨Fan.IsLimit.lift h' (fun i ↦ ↾fun _ : PUnit.{u + 2} ↦ x i) PUnit.unit, ?_⟩
    funext i
    exact ConcreteCategory.congr_hom (Fan.IsLimit.fac h' _ i) PUnit.unit

/-- Let `P` be a presheaf of modules on `X_proét` and `V` an object such that every covering sieve
of `V` contains a covering family `fᵢ : Tᵢ ⟶ V` for which `P(V) ⟶ ∏ P(Tᵢ)` is bijective. Then
the sheafification map `P(V) ⟶ P^#(V)` is bijective. -/
lemma bijective_toSheafify_app_of_forall {X : Scheme.{u}}
    (P : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R) (V : X.ProEt)
    (h : ∀ S ∈ ProEt.topology X V, ∃ (ι : Type u) (T : ι → X.ProEt) (f : ∀ i, T i ⟶ V),
      (∀ i, S (f i)) ∧ Sieve.ofArrows T f ∈ ProEt.topology X V ∧
        Function.Bijective (fun (x : P.obj (op V)) i ↦ P.map (f i).op x)) :
    Function.Bijective ((toSheafify (ProEt.topology X) P).app (op V)) := by
  let J := ProEt.topology X
  refine ⟨fun x y hxy ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨ι, T, f, hS, -, hb⟩ := h _ (Presheaf.equalizerSieve_mem J (toSheafify J P) x y hxy)
    exact hb.1 (funext fun i ↦ hS i)
  · obtain ⟨ι, T, f, hS, hcov, hb⟩ := h _ (Presheaf.imageSieve_mem J (toSheafify J P) t)
    choose x hx using hS
    obtain ⟨s, hs⟩ := hb.2 x
    refine ⟨s, ?_⟩
    let F : Sheaf J (ModuleCat.{u + 1} R) := (presheafToSheaf J _).obj P
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget (ModuleCat.{u + 1} R)) F.property) _ hcov
    rw [← Presieve.isSheafFor_iff_generate] at hsh
    refine hsh.isSeparatedFor.ext fun _ _ ⟨i⟩ ↦ ?_
    change (sheafify J P).map (f i).op ((toSheafify J P).app (op V) s) =
      (sheafify J P).map (f i).op t
    rw [← NatTrans.naturality_apply, ← hx i]
    exact congrArg _ (congrFun hs i)

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) {V : Z.ProEt} {W₀ : Y.ProEt} {ψ : V.left ⟶ W₀.left}
  (hψ : ProEt.IsHull (V.hom ≫ g) W₀ ψ)

/-- The morphism from `V` to the base change `W₀ ×_Y Z` of the hull `W₀` of `V ⟶ Y`. -/
noncomputable def hullHom : V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W₀ :=
  MorphismProperty.Over.homMk (pullback.lift ψ V.hom (by rw [hψ.1])) (pullback.lift_snd _ _ _)
    trivial

lemma hullHom_left : (hullHom g hψ).left = pullback.lift ψ V.hom (by rw [hψ.1]) :=
  rfl

/-- The underlying morphism of `hullHom` followed by the base change of `t : W₀ ⟶ W`. -/
lemma hullHom_comp_map_left {W : Y.ProEt} (t : W₀ ⟶ W) :
    (hullHom g hψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map t).left =
      pullback.lift ψ V.hom (by rw [hψ.1]) ≫
        pullback.lift (pullback.fst W₀.hom g ≫ t.left) (pullback.snd W₀.hom g)
          (by rw [Category.assoc, MorphismProperty.Over.w t, pullback.condition]) :=
  rfl

/-- Morphisms from `V` to base changes `W ×_Y Z` factor uniquely through `hullHom`. -/
lemma existsUnique_hullHom_comp (W : Y.ProEt)
    (b : V ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W) :
    ∃! t : W₀ ⟶ W, hullHom g hψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map t = b := by
  have hb : b.left ≫ pullback.snd W.hom g = V.hom := MorphismProperty.Over.w b
  have hφ : (b.left ≫ pullback.fst W.hom g) ≫ W.hom = V.hom ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb]
  obtain ⟨t, ht, hu⟩ := hψ.2 W _ hφ
  have key (t' : W₀ ⟶ W) :
      hullHom g hψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map t' = b ↔
        ψ ≫ t'.left = b.left ≫ pullback.fst W.hom g := by
    constructor
    · intro h
      rw [← h, hullHom_comp_map_left]
      simp
    · intro h
      refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
      · rw [hullHom_comp_map_left]
        simp [h]
      · rw [hullHom_comp_map_left]
        simp [hb]
  exact ⟨t, (key t).2 ht, fun t' ht' ↦ hu t' ((key t').1 ht')⟩

variable (F : Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} R)

/-- The comparison map `F(W₀) ⟶ (Lan F)(V)` for a hull `W₀` of `V ⟶ Y`. -/
noncomputable def hullLanMap :
    F.obj (op W₀) ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F).obj (op V) :=
  ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lanUnit.app F).app (op W₀) ≫
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F).map (hullHom g hψ).op

/-- **The presheaf pullback at an object with a hull.** The left Kan extension along base change
takes the value `F(W₀)` at `V`, for a hull `W₀` of `V ⟶ Y`. -/
lemma isIso_hullLanMap : IsIso (hullLanMap g hψ F) :=
  Functor.isIso_leftKanExtensionUnit_app_comp_map _ F (hullHom g hψ)
    (existsUnique_hullHom_comp g hψ)

/-- The comparison maps `F(W₀) ⟶ (Lan F)(V)` are compatible with restriction along a morphism
`V' ⟶ V` and the induced morphism of hulls `W₀' ⟶ W₀`. -/
lemma hullLanMap_comp_map {V' : Z.ProEt} (f : V' ⟶ V) {W₀' : Y.ProEt} {ψ' : V'.left ⟶ W₀'.left}
    (hψ' : ProEt.IsHull (V'.hom ≫ g) W₀' ψ') (s : W₀' ⟶ W₀) (hs : ψ' ≫ s.left = f.left ≫ ψ) :
    hullLanMap g hψ F ≫
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan.obj F).map f.op =
      F.map s.op ≫ hullLanMap g hψ' F := by
  have h : hullHom g hψ' ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map s =
      f ≫ hullHom g hψ := by
    refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
    · rw [hullHom_comp_map_left]
      change _ = f.left ≫ pullback.lift ψ V.hom _ ≫ _
      simp [hs]
    · rw [hullHom_comp_map_left]
      change _ = f.left ≫ pullback.lift ψ V.hom _ ≫ _
      simp [MorphismProperty.Over.w f]
  have hn := ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lanUnit.app F).naturality s.op
  rw [hullLanMap, hullLanMap, Category.assoc, ← Functor.map_comp, ← op_comp, ← h, op_comp,
    Functor.map_comp]
  exact ((reassoc_of% hn) _).symm

end AlgebraicGeometry.ProEtale
