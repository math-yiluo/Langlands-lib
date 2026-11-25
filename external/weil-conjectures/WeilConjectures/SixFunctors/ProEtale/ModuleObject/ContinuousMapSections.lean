/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison

/-!
# Global sections of the sheaf of continuous maps

Let `T` be a topological ring and `X` a scheme. The global sections `𝟙 ⟶ C(-, T)_X` of the ring
object underlying the sheaf of rings `U ↦ C(U, T)` on `X_proét` are the continuous maps `X → T`
(`AlgebraicGeometry.ProEtale.continuousMapSectionRingHom_bijective`): `X` is the terminal object
of `X_proét`. Along a morphism `g : X' ⟶ X`, the global section of a continuous map `f : X → T`
pulls back to the global section of `f ∘ g`
(`AlgebraicGeometry.ProEtale.Γ_map_continuousMapPullbackHom_mapFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- For a monoidal adjunction `F ⊣ G`, a global section `s : 𝟙 ⟶ X` and `b : X ⟶ G Y`: if
`s ≫ b` is the image `ε ≫ G k` of a global section `k : 𝟙 ⟶ Y`, then `ε ≫ F s` followed by the
adjoint `F X ⟶ Y` of `b` is `k`. -/
lemma ε_comp_map_comp_homEquiv_symm_eq {X : C} {Y : D} (s : 𝟙_ C ⟶ X) (b : X ⟶ G.obj Y)
    (k : 𝟙_ D ⟶ Y) (h : s ≫ b = ε G ≫ G.map k) :
    ε F ≫ F.map s ≫ (adj.homEquiv _ _).symm b = k := by
  have e : (adj.homEquiv _ _).symm (ε G) = Functor.OplaxMonoidal.η F := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, adj.unit_app_unit_comp_map_η]
  rw [← Adjunction.homEquiv_naturality_left_symm, h, Adjunction.homEquiv_naturality_right_symm, e,
    Functor.Monoidal.ε_η_assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The restriction `C(X, T) →+* C(V, T)` along the structure morphism of `V` in `X_proét`. -/
noncomputable def continuousMapRestrictRingHom (V : X.ProEtᵒᵖ) :
    C(X, T) →+* (continuousMapRingSheaf.{0} X T).obj.obj V :=
  ULift.ringEquiv.symm.toRingHom.comp
    (ContinuousMap.compRightAlgHom ℤ T V.unop.hom.base.hom).toRingHom

lemma continuousMapRestrictRingHom_apply (V : X.ProEtᵒᵖ) (f : C(X, T)) :
    continuousMapRestrictRingHom X T V f = ULift.up (f.comp V.unop.hom.base.hom) :=
  rfl

lemma continuousMapRestrictRingHom_naturality {V V' : X.ProEtᵒᵖ} (k : V ⟶ V') (f : C(X, T)) :
    (continuousMapRingSheaf.{0} X T).obj.map k (continuousMapRestrictRingHom X T V f) =
      continuousMapRestrictRingHom X T V' f := by
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change f (V.unop.hom.base (k.unop.left.base x)) = f (V'.unop.hom.base x)
  have h := congrArg (fun φ : _ ⟶ X ↦ φ.base x) (MorphismProperty.Over.w k.unop)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  exact congrArg f h

/-- The global section of `C(-, T)_X` given by a continuous map `X → T`. -/
noncomputable def continuousMapSectionRingHom :
    C(X, T) →+* Γ ((sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf.{0} X T)) :=
  Sheaf.ringHomΓSheafCompose (ProEt.topology X) (continuousMapRingSheaf.{0} X T)
    (continuousMapRestrictRingHom X T) (continuousMapRestrictRingHom_naturality X T)

lemma unitHomEval_continuousMapSectionRingHom (f : C(X, T)) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        (continuousMapSectionRingHom X T f).hom =
      continuousMapRestrictRingHom X T (op (ProEt.mk (𝟙 X))) f :=
  Sheaf.unitHomEval_ringHomΓSheafCompose (J := ProEt.topology X) (ProEt.mk (𝟙 X))
    (continuousMapRingSheaf.{0} X T) (continuousMapRestrictRingHom X T)
    (continuousMapRestrictRingHom_naturality X T) f

/-- **The global sections of `C(-, T)_X` are the continuous maps `X → T`.** -/
lemma continuousMapSectionRingHom_bijective :
    Function.Bijective (continuousMapSectionRingHom X T) := by
  refine Sheaf.ringHomΓSheafCompose_bijective (J := ProEt.topology X)
    (continuousMapRingSheaf.{0} X T) (ProEt.isTerminalMkId X) _ _ ?_
  refine ⟨fun f f' h ↦ ContinuousMap.ext fun x ↦ ?_, fun f ↦ ⟨f.down, ?_⟩⟩
  · exact congrArg (fun a : ULift.{u + 1} C(X, T) ↦ a.down x) h
  · exact ULift.ext (ContinuousMap.ext fun x ↦ rfl)

variable {X} {X' : Scheme.{u}} (g : X' ⟶ X)

/-- The comparison `g^* C(-, T)_X ⟶ C(-, T)_{X'}` is a morphism of ring objects. -/
instance isMonHom_continuousMapPullbackHom : IsMonHom (continuousMapPullbackHom g T) := by
  have : Functor.IsContinuous (C := X.ProEt) (D := X'.ProEt)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X)
      (ProEt.topology X') :=
    ProEt.isContinuous_overPullback _
  have h₁ := Sheaf.monObjObj_sheafPushforwardContinuous_eq (J := ProEt.topology X)
    (K := ProEt.topology X') (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g)
    (continuousMapRingSheaf.{0} X' T)
  have : IsMonHom (continuousMapToPushforward g T) :=
    IsMonHom.of_eq _ rfl h₁.symm (hf := Sheaf.isMonHom_sheafCompose_map
      (J := ProEt.topology X) (continuousMapRingSheafToPushforward g T))
  exact (upperStarLowerStarAdjunction Ab.{u + 1} g).isMonHom_homEquiv_symm _

omit [TopologicalSpace T] [Ring T] [IsTopologicalRing T] in
/-- The value at the unit section of the image `ε ≫ g_* k` of a global section `k` under the
pushforward is the restriction of the value of `k` to `X ×_X X'`. -/
lemma unitHomEval_ε_comp_lowerStar_map {G : Sheaf (ProEt.topology X') Ab.{u + 1}}
    (k : 𝟙_ (Sheaf (ProEt.topology X') Ab.{u + 1}) ⟶ G) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        (ε (g)_*[Ab.{u + 1}] ≫ (g)_*[Ab.{u + 1}].map k) =
      G.obj.map ((ProEt.isTerminalMkId X').from _).op
        (Sheaf.unitHomEval (J := ProEt.topology X') (ProEt.mk (𝟙 X')) k) := by
  have : Functor.IsContinuous (C := X.ProEt) (D := X'.ProEt)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X) (ProEt.topology X') :=
    ProEt.isContinuous_overPullback _
  exact Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map _ (ProEt.isTerminalMkId X') k

/-- **Pullback of the global section of a continuous map**: along `g : X' ⟶ X`, the global
section of `C(-, T)_X` given by `f : X → T` pulls back to the global section of `f ∘ g`. -/
lemma Γ_map_continuousMapPullbackHom_mapFunctor (f : C(X, T)) :
    Γ.map (continuousMapPullbackHom g T)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (continuousMapSectionRingHom X T f)) =
      continuousMapSectionRingHom X' T (f.comp g.base.hom) := by
  refine Γ.ext ?_
  rw [Γ.map_hom, Γ.mapFunctor_hom, Category.assoc]
  refine (upperStarLowerStarAdjunction Ab.{u + 1} g).ε_comp_map_comp_homEquiv_symm_eq _ _ _ ?_
  refine Sheaf.unitHomEval_injective (J := ProEt.topology X) (ProEt.isTerminalMkId X) _ ?_
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans ?_
  refine Eq.trans ?_ (unitHomEval_ε_comp_lowerStar_map g
    (continuousMapSectionRingHom X' T (f.comp g.base.hom)).hom).symm
  rw [unitHomEval_continuousMapSectionRingHom, unitHomEval_continuousMapSectionRingHom]
  erw [continuousMapRestrictRingHom_naturality]
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change f ((𝟙 X : X ⟶ X).base ((pullback.fst (𝟙 X) g).base x)) =
    f (g.base ((pullback.snd (𝟙 X) g).base x))
  have h := congrArg (fun k ↦ k.base x) (pullback.condition (f := 𝟙 X) (g := g))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  exact congrArg f h

end AlgebraicGeometry.ProEtale
