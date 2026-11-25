/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsOfIsIso
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!
# The Frobenius of `Spec Ω` and the Galois trivialization

Let `Ω` be a separably closed field in which the prime `p` vanishes, `F_Ω` the `p ^ n`-power
absolute Frobenius of `Spec Ω` and `σ` an endomorphism of `Spec Ω` with `F_Ω ≫ σ = 𝟙`. The
trivialization `κ : F_Ω^* ≅ 𝟭` of the pullback of module objects along the Frobenius
(`ProEtale.CondensedRing.upperStarIterateFrobeniusIso`) and the trivialization `τ : σ^* ≅ 𝟭`
through the pullback from the condensed point (`ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed`)
are inverse to each other:
```
N ≅ 𝟙^* N = (F_Ω ≫ σ)^* N ≅ F_Ω^* σ^* N --F_Ω^* τ--> F_Ω^* N --κ--> N
```
is the identity. Both are the identity on the modules pulled back from the condensed point, which
are all modules on `Spec Ω`.

On a module `p^* A` pulled back from the condensed point, each factor of the composite is a
comparison `p^* ⋙ t^* ≅ p^*` (`ProEtale.CondensedRing.upperStarFromPointModComp`), and these
comparisons are compatible with the composition and identity isomorphisms of the pullbacks. The
latter is checked after passing to adjoints under `f^* ⊣ f_*`, where it reduces to the
compatibility of the comparison of abelian sheaves with composition
(`ProEtale.unitCompUpperStarComp_comp`, `ProEtale.unitCompUpperStarComp_id`).

## Main results

- `ProEtale.CondensedRing.upperStarComp_hom_app_comp_upperStarFromPointModComp` and
  `ProEtale.CondensedRing.upperStarFromPointModComp_id_hom_app`: the comparisons
  `p_Y^* ⋙ f^* ≅ p_X^*` are compatible with composition and identities.
- `ProEtale.CondensedRing.upperStarIterateFrobeniusIso_hom_app_upperStarFromPointMod`: on `p_X^* A`,
  the Frobenius trivialization `F_X^* ≅ 𝟭` is the comparison `p_X^* ⋙ F_X^* ≅ p_X^*`.
- `ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod`: on `p^* A`,
  the trivialization `σ^* ≅ 𝟭` is the comparison `p^* ⋙ σ^* ≅ p^*`.
- `ProEtale.CondensedRing.upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed`.

## Implementation notes

Components of `upperStarFromPointModComp`, `upperStarIterateFrobeniusIso` and
`upperStarIsoIdOfIsSepClosed` are computed by first rewriting with the unfolding equations of
the isomorphisms (`upperStarFromPointModComp_eq`, ...), which hold by `rfl`, and then applying
the abstract lemmas of `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsOfIsIso`:
stating the unfolded components directly makes the kernel unfold the sheaf pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section PointModuleComp

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The comparison `p_Y^* ⋙ f^* ≅ p_X^*` on module objects, unfolded. Rewriting with this
equation of isomorphisms (rather than computing components by unfolding) keeps the kernel from
unfolding the sheaf pullbacks. -/
lemma upperStarFromPointModComp_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStarFromPointModComp Λ f =
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
        (upperStarFromPointComp f).hom Λ) (Mod.extendScalars (condensedPullbackHom Λ f)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (upperStarFromPointMod Λ X)
        (Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ f))
          (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
        (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
      Functor.rightUnitor _ :=
  rfl

/-- The comparison `p_Y^* ⋙ f^* ≅ p_X^*` on module objects, precomposed with the unit
`f^* p_Y^* A ⟶ Λ_X ⊗_{f^* Λ_Y} f^* p_Y^* A` of the extension of scalars, is the comparison
`f^* p_Y^* ≅ p_X^*` of abelian sheaves on underlying sheaves. -/
lemma extendUnitHom_comp_upperStarFromPointModComp_hom_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((f)^*[Ab.{u + 1}].mapMod _).obj ((upperStarFromPointMod Λ Y).obj A)) ≫
      ((upperStarFromPointModComp Λ f).hom.app A).hom =
      (upperStarFromPointComp f).hom.app A.X := by
  rw [upperStarFromPointModComp_eq]
  refine (Mod.extendUnitHom_comp_compIsoOfIsIso_hom_app_hom (condensedPullbackHom Λ f)
    (Functor.mapModCompIso (upperStarFromPoint Y) (f)^*[Ab.{u + 1}]
      (upperStarFromPointComp f).hom Λ) A).trans ?_
  rw [Functor.mapModCompIso_hom_app_hom]

/-- The adjoint `p_Y^* A ⟶ f_* p_X^* A` of the comparison `f^* p_Y^* A ≅ p_X^* A` of module
objects is, on underlying sheaves, the adjoint of the comparison `f^* p_Y^* ≅ p_X^*` of abelian
sheaves. -/
lemma upperStarLowerStarAdjunction_homEquiv_upperStarFromPointModComp_hom_app_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    ((upperStarLowerStarAdjunction Λ f).homEquiv _ _
      ((upperStarFromPointModComp Λ f).hom.app A)).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app
          ((upperStarFromPointMod Λ Y).obj A).X ≫
        (f)_*[Ab.{u + 1}].map ((upperStarFromPointComp f).hom.app A.X) := by
  rw [upperStarLowerStarAdjunction_homEquiv_hom,
    extendUnitHom_comp_upperStarFromPointModComp_hom_app_hom]

omit [IsCommMonObj Λ] in
/-- On underlying sheaves, the inverse of the identity isomorphism of the pushforward of module
objects is that of the pushforward of sheaves. -/
lemma lowerStarId_inv_app_hom (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((lowerStarId Λ X).inv.app M).hom = (ProEtale.lowerStarId Ab.{u + 1} X).inv.app M.X :=
  rfl

/-- **The comparison `p_X^* ⋙ (𝟙 X)^* ≅ p_X^*` is the identity isomorphism** of the pullback
along `𝟙 X`, on modules pulled back from the point. -/
lemma upperStarFromPointModComp_id_hom_app (X : Scheme.{u})
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (upperStarFromPointModComp Λ (𝟙 X)).hom.app A =
      (upperStarId Λ X).hom.app ((upperStarFromPointMod Λ X).obj A) := by
  apply ((upperStarLowerStarAdjunction Λ (𝟙 X)).homEquiv _ _).injective
  have h := homEquiv_comp_conjugateEquiv_app Adjunction.id (upperStarLowerStarAdjunction Λ (𝟙 X))
    (upperStarId Λ X).hom (𝟙 ((upperStarFromPointMod Λ X).obj A))
  erw [Category.comp_id] at h
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarId] at h
  refine Eq.trans ?_ h
  ext1
  rw [upperStarLowerStarAdjunction_homEquiv_upperStarFromPointModComp_hom_app_hom]
  erw [Adjunction.id_homEquiv_apply, Category.id_comp]
  rw [Iso.symm_hom, lowerStarId_inv_app_hom, upperStarFromPointComp_hom_app,
    upperStarCongr_hom_eq_eqToHom]
  exact unitCompUpperStarComp_id Ab.{u + 1} (toSpecZ X) (comp_toSpecZ (𝟙 X))
    (pointUpperStar.obj A.X)

/-- **Pseudo-naturality of the comparison `p_Y^* ⋙ f^* ≅ p_X^*`**: for `f : X ⟶ Y` and
`g : Y ⟶ Z`, the composite `(f ≫ g)^* p_Z^* A ≅ f^* g^* p_Z^* A ≅ f^* p_Y^* A ≅ p_X^* A` is the
comparison for `f ≫ g`. -/
lemma upperStarComp_hom_app_comp_upperStarFromPointModComp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (upperStarComp Λ f g).hom.app ((upperStarFromPointMod Λ Z).obj A) ≫
        (f)^*⟦Λ⟧.map ((upperStarFromPointModComp Λ g).hom.app A) ≫
        (upperStarFromPointModComp Λ f).hom.app A =
      (upperStarFromPointModComp Λ (f ≫ g)).hom.app A := by
  apply ((upperStarLowerStarAdjunction Λ (f ≫ g)).homEquiv _ _).injective
  have h := homEquiv_comp_conjugateEquiv_app
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom
    ((f)^*⟦Λ⟧.map ((upperStarFromPointModComp Λ g).hom.app A) ≫
      (upperStarFromPointModComp Λ f).hom.app A)
  have hc : ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f)).homEquiv
      _ _ ((f)^*⟦Λ⟧.map ((upperStarFromPointModComp Λ g).hom.app A) ≫
        (upperStarFromPointModComp Λ f).hom.app A) =
      (upperStarLowerStarAdjunction Λ g).homEquiv _ _ ((upperStarLowerStarAdjunction Λ f).homEquiv
        _ _ ((f)^*⟦Λ⟧.map ((upperStarFromPointModComp Λ g).hom.app A) ≫
          (upperStarFromPointModComp Λ f).hom.app A)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp, hc] at h
  rw [← h, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  ext1
  simp only [Mod.comp_hom', lowerStar_map_hom, lowerStarComp_hom_app_hom,
    upperStarLowerStarAdjunction_homEquiv_upperStarFromPointModComp_hom_app_hom,
    upperStarFromPointComp_hom_app, upperStarCongr_hom_eq_eqToHom, Category.assoc]
  have h' := unitCompUpperStarComp_comp Ab.{u + 1} f g (toSpecZ X) (toSpecZ Y) (toSpecZ Z)
    (comp_toSpecZ f) (comp_toSpecZ g) (comp_toSpecZ (f ≫ g)) (pointUpperStar.obj A.X)
  simp only [Category.assoc] at h'
  exact h'.symm

/-- The comparisons `p_Y^* ⋙ t^* ≅ p_X^*` along equal morphisms `t = t'` agree up to the
transport `t^* ≅ t'^*`. -/
lemma eqToHom_comp_upperStarFromPointModComp_hom_app {X Y : Scheme.{u}} {t t' : X ⟶ Y}
    (h : t = t') (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj ((upperStarFromPointMod Λ Y).obj A)) h) ≫
        (upperStarFromPointModComp Λ t').hom.app A =
      (upperStarFromPointModComp Λ t).hom.app A := by
  subst h
  exact Category.id_comp _

end PointModuleComp

section Frobenius

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The trivialization `F_X^* ≅ 𝟭` of the pullback of `Λ_X`-modules along the Frobenius,
unfolded. -/
lemma upperStarIterateFrobeniusIso_eq :
    upperStarIterateFrobeniusIso Λ hp hX n =
      Functor.isoWhiskerRight (Functor.mapModIsoComapOfIsoId
          (ProEtale.upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n) _ _
          (ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint hp hX n Λ))
        (Mod.extendScalars (condensedPullbackHom Λ (X.iterateFrobenius hp hX n))) ≪≫
      Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ (X.iterateFrobenius hp hX n)))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (X.iterateFrobenius hp hX n))) ≪≫
      (Mod.comapEquivalenceOfIsIso
        (condensedPullbackHom Λ (X.iterateFrobenius hp hX n))).unitIso.symm :=
  rfl

/-- The trivialization `F_X^* ≅ 𝟭` of the pullback of `Λ_X`-modules, precomposed with the unit
of the extension of scalars, is the trivialization `F_X^* ≅ 𝟭` of abelian sheaves on
underlying sheaves. -/
lemma extendUnitHom_comp_upperStarIterateFrobeniusIso_hom_app_hom
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.extendUnitHom (condensedPullbackHom Λ (X.iterateFrobenius hp hX n))
        (((X.iterateFrobenius hp hX n)^*[Ab.{u + 1}].mapMod _).obj N) ≫
      ((upperStarIterateFrobeniusIso Λ hp hX n).hom.app N).hom =
      (ProEtale.upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n).hom.app N.X := by
  rw [upperStarIterateFrobeniusIso_eq]
  refine (Mod.extendUnitHom_comp_isoIdOfIsIso_hom_app_hom _ (Functor.mapModIsoComapOfIsoId
    (ProEtale.upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n) _ _
    (ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint hp hX n Λ)) N).trans ?_
  rw [Functor.mapModIsoComapOfIsoId_hom_app_hom]

/-- **The Frobenius trivialization on modules pulled back from the point**: on `p_X^* A`, the
trivialization `F_X^* ≅ 𝟭` of the pullback of `Λ_X`-modules is the comparison
`p_X^* ⋙ F_X^* ≅ p_X^*`. -/
lemma upperStarIterateFrobeniusIso_hom_app_upperStarFromPointMod
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (upperStarIterateFrobeniusIso Λ hp hX n).hom.app ((upperStarFromPointMod Λ X).obj A) =
      (upperStarFromPointModComp Λ (X.iterateFrobenius hp hX n)).hom.app A := by
  refine Mod.hom_ext_of_extendUnitHom _ ?_
  rw [extendUnitHom_comp_upperStarIterateFrobeniusIso_hom_app_hom,
    extendUnitHom_comp_upperStarFromPointModComp_hom_app_hom]
  exact ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint hp hX n A.X

end Frobenius

section SepClosed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ Spec (.of Ω))

/-- The trivialization `σ^* ≅ 𝟭` through the pullback from the condensed point, unfolded. -/
lemma upperStarIsoIdOfIsSepClosed_eq :
    upperStarIsoIdOfIsSepClosed Λ σ =
      (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (upperStarFromPointMod Λ (Spec (.of Ω))).asEquivalence.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (upperStarFromPointModComp Λ σ) ≪≫
      (upperStarFromPointMod Λ (Spec (.of Ω))).asEquivalence.counitIso :=
  rfl

/-- On modules `p^* A` pulled back from the condensed point, the trivialization `σ^* ≅ 𝟭` is the
comparison `p^* ⋙ σ^* ≅ p^*`. -/
lemma upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (upperStarIsoIdOfIsSepClosed Λ σ).hom.app ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) =
      (upperStarFromPointModComp Λ σ).hom.app A := by
  rw [upperStarIsoIdOfIsSepClosed_eq]
  exact Functor.isoWhiskerLeft_counitIso_hom_app_functor_obj _ _ A

end SepClosed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {p : ℕ} (hp : p.Prime)
  (hΩ : (p : Γ(Spec (.of Ω), ⊤)) = 0) (n : ℕ) (σ : Spec (.of Ω) ⟶ Spec (.of Ω))
  (hσ : (Spec (.of Ω)).iterateFrobenius hp hΩ n ≫ σ = 𝟙 _)

/-- On modules `p^* A` pulled back from the condensed point, the composite
`p^* A ≅ 𝟙^* p^* A = (F_Ω ≫ σ)^* p^* A ≅ F_Ω^* σ^* p^* A ⟶ F_Ω^* p^* A ⟶ p^* A` is the
identity: each of its factors is a comparison `p^* ⋙ t^* ≅ p^*`, and these are compatible with
composition and identities. -/
lemma upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed_upperStarFromPointMod
    (A : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (upperStarId Λ _).inv.app ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) ≫
        eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A))
          hσ.symm) ≫
        (upperStarComp Λ ((Spec (.of Ω)).iterateFrobenius hp hΩ n) σ).hom.app
          ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) ≫
        ((Spec (.of Ω)).iterateFrobenius hp hΩ n)^*⟦Λ⟧.map
          ((upperStarIsoIdOfIsSepClosed Λ σ).hom.app
            ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A)) ≫
        (upperStarIterateFrobeniusIso Λ hp hΩ n).hom.app
          ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) = 𝟙 _ := by
  rw [upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod,
    upperStarIterateFrobeniusIso_hom_app_upperStarFromPointMod,
    upperStarComp_hom_app_comp_upperStarFromPointModComp,
    eqToHom_comp_upperStarFromPointModComp_hom_app _ hσ.symm, upperStarFromPointModComp_id_hom_app,
    Iso.inv_hom_id_app]

/-- **The Frobenius and Galois trivializations of `Spec Ω` are inverse**: for `F_Ω ≫ σ = 𝟙`, the
composite `N ≅ 𝟙^* N = (F_Ω ≫ σ)^* N ≅ F_Ω^* σ^* N --F_Ω^* τ--> F_Ω^* N --κ--> N` is the
identity. -/
theorem upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))) :
    (upperStarId Λ _).inv.app N ≫ eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) hσ.symm) ≫
        (upperStarComp Λ ((Spec (.of Ω)).iterateFrobenius hp hΩ n) σ).hom.app N ≫
        ((Spec (.of Ω)).iterateFrobenius hp hΩ n)^*⟦Λ⟧.map
          ((upperStarIsoIdOfIsSepClosed Λ σ).hom.app N) ≫
        (upperStarIterateFrobeniusIso Λ hp hΩ n).hom.app N = 𝟙 N := by
  have key := NatTrans.app_eq_id_of_essSurj (upperStarFromPointMod Λ (Spec (.of Ω)))
    ((upperStarId Λ _).inv ≫ (upperStarEqToIso Λ hσ.symm).hom ≫
      (upperStarComp Λ ((Spec (.of Ω)).iterateFrobenius hp hΩ n) σ).hom ≫
      Functor.whiskerRight (upperStarIsoIdOfIsSepClosed Λ σ).hom
        ((Spec (.of Ω)).iterateFrobenius hp hΩ n)^*⟦Λ⟧ ≫
      (Functor.leftUnitor _).hom ≫ (upperStarIterateFrobeniusIso Λ hp hΩ n).hom) (fun A ↦ ?_) N
  · simpa only [NatTrans.comp_app, upperStarEqToIso_hom_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.id_comp] using key
  · simpa only [NatTrans.comp_app, upperStarEqToIso_hom_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.id_comp] using
      upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed_upperStarFromPointMod
        Λ hp hΩ n σ hσ A

/-- `upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed` for a trivialization `τ`
equal to `upperStarIsoIdOfIsSepClosed Λ σ`. -/
theorem upperStarIterateFrobeniusIso_comp_eq_id_of_eq (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _)
    (hτ : τ = upperStarIsoIdOfIsSepClosed Λ σ)
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))) :
    (upperStarId Λ _).inv.app N ≫ eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) hσ.symm) ≫
        (upperStarComp Λ ((Spec (.of Ω)).iterateFrobenius hp hΩ n) σ).hom.app N ≫
        ((Spec (.of Ω)).iterateFrobenius hp hΩ n)^*⟦Λ⟧.map (τ.hom.app N) ≫
        (upperStarIterateFrobeniusIso Λ hp hΩ n).hom.app N = 𝟙 N := by
  subst hτ
  exact upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed Λ hp hΩ n σ hσ N

end AlgebraicGeometry.ProEtale.CondensedRing
