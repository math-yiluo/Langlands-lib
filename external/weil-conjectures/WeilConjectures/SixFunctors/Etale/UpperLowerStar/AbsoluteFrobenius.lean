/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The absolute Frobenius acts as the identity on the étale topos

Let `X` be a scheme of characteristic `p` and `F_X` its absolute `p ^ n`-power Frobenius
(`AlgebraicGeometry.Scheme.iterateFrobenius`). For an étale `u : U ⟶ X`, the relative Frobenius
`U ⟶ U ×_{X, F_X} X` is an isomorphism (Stacks 03SN): it is étale, being a morphism between
étale `X`-schemes, and a universal homeomorphism, since its composite with the projection to
`U` is the absolute Frobenius `F_U` and this projection is a base change of `F_X`. Hence base
change along `F_X` on the small étale site of `X` is isomorphic to base change along `𝟙 X`, and
the pushforward and the pullback along `F_X` on étale sheaves are isomorphic to those along
`𝟙 X`, compatibly with pullback along morphisms of schemes of characteristic `p`.
The relative Frobenius `AlgebraicGeometry.Scheme.relativeIterateFrobenius` and the facts that
it is a universal homeomorphism and, for a weakly étale `u`, an isomorphism
(`AlgebraicGeometry.Scheme.isIso_relativeIterateFrobenius`) are in
`WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius`.

## Main definitions

- `AlgebraicGeometry.Etale.overPullbackIterateFrobeniusIso`: base change along `𝟙 X` and along
  `F_X` on the small étale site of `X` are isomorphic.
- `AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso`: `(F_X)_* ≅ (𝟙 X)_*`.
- `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso`: `(F_X)^* ≅ (𝟙 X)^*`.

## Main results

- `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_naturality`: the isomorphisms
  `(F_X)^* ≅ (𝟙 X)^*` are compatible with pullback along morphisms `f : Y ⟶ X`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {p : ℕ} (hp : p.Prime)

/-- `Spec` of the `p ^ n`-power endomorphism of a ring in which `p` vanishes is universally
injective: the `p ^ n`-power map of a field of characteristic `p` is injective. -/
lemma universallyInjective_specMap_iterateFrobeniusOfPrime {R : CommRingCat.{u}}
    (hR : (p : R) = 0) (n : ℕ) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n))) := by
  have h := (tfae_universallyInjective
    (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n)))).out 1 2
  rw [h]
  intro K _ g₁ g₂ hg
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
  simp only [← Spec.map_comp] at hg
  have hg' := congr(($(Spec.map_injective hg)).hom)
  congr 1
  ext r
  have hK : (p : K) = 0 := by rw [← map_natCast (Spec.preimage g₁).hom, hR, map_zero]
  apply (iterateFrobeniusOfPrime K hp hK n).injective
  simpa using congr($hg' r)

/-- `Spec` of the `p ^ n`-power endomorphism of a ring in which `p` vanishes is a universal
homeomorphism. -/
lemma isUniversalHomeomorphism_specMap_iterateFrobeniusOfPrime {R : CommRingCat.{u}}
    (hR : (p : R) = 0) (n : ℕ) :
    IsUniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n))) := by
  have hq : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n))) :=
    isIntegralHom_specMap_of_pow hq fun _ ↦ rfl
  have : Surjective (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n))) :=
    ⟨fun x ↦ ⟨x, specMap_base_apply_of_pow hq (fun _ ↦ rfl) x⟩⟩
  have := universallyInjective_specMap_iterateFrobeniusOfPrime hp hR n
  constructor

/-- Over an open immersion `t : U ⟶ X`, the absolute Frobenius of `X` is the absolute
Frobenius of `U`: the square `F_U ≫ t = t ≫ F_X` is Cartesian, since `F_X` is the identity on
the underlying space. -/
lemma isPullback_iterateFrobenius {X U : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (t : U ⟶ X) [IsOpenImmersion t] :
    IsPullback (U.iterateFrobenius hp (IsOfCharacteristic.of_hom hX t) n) t t
      (X.iterateFrobenius hp hX n) := by
  have hw : U.iterateFrobenius hp (IsOfCharacteristic.of_hom hX t) n ≫ t =
      t ≫ X.iterateFrobenius hp hX n :=
    (comp_iterateFrobenius hp t hX (IsOfCharacteristic.of_hom hX t) n).symm
  have hr (s : PullbackCone t (X.iterateFrobenius hp hX n)) : Set.range s.snd ⊆ Set.range t := by
    rintro _ ⟨w, rfl⟩
    refine ⟨s.fst w, ?_⟩
    rw [← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply, iterateFrobenius_apply]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ IsOpenImmersion.lift t s.snd (hr s))
    (fun s ↦ ?_) (fun s ↦ IsOpenImmersion.lift_fac _ _ _) (fun s m _ h₂ ↦ ?_)⟩⟩
  · rw [← cancel_mono t, Category.assoc, hw, ← Category.assoc, IsOpenImmersion.lift_fac,
      s.condition]
  · rw [← cancel_mono t, h₂, IsOpenImmersion.lift_fac]

end Scheme

namespace Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {p : ℕ} (hp : p.Prime) {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- Base change along the identity and along the absolute Frobenius `F_X` on the small étale
site of a scheme `X` of characteristic `p` are isomorphic: the component at an étale
`U ⟶ X` is `U ×_{X, 𝟙} X ≅ U ≅ U ×_{X, F_X} X`, the second isomorphism being the relative
Frobenius `AlgebraicGeometry.Scheme.relativeIterateFrobenius`. -/
noncomputable def overPullbackIterateFrobeniusIso :
    MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X) ≅
      MorphismProperty.Over.pullback @Etale ⊤ (X.iterateFrobenius hp hX n) :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk
      (asIso (pullback.fst U.hom (𝟙 X)) ≪≫ asIso (relativeIterateFrobenius hp hX n U.hom))
      (by simp [pullback.condition]))
    (fun {U V} φ ↦ by
      ext : 1
      apply pullback.hom_ext
      · simp [comp_iterateFrobenius hp φ.left (IsOfCharacteristic.of_hom hX V.hom)
          (IsOfCharacteristic.of_hom hX U.hom) n]
      · simp)

@[reassoc (attr := simp)]
lemma overPullbackIterateFrobeniusIso_hom_app_left_fst (U : MorphismProperty.Over @Etale ⊤ X) :
    ((overPullbackIterateFrobeniusIso hp hX n).hom.app U).left ≫
        pullback.fst U.hom (X.iterateFrobenius hp hX n) =
      pullback.fst U.hom (𝟙 X) ≫
        U.left.iterateFrobenius hp (IsOfCharacteristic.of_hom hX U.hom) n := by
  simp [overPullbackIterateFrobeniusIso]

@[reassoc (attr := simp)]
lemma overPullbackIterateFrobeniusIso_hom_app_left_snd (U : MorphismProperty.Over @Etale ⊤ X) :
    ((overPullbackIterateFrobeniusIso hp hX n).hom.app U).left ≫
        pullback.snd U.hom (X.iterateFrobenius hp hX n) = pullback.snd U.hom (𝟙 X) := by
  simp [overPullbackIterateFrobeniusIso, pullback.condition]

/-- The pushforward along the absolute Frobenius `F_X` of a scheme `X` of characteristic `p`
is isomorphic to the pushforward along the identity: it is the pushforward along the base
change functor along `F_X`, which is isomorphic to base change along `𝟙 X`
(`AlgebraicGeometry.Etale.overPullbackIterateFrobeniusIso`). -/
noncomputable def lowerStarIterateFrobeniusIso :
    (X.iterateFrobenius hp hX n)_*[A] ≅ (𝟙 X)_*[A] :=
  Functor.sheafPushforwardContinuousIso (overPullbackIterateFrobeniusIso hp hX n).symm A
    (X.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso` are the
restriction maps along the components of
`AlgebraicGeometry.Etale.overPullbackIterateFrobeniusIso`. -/
lemma lowerStarIterateFrobeniusIso_hom_app_hom_app (G : Sheaf X.smallEtaleTopology A)
    (V : X.Etaleᵒᵖ) :
    ((lowerStarIterateFrobeniusIso A hp hX n).hom.app G).hom.app V =
      G.obj.map ((overPullbackIterateFrobeniusIso hp hX n).hom.app V.unop).op :=
  rfl

/-- Étale analogue of blueprint `lemma-scheme-frobenius-geometric-frobenius--1` (stated there for
the small pro-étale site): the absolute Frobenius acts as the identity on
the étale topos. For a scheme `X` of characteristic `p`, the pullback `(F_X)^*` along the
absolute `p ^ n`-power Frobenius is isomorphic to the pullback `(𝟙 X)^*` along the identity. It
is the conjugate of `AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso` under the
adjunctions `g^* ⊣ g_*`. -/
noncomputable def upperStarIterateFrobeniusIso :
    (X.iterateFrobenius hp hX n)^*[A] ≅ (𝟙 X)^*[A] :=
  (conjugateIsoEquiv (upperStarLowerStarAdjunction A (𝟙 X))
    (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))).symm
    (lowerStarIterateFrobeniusIso A hp hX n).symm

/-- `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso` is the conjugate of
`AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso`. -/
lemma conjugateIsoEquiv_upperStarIterateFrobeniusIso :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A (𝟙 X))
        (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))
        (upperStarIterateFrobeniusIso A hp hX n) =
      (lowerStarIterateFrobeniusIso A hp hX n).symm :=
  Equiv.apply_symm_apply _ _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The inverse of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*` of étale
pushforwards is given by the restriction maps along the inverse pullback pasting
isomorphisms. -/
lemma lowerStarComp_inv_app_hom_app' {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂) (G : Sheaf T.smallEtaleTopology A)
    (V : R.Etaleᵒᵖ) :
    ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app G).hom.app V =
      G.obj.map
        ((MorphismProperty.Over.pullbackComp h₁ h₂ h₁₂ hh₁₂).inv.app V.unop).op := by
  simp only [Etale.lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

section Naturality

variable {Y : Scheme.{u}} (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- The base change form of `AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso_naturality`:
for an étale `V ⟶ Y`, the two isomorphisms `V ×_Y X ≅ V ×_{Y, F_X ≫ f} X` built from
`F_X ≫ f = f ≫ F_Y` agree, both being `(v, x) ↦ (F_V v, x)`. -/
lemma overPullbackIterateFrobeniusIso_naturality (V : MorphismProperty.Over @Etale ⊤ Y) :
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f (𝟙 Y) f
        (Category.comp_id f).symm).hom.app V ≫
      (MorphismProperty.Over.pullback @Etale ⊤ f).map
        ((overPullbackIterateFrobeniusIso hp hY n).hom.app V) ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f (Y.iterateFrobenius hp hY n)
        (X.iterateFrobenius hp hX n ≫ f) (comp_iterateFrobenius hp f hY hX n).symm).inv.app V =
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (𝟙 X) f f
        (Category.id_comp f).symm).hom.app V ≫
      (overPullbackIterateFrobeniusIso hp hX n).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (X.iterateFrobenius hp hX n) f
        (X.iterateFrobenius hp hX n ≫ f) rfl).inv.app V := by
  have hfst : (MorphismProperty.Comma.Hom.hom ((overPullbackIterateFrobeniusIso hp hX n).hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))).left ≫
        pullback.fst (pullback.snd V.hom f) (X.iterateFrobenius hp hX n) =
      pullback.fst (pullback.snd V.hom f) (𝟙 X) ≫
        (pullback V.hom f).iterateFrobenius hp
          (IsOfCharacteristic.of_hom hX (pullback.snd V.hom f)) n :=
    overPullbackIterateFrobeniusIso_hom_app_left_fst hp hX n _
  have hsnd : (MorphismProperty.Comma.Hom.hom ((overPullbackIterateFrobeniusIso hp hX n).hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))).left ≫
        pullback.snd (pullback.snd V.hom f) (X.iterateFrobenius hp hX n) =
      pullback.snd (pullback.snd V.hom f) (𝟙 X) :=
    overPullbackIterateFrobeniusIso_hom_app_left_snd hp hX n _
  ext : 1
  apply pullback.hom_ext
  · simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
      MorphismProperty.Comma.comp_hom, Comma.comp_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
      pullback.map_id]
    erw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [overPullbackIterateFrobeniusIso_hom_app_left_fst, reassoc_of% hfst,
      ← comp_iterateFrobenius hp (pullback.fst V.hom f) (IsOfCharacteristic.of_hom hY V.hom)
        (IsOfCharacteristic.of_hom hX (pullback.snd V.hom f)) n]
    erw [pullbackLeftPullbackSndIso_inv_fst_assoc]
    simp
  · simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
      MorphismProperty.Comma.comp_hom, Comma.comp_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd,
      pullback.map_id]
    erw [pullback.lift_snd]
    rw [hsnd]
    erw [pullbackLeftPullbackSndIso_inv_snd_snd]
    simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforward form of `AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso_naturality`:
the two isomorphisms `(F_X ≫ f)_* ≅ f_*` built from `F_Y ≫ f = f ≫ F_X` agree. -/
lemma lowerStarIterateFrobeniusIso_naturality :
    (lowerStarComp A f (Y.iterateFrobenius hp hY n) (X.iterateFrobenius hp hX n ≫ f)
        (comp_iterateFrobenius hp f hY hX n).symm).inv ≫
      Functor.whiskerLeft (f)_*[A] (lowerStarIterateFrobeniusIso A hp hY n).hom ≫
      (lowerStarComp A f (𝟙 Y) f (Category.comp_id f).symm).hom =
    (lowerStarComp A (X.iterateFrobenius hp hX n) f).inv ≫
      Functor.whiskerRight (lowerStarIterateFrobeniusIso A hp hX n).hom (f)_*[A] ≫
      (lowerStarComp A (𝟙 X) f f (Category.id_comp f).symm).hom := by
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_)))
  have hl : ((Functor.whiskerLeft (f)_*[A] (lowerStarIterateFrobeniusIso A hp hY n).hom).app
      G).hom.app V = G.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ f).map
        ((overPullbackIterateFrobeniusIso hp hY n).hom.app V.unop)).op :=
    rfl
  have hr : ((Functor.whiskerRight (lowerStarIterateFrobeniusIso A hp hX n).hom (f)_*[A]).app
      G).hom.app V = G.obj.map ((overPullbackIterateFrobeniusIso hp hX n).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop)).op :=
    rfl
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_inv_app_hom_app', lowerStarComp_hom_app_hom_app, hl, hr,
    ← Functor.map_comp, ← op_comp]
  exact congrArg (fun m ↦ G.obj.map m.op) ((Category.assoc _ _ _).trans
    ((overPullbackIterateFrobeniusIso_naturality hp hX n hY f V.unop).trans
      (Category.assoc _ _ _).symm))

/-- The isomorphisms `(F_X)^* ≅ (𝟙 X)^*` of
`AlgebraicGeometry.Etale.upperStarIterateFrobeniusIso` are compatible with pullback along a
morphism `f : X ⟶ Y` of schemes of characteristic `p`: writing `F_X ≫ f = f ≫ F_Y`, the two
isomorphisms `(F_X ≫ f)^* ≅ f^*`
```
(F_X ≫ f)^* ≅ F_Y^* ⋙ f^* ≅ (𝟙 Y)^* ⋙ f^* ≅ f^*
(F_X ≫ f)^* ≅ f^* ⋙ F_X^* ≅ f^* ⋙ (𝟙 X)^* ≅ f^*
```
agree. Both are conjugate to isomorphisms of pushforwards, which are given by restriction maps
along morphisms into fibre products with the same projections
(`AlgebraicGeometry.Etale.lowerStarIterateFrobeniusIso_naturality`). -/
theorem upperStarIterateFrobeniusIso_naturality :
    upperStarComp A f (Y.iterateFrobenius hp hY n) (X.iterateFrobenius hp hX n ≫ f)
        (comp_iterateFrobenius hp f hY hX n).symm ≪≫
      Functor.isoWhiskerRight (upperStarIterateFrobeniusIso A hp hY n) (f)^*[A] ≪≫
      (upperStarComp A f (𝟙 Y) f (Category.comp_id f).symm).symm =
    upperStarComp A (X.iterateFrobenius hp hX n) f ≪≫
      Functor.isoWhiskerLeft (f)^*[A] (upperStarIterateFrobeniusIso A hp hX n) ≪≫
      (upperStarComp A (𝟙 X) f f (Category.id_comp f).symm).symm := by
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  apply (conjugateEquiv (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n ≫ f))
    (upperStarLowerStarAdjunction A f)).injective
  have h₁ := congrArg Iso.inv (conjugateIsoEquiv_upperStarComp A f (Y.iterateFrobenius hp hY n)
    (X.iterateFrobenius hp hX n ≫ f) (comp_iterateFrobenius hp f hY hX n).symm)
  have h₂ := congrArg Iso.hom
    (conjugateIsoEquiv_upperStarComp A f (𝟙 Y) f (Category.comp_id f).symm)
  have h₃ := congrArg Iso.inv
    (conjugateIsoEquiv_upperStarComp A (X.iterateFrobenius hp hX n) f)
  have h₄ := congrArg Iso.hom
    (conjugateIsoEquiv_upperStarComp A (𝟙 X) f f (Category.id_comp f).symm)
  have hY' := congrArg Iso.inv (conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hY n)
  have hX' := congrArg Iso.inv (conjugateIsoEquiv_upperStarIterateFrobeniusIso A hp hX n)
  simp only [conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv, Iso.symm_inv]
    at h₁ h₂ h₃ h₄ hY' hX'
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv]
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A (Y.iterateFrobenius hp hY n)).comp
      (upperStarLowerStarAdjunction A f)),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A (𝟙 Y)).comp
      (upperStarLowerStarAdjunction A f)),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A f).comp
      (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A f).comp
      (upperStarLowerStarAdjunction A (𝟙 X))),
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, h₁, h₂, h₃, h₄, hY', hX']
  exact lowerStarIterateFrobeniusIso_naturality A hp hX n hY f

end Naturality

end Etale

end AlgebraicGeometry
