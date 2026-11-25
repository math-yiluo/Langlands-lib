/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteEtaleTraceLocal

/-!
# Gluing morphisms of pro-étale sheaves along a cover

Let `g i : W i ⟶ X` be a pro-étale covering family. Morphisms of sheaves on `X_proét` are
determined by their restrictions along the `g i`
(`AlgebraicGeometry.ProEtale.hom_ext_of_localizationRestriction`). This file proves the
corresponding existence statement: a family of morphisms `φ i : j_i^* G ⟶ j_i^* G'` of the
restrictions along the localization functors which agree on overlaps glues to a morphism
`G ⟶ G'`.

The overlap condition is formulated pointwise. A weakly étale `X`-scheme `Z` together with a
factorization `p : Z ⟶ W i` of its structure morphism through `g i` is the image of the weakly
étale `W i`-scheme `p` under the localization functor, up to the canonical isomorphism; through
it, `φ i` induces a map `G(Z) ⟶ G'(Z)` (`AlgebraicGeometry.ProEtale.glueComponent`). The family
is *compatible* if this map does not depend on the choice of `i` and of the factorization `p`.

## Main results

* `AlgebraicGeometry.ProEtale.glue`: the glued morphism, and
  `AlgebraicGeometry.ProEtale.localizationRestriction_map_glue`: its restriction along `g i`
  is `φ i`;
* `AlgebraicGeometry.ProEtale.existsUnique_hom_of_localizationRestriction`: existence and
  uniqueness of the glued morphism;
* `AlgebraicGeometry.ProEtale.glueComponent_localizationRestriction_map`: the restrictions of a
  global morphism form a compatible family.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}}
  (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]

section Lift

variable {Z : X.ProEt} {i : ι} (p : Z.left ⟶ W i) (hp : p ≫ g i = Z.hom)

include hp in
lemma weaklyEtale_of_comp_eq : WeaklyEtale p := by
  have : WeaklyEtale (p ≫ g i) := hp ▸ Z.prop
  exact .of_comp p (g i)

/-- A weakly étale `X`-scheme `Z` with a factorization `p` of its structure morphism through
`g i`, as a weakly étale `W i`-scheme. -/
noncomputable def liftObj : (W i).ProEt :=
  MorphismProperty.Over.mk ⊤ p (weaklyEtale_of_comp_eq g p hp)

/-- The image of `liftObj g p hp` under the localization functor along `g i` is `Z`. -/
noncomputable def liftObjIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj (liftObj g p hp) ≅
      Z :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp [liftObj, hp])

omit [∀ i, WeaklyEtale (g i)] in
include hp in
/-- A factorization of the structure morphism of `Z` through `g i` induces one of every
`Z'` over `Z`. -/
lemma comp_left_comp_eq {Z' : X.ProEt} (f : Z' ⟶ Z) : (f.left ≫ p) ≫ g i = Z'.hom := by
  simp only [Category.assoc, hp]
  exact MorphismProperty.Over.w f

end Lift

variable {G G' : Sheaf (ProEt.topology X) A}
  (φ : ∀ i, (localizationRestriction A (g i) inferInstance).obj G ⟶
    (localizationRestriction A (g i) inferInstance).obj G')

/-- The map `G(Z) ⟶ G'(Z)` induced by `φ i` on a weakly étale `X`-scheme `Z` whose structure
morphism factors as `p ≫ g i`: the component of `φ i` at `p`, transported along the canonical
isomorphism of `Z` with the image of `p` under the localization functor. -/
noncomputable def glueComponent (Z : X.ProEt) (i : ι) (p : Z.left ⟶ W i)
    (hp : p ≫ g i = Z.hom) : G.obj.obj (op Z) ⟶ G'.obj.obj (op Z) :=
  G.obj.map (liftObjIso g p hp).hom.op ≫ (φ i).hom.app (op (liftObj g p hp)) ≫
    G'.obj.map (liftObjIso g p hp).inv.op

/-- On the image of a weakly étale `W i`-scheme `b`, with its tautological factorization,
`glueComponent` is the component of `φ i` at `b`. -/
lemma glueComponent_map_obj {i : ι} (b : (W i).ProEt) :
    glueComponent g φ ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj b)
      i b.hom rfl = (φ i).hom.app (op b) := by
  let Z := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj b
  have h1 : (liftObjIso (Z := Z) g b.hom rfl).hom = 𝟙 _ := MorphismProperty.Over.Hom.ext (by
    simp [liftObjIso, MorphismProperty.Over.isoMk])
  have h2 : (liftObjIso (Z := Z) g b.hom rfl).inv = 𝟙 _ := MorphismProperty.Over.Hom.ext (by
    simp [liftObjIso, MorphismProperty.Over.isoMk]; try rfl)
  erw [glueComponent, h1, h2, op_id, G.obj.map_id, Category.id_comp, G'.obj.map_id,
    Category.comp_id]
  rfl

/-- `glueComponent` is natural in the weakly étale `X`-scheme `Z`, the factorization being
precomposed with the morphism. -/
lemma glueComponent_naturality {Z Z' : X.ProEt} (f : Z' ⟶ Z) (i : ι) (p : Z.left ⟶ W i)
    (hp : p ≫ g i = Z.hom) (hp' : (f.left ≫ p) ≫ g i = Z'.hom) :
    glueComponent g φ Z i p hp ≫ G'.obj.map f.op =
      G.obj.map f.op ≫ glueComponent g φ Z' i (f.left ≫ p) hp' := by
  let m : liftObj g (f.left ≫ p) hp' ⟶ liftObj g p hp :=
    MorphismProperty.Over.homMk f.left (by simp [liftObj])
  let mm := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).map m
  have hm : G.obj.map mm.op ≫ (φ i).hom.app (op (liftObj g (f.left ≫ p) hp')) =
      (φ i).hom.app (op (liftObj g p hp)) ≫ G'.obj.map mm.op :=
    (φ i).hom.naturality m.op
  have e1 : f ≫ (liftObjIso g p hp).inv = (liftObjIso g (f.left ≫ p) hp').inv ≫ mm :=
    MorphismProperty.Over.Hom.ext ((Category.comp_id f.left).trans (Category.id_comp f.left).symm)
  have e2 : (liftObjIso g (f.left ≫ p) hp').hom ≫ f = mm ≫ (liftObjIso g p hp).hom :=
    MorphismProperty.Over.Hom.ext ((Category.comp_id f.left).trans (Category.id_comp f.left).symm)
  have e1' : G'.obj.map (liftObjIso g p hp).inv.op ≫ G'.obj.map f.op =
      G'.obj.map mm.op ≫ G'.obj.map (liftObjIso g (f.left ≫ p) hp').inv.op := by
    rw [← G'.obj.map_comp, ← G'.obj.map_comp, ← op_comp, ← op_comp, e1]
  have e2' : G.obj.map f.op ≫ G.obj.map (liftObjIso g (f.left ≫ p) hp').hom.op =
      G.obj.map (liftObjIso g p hp).hom.op ≫ G.obj.map mm.op := by
    rw [← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp, e2]
  simp only [glueComponent, Category.assoc]
  rw [e1', reassoc_of% e2', reassoc_of% hm]

/-- A family of morphisms `φ i : j_i^* G ⟶ j_i^* G'` is *compatible* if the maps
`G(Z) ⟶ G'(Z)` it induces on weakly étale `X`-schemes `Z` do not depend on the factorization of
the structure morphism of `Z` through one of the `g i`. This is the pointwise form of the
condition that `φ i` and `φ j` agree on `W i ×_X W j`. -/
def GlueCompatible : Prop :=
  ∀ (Z : X.ProEt) (i j : ι) (p : Z.left ⟶ W i) (q : Z.left ⟶ W j) (hp : p ≫ g i = Z.hom)
    (hq : q ≫ g j = Z.hom), glueComponent g φ Z i p hp = glueComponent g φ Z j q hq

lemma baseChange_snd_comp (V : X.ProEt) (i : ι) :
    pullback.snd V.hom (g i) ≫ g i = (ProEt.baseChange (g i) V).hom := by
  simp [ProEt.baseChange, pullback.condition]

section Glue

variable (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X) {g φ} (hφ : GlueCompatible g φ)

include hφ in
/-- The component at `V` of the glued morphism: the amalgamation, over the cover of `V` by the
base changes `V ×_X W i`, of the maps induced by the `φ i`. -/
noncomputable def glueApp (V : X.ProEt) : G.obj.obj (op V) ⟶ G'.obj.obj (op V) :=
  G'.property.amalgamateOfArrows (fun i ↦ ProEt.baseChangeHom (g i) V)
    (ProEt.ofArrows_baseChange_mem_topology V g hg)
    (fun i ↦ G.obj.map (ProEt.baseChangeHom (g i) V).op ≫
      glueComponent g φ _ i (pullback.snd V.hom (g i)) (baseChange_snd_comp g V i))
    (by
      intro T i j a b hab
      rw [Category.assoc, glueComponent_naturality g φ a i _ _
          (comp_left_comp_eq g _ (baseChange_snd_comp g V i) a),
        Category.assoc, glueComponent_naturality g φ b j _ _
          (comp_left_comp_eq g _ (baseChange_snd_comp g V j) b),
        hφ T i j _ (b.left ≫ pullback.snd V.hom (g j)) _
          (comp_left_comp_eq g _ (baseChange_snd_comp g V j) b),
        ← G.obj.map_comp_assoc, ← G.obj.map_comp_assoc, ← op_comp, ← op_comp, hab])

include hφ in
/-- The glued component at `V`, restricted along `k : Z ⟶ V`, is given at `Z` by any
factorization of the structure morphism of `Z` through one of the `g i`. -/
lemma glueApp_comp {Z V : X.ProEt} (k : Z ⟶ V) (i : ι) (p : Z.left ⟶ W i)
    (hp : p ≫ g i = Z.hom) :
    glueApp hg hφ V ≫ G'.obj.map k.op = G.obj.map k.op ≫ glueComponent g φ Z i p hp := by
  refine G'.property.hom_ext_ofArrows (fun j ↦ ProEt.baseChangeHom (g j) Z)
    (ProEt.ofArrows_baseChange_mem_topology Z g hg) fun j ↦ ?_
  let m : ProEt.baseChange (g j) Z ⟶ ProEt.baseChange (g j) V :=
    MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst Z.hom (g j) ≫ k.left) (pullback.snd Z.hom (g j))
        (by rw [Category.assoc, MorphismProperty.Over.w k, pullback.condition]))
      (by simp [ProEt.baseChange, MorphismProperty.Over.w k])
  have hm : m ≫ ProEt.baseChangeHom (g j) V = ProEt.baseChangeHom (g j) Z ≫ k :=
    MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  have hj := comp_left_comp_eq g _ (baseChange_snd_comp g V j) m
  have hi := comp_left_comp_eq g p hp (ProEt.baseChangeHom (g j) Z)
  rw [Category.assoc, ← G'.obj.map_comp, ← op_comp, ← hm, op_comp, G'.obj.map_comp, glueApp,
    Presheaf.IsSheaf.amalgamateOfArrows_map_assoc, Category.assoc,
    glueComponent_naturality g φ m j _ _ hj, ← G.obj.map_comp_assoc, ← op_comp, hm,
    Category.assoc, glueComponent_naturality g φ (ProEt.baseChangeHom (g j) Z) i p hp hi,
    op_comp, G.obj.map_comp_assoc, hφ]

/-- **Gluing of morphisms of pro-étale sheaves**: a compatible family of morphisms
`φ i : j_i^* G ⟶ j_i^* G'` of the restrictions along a pro-étale covering family glues to a
morphism `G ⟶ G'` (`AlgebraicGeometry.ProEtale.localizationRestriction_map_glue`). -/
noncomputable def glue : G ⟶ G' :=
  ObjectProperty.homMk
    { app := fun V ↦ glueApp hg hφ V.unop
      naturality := fun V V' f ↦ by
        refine G'.property.hom_ext_ofArrows (fun j ↦ ProEt.baseChangeHom (g j) V'.unop)
          (ProEt.ofArrows_baseChange_mem_topology V'.unop g hg) fun j ↦ ?_
        have h₁ := glueApp_comp hg hφ (ProEt.baseChangeHom (g j) V'.unop) j _
          (baseChange_snd_comp g V'.unop j)
        have h₂ := glueApp_comp hg hφ (ProEt.baseChangeHom (g j) V'.unop ≫ f.unop) j _
          (baseChange_snd_comp g V'.unop j)
        rw [op_comp, Quiver.Hom.op_unop, G'.obj.map_comp, G.obj.map_comp, Category.assoc] at h₂
        rw [Category.assoc, h₁, Category.assoc, h₂] }

lemma glue_hom_app (V : X.ProEt) : (glue hg hφ).hom.app (op V) = glueApp hg hφ V := rfl

/-- The restriction of the glued morphism along `g i` is `φ i`. -/
lemma localizationRestriction_map_glue (i : ι) :
    (localizationRestriction A (g i) inferInstance).map (glue hg hφ) = φ i := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun b ↦ ?_))
  induction b using Opposite.rec with | op b => ?_
  rw [localizationRestriction_map_hom_app, glue_hom_app]
  have h := glueApp_comp hg hφ
    (𝟙 ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj b)) i b.hom rfl
  rw [op_id, G'.obj.map_id, G.obj.map_id, Category.comp_id, Category.id_comp] at h
  rw [h, glueComponent_map_obj]

include hg hφ in
/-- **Gluing of morphisms of pro-étale sheaves**: a compatible family of morphisms of the
restrictions along a pro-étale covering family is the family of restrictions of a unique
morphism of sheaves. -/
theorem existsUnique_hom_of_localizationRestriction :
    ∃! ψ : G ⟶ G', ∀ i, (localizationRestriction A (g i) inferInstance).map ψ = φ i :=
  ⟨glue hg hφ, localizationRestriction_map_glue hg hφ, fun _ hψ ↦
    hom_ext_of_localizationRestriction A g hg fun i ↦
      (hψ i).trans (localizationRestriction_map_glue hg hφ i).symm⟩

end Glue

/-- Conversely, the restrictions of a morphism of sheaves form a compatible family: the induced
map at `Z` is the component of the morphism at `Z`. -/
lemma glueComponent_localizationRestriction_map (ψ : G ⟶ G') (Z : X.ProEt) (i : ι)
    (p : Z.left ⟶ W i) (hp : p ≫ g i = Z.hom) :
    glueComponent g (fun i ↦ (localizationRestriction A (g i) inferInstance).map ψ) Z i p hp =
      ψ.hom.app (op Z) := by
  erw [glueComponent, localizationRestriction_map_hom_app, ψ.hom.naturality_assoc,
    ← G'.obj.map_comp, ← op_comp, Iso.inv_hom_id, op_id, G'.obj.map_id, Category.comp_id]

lemma glueCompatible_localizationRestriction_map (ψ : G ⟶ G') :
    GlueCompatible g (fun i ↦ (localizationRestriction A (g i) inferInstance).map ψ) :=
  fun Z i j p q hp hq ↦ by
    rw [glueComponent_localizationRestriction_map, glueComponent_localizationRestriction_map]

end AlgebraicGeometry.ProEtale
