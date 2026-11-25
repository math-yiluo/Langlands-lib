/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.HenselianPairSections

/-!
# Sections of étale sheaves on proper schemes over a henselian base

Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper, with closed fibre
`i : Y₀ = Y ×_A A/I ⟶ Y`. For every étale sheaf `F` on `Y`, restriction
`Γ(Y, F) ⟶ Γ(Y₀, F|_{Y₀})` is an isomorphism. Over a strictly henselian local ring `A` the
closed fibre may be replaced by the closed geometric fibre `Z_s = Z ×_A κ̄`, where `κ̄` is an
algebraic closure of the residue field `κ`: as `κ` is separably closed, `κ̄/κ` is purely
inseparable and `Z_s ⟶ Z₀` is a universal homeomorphism.

These degree-zero comparisons compute the stalks of a direct image along a proper morphism,
and are the input of the underived proper base change
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`.

## Main definitions

- `AlgebraicGeometry.Etale.projectiveLineClosedFibreRestriction`: the restriction
  `Γ(ℙ¹_A, F) ⟶ Γ(ℙ¹_κ, F₀)` to the closed fibre of the projective line.

## Main statements

- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`: the comparison
  over a henselian pair.
- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`: the comparison
  with the closed geometric fibre over a strictly henselian local ring.
- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_henselianRing`,
  `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_geometricFibre`: the
  same for abelian sheaves.

## References

- Stacks Project, Lemma 59.91.2, <https://stacks.math.columbia.edu/tag/0A0C>
- Stacks Project, Lemma 59.82.2, <https://stacks.math.columbia.edu/tag/09ZF>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms of étale `X`-schemes into an étale `X`-scheme whose structure morphism is a
monomorphism are unique. -/
lemma _root_.AlgebraicGeometry.Scheme.Etale.hom_ext_of_mono {X : Scheme.{u}} {V W : X.Etale}
    [Mono W.hom] (a b : V ⟶ W) : a = b :=
  MorphismProperty.Over.Hom.ext ((cancel_mono W.hom).1
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The pullback map on global sections of an abelian étale sheaf is an isomorphism if and only
if the pullback of sections `pullSection` between the terminal étale schemes is bijective. -/
lemma isIso_globalSectionsUpperStarMap_iff_bijective_pullSection {X Y : Scheme.{u}}
    (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f G) ↔
      Function.Bijective (pullSection f G (V := Scheme.Etale.mk (𝟙 X))
        (U := Scheme.Etale.mk (𝟙 Y)) f ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  let eY := terminalIsoIsTerminal (Scheme.Etale.isTerminalMkId Y)
  let eX := terminalIsoIsTerminal (Scheme.Etale.isTerminalMkId X)
  let F := (f)^*[AddCommGrpCat.{u + 1}].obj G
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G
  let P : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶ F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
    η.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫ F.obj.map (homToPullback f f
      ((Category.comp_id _).trans (Category.id_comp _).symm)).op
  have : Mono (f.Etale.obj (Scheme.Etale.mk (𝟙 Y))).hom :=
    inferInstanceAs (Mono (pullback.snd (𝟙 Y) f))
  have key : η.hom.app (op (⊤_ Y.Etale)) ≫ F.obj.map (PreservesTerminal.iso f.Etale).inv.op =
      G.obj.map eY.inv.op ≫ P ≫ F.obj.map eX.hom.op := by
    have hn : G.obj.map eY.inv.op ≫ η.hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
        η.hom.app (op (⊤_ Y.Etale)) ≫ F.obj.map (f.Etale.map eY.inv).op :=
      η.hom.naturality eY.inv.op
    simp only [P, ← Category.assoc]
    rw [hn]
    simp only [Category.assoc]
    congr 1
    simp only [← Functor.map_comp, ← op_comp]
    have hm : ∀ a b : ⊤_ X.Etale ⟶ f.Etale.obj (⊤_ Y.Etale), a = b := fun a b ↦
      (cancel_mono (f.Etale.map eY.hom)).1 (Scheme.Etale.hom_ext_of_mono _ _)
    exact congrArg (fun a ↦ F.obj.map (Quiver.Hom.op a)) (hm _ _)
  have hg : globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f G =
      ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G ≫ G.obj.map eY.inv.op) ≫
        P ≫ (F.obj.map eX.hom.op ≫
          (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app F) := by
    rw [globalSectionsUpperStarMap]
    simp only [Category.assoc]
    rw [← reassoc_of% key]
    rfl
  have : IsIso (G.obj.map eY.inv.op) := inferInstance
  have : IsIso (F.obj.map eX.hom.op) := inferInstance
  rw [hg, isIso_comp_left_iff, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of global sections of `t^* G` along `m : T' ⟶ T` is bijective if and only if
the pullback map on global sections of `t^* G` along `m` is an isomorphism. -/
lemma bijective_restrictAlong_iff_isIso_globalSectionsUpperStarMap {R T T' : Scheme.{u}}
    (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (m : T' ⟶ T)
    (t' : T' ⟶ R) (ht' : t' = m ≫ t) :
    Function.Bijective (restrictAlong t G m t' ht' (V := Scheme.Etale.mk (𝟙 T))
      (V' := Scheme.Etale.mk (𝟙 T')) m ((Category.comp_id _).trans (Category.id_comp _).symm)) ↔
      IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} m
        ((t)^*[AddCommGrpCat.{u + 1}].obj G)) := by
  rw [isIso_globalSectionsUpperStarMap_iff_bijective_pullSection]
  have h : Function.Bijective (((upperStarComp AddCommGrpCat.{u + 1} m t t' ht').inv.app
      G).hom.app (op (Scheme.Etale.mk (𝟙 T')))) :=
    ConcreteCategory.bijective_of_isIso (((sheafSections _ _).obj _).map
      ((upperStarComp AddCommGrpCat.{u + 1} m t t' ht').inv.app G))
  have e : ⇑(restrictAlong t G m t' ht' (V := Scheme.Etale.mk (𝟙 T))
      (V' := Scheme.Etale.mk (𝟙 T')) m ((Category.comp_id _).trans (Category.id_comp _).symm)) =
      ⇑(((upperStarComp AddCommGrpCat.{u + 1} m t t' ht').inv.app G).hom.app
        (op (Scheme.Etale.mk (𝟙 T')))) ∘ pullSection m ((t)^*[AddCommGrpCat.{u + 1}].obj G)
          (V := Scheme.Etale.mk (𝟙 T')) (U := Scheme.Etale.mk (𝟙 T)) m
          ((Category.comp_id _).trans (Category.id_comp _).symm) :=
    funext fun s ↦ restrictAlong_apply t G m t' ht' _ _ s
  rw [e, h.of_comp_iff']

/-- The pullback of global sections of abelian sheaves along a universal homeomorphism is an
isomorphism. -/
instance Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f G) := by
  have := isEquivalence_upperStar AddCommGrpCat.{u + 1} f
  unfold globalSectionsUpperStarMap
  infer_instance

/-- **Étale henselian restriction in degree zero**, for abelian sheaves: the version of
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing` for sheaves of
abelian groups. -/
theorem Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_henselianRing {A : Type u}
    [CommRing A] (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    [IsProper p] (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G) :=
  (isIso_globalSectionsUpperStarMap_iff_bijective_pullSection i G).2
    (bijective_pullSection_of_henselianRing I p i p₀ h G)

/-- **Degree-zero comparison over a strictly henselian base**, for abelian sheaves: the version
of `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre` for sheaves of
abelian groups. -/
theorem Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_geometricFibre (A : Type u)
    [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsProper p]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (pullback.fst p
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))))) F) := by
  let κ := IsLocalRing.ResidueField A
  let s₀ : Spec (.of κ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let t : Spec (.of (AlgebraicClosure κ)) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ (AlgebraicClosure κ)))
  have hs : Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure κ))) = t ≫ s₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq A κ,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hs]
  let i₀ := pullback.fst p s₀
  let v := (pullbackLeftPullbackSndIso p s₀ t).inv ≫ pullback.fst (pullback.snd p s₀) t
  have hv : v ≫ i₀ = pullback.fst p (t ≫ s₀) := by
    simp [v, i₀]
  have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i₀ F) :=
    Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_of_henselianRing
      (IsLocalRing.maximalIdeal A) p i₀ (pullback.snd p s₀) (IsPullback.of_hasPullback p s₀) F
  have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (v ≫ i₀) F ≫
      (Sheaf.Γ _ AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1} v i₀).hom.app F)) := by
    rw [globalSectionsUpperStarMap_comp]
    infer_instance
  have := IsIso.of_isIso_comp_right
    (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (v ≫ i₀) F)
    ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).map
      ((upperStarComp AddCommGrpCat.{u + 1} v i₀ (v ≫ i₀) rfl).hom.app F))
  rw [← hv]
  exact this

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The strictly henselian setup for the projective line.** For a local ring `A` with
residue field `κ` — in the application `A` is strictly henselian — let `X = ℙ¹_A`, let
`X₀ = ℙ¹_κ` be its closed fibre, and for an étale sheaf `F` on `X` let `F₀` be its inverse
image on `X₀`. This is the restriction map `res_F : Γ(X, F) ⟶ Γ(X₀, F₀)`.
(blueprint: `proposition-cohomology-p-1-over-henselian--1`) -/
noncomputable def Etale.projectiveLineClosedFibreRestriction (A : Type u) [CommRing A]
    [IsLocalRing A]
    (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj F ⟶
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj ((ProjectiveSpace.map _
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F) :=
  globalSectionsUpperStarMap _ _ F

/-- **Étale henselian restriction in degree zero.** Let `(A, I)` be a henselian pair, let
`p : Y ⟶ Spec A` be proper, and let `i : Y₀ ⟶ Y` be the closed fibre over `Spec (A ⧸ I)`.
For every étale sheaf `F` of `Λ`-modules on `Y`, restriction `Γ(Y, F) ⟶ Γ(Y₀, F|_{Y₀})` is an
isomorphism.

The statement reduces to abelian sheaves
(`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_iff_forget₂`), where it is
`AlgebraicGeometry.Etale.bijective_pullSection_of_henselianRing`: the Zariski gluing near the
closed fibre on the finite covers of `Y`, from the connectedness of the closed fibres
(`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`) and the spectral
shrinking `SpectralSpace.exists_shrink_of_isConnected_inter`, and the passage to étale sheaves
by finite refinement (`AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale`)
and descent (`AlgebraicGeometry.Etale.exists_pullSection_eq_of_isFinite_of_surjective`).
(blueprint: `theorem-comparison-over-henselian-pair-degree--1`) -/
@[stacks 0A0C]
theorem Etale.isIso_globalSectionsUpperStarMap_of_henselianRing {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y Y₀ : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    (i : Y₀ ⟶ Y) (p₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i p₀ p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  rw [isIso_globalSectionsUpperStarMap_iff_forget₂,
    isIso_globalSectionsUpperStarMap_iff_bijective_pullSection]
  exact bijective_pullSection_of_henselianRing I p i p₀ h _

/-- The pullback of global sections along a universal homeomorphism is an isomorphism: the
pullback is then an equivalence of categories of étale sheaves
(`AlgebraicGeometry.Etale.isEquivalence_upperStar`), so the unit of `f^* ⊣ f_*` is an
isomorphism. -/
instance Etale.isIso_globalSectionsUpperStarMap_of_isUniversalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsUniversalHomeomorphism f]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) := by
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) f
  unfold globalSectionsUpperStarMap
  infer_instance

/-- **Degree-zero comparison over a strictly henselian base.** Let `A` be a strictly henselian
local ring with residue field `κ`, let `s : Spec κ̄ ⟶ Spec A` be the closed geometric point
given by an algebraic closure `κ̄` of `κ`, and let `p : Z ⟶ Spec A` be proper. For every étale
sheaf `F` of `Λ`-modules on `Z`, restriction `Γ(Z, F) ⟶ Γ(Z_s, F|_{Z_s})` to the closed
geometric fibre `Z_s = Z ×_A κ̄` is an isomorphism.

As `κ` is separably closed, `κ̄/κ` is purely inseparable, so `Z_s ⟶ Z₀ = Z ×_A κ` is a universal
homeomorphism and induces an isomorphism on sections; the comparison for `Z₀` is
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_henselianRing`.
(blueprint: `lemma-sections-geometric-fibre`) -/
theorem Etale.isIso_globalSectionsUpperStarMap_geometricFibre (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of A)) [IsProper p] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) (pullback.fst p
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))))) F) :=
  (isIso_globalSectionsUpperStarMap_iff_forget₂ Λ _ F).2
    (Etale.isIso_globalSectionsUpperStarMap_addCommGrpCat_geometricFibre A p _)

end AlgebraicGeometry
